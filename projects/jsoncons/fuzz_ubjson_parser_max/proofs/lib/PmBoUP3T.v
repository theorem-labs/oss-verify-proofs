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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uboTs0 LibSegJu_uboTs1 LibSegJu_uboTs2 LibSegJu_uboTs3 LibSegJu_uboTs4 LibSegJu_uboTs5 LibSegJu_uboTs6 LibSegJu_uboTs7 LibSegJu_uboTs8 LibSegJu_uboTs9 LibSegJu_uboTs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOUP3T.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uboTs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs0.regs0 LibSegJu_uboTs0.regs_out0).
Lemma KS_uboTs0_ok : BG.kept_ok 64 LibSegJu_uboTs0.regs0 LibSegJu_uboTs0.regs_out0 KS_uboTs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uboTs0_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#2T,9#1T,:#40T,;#2T,<#1T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs0] fx R M V uboTs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs0] LibSegJu_uboTs0.regs0 LibSegJu_uboTs0.kn0 LibSegJu_uboTs0.BR LibSegJu_uboTs0.PSS LibSegJu_uboTs0.NX0 LibSegJu_uboTs0.F0 230392 LibSegJu_uboTs0.seg_sound_ax fx R M V uboTs0_conc_s. Qed.
Definition KS_uboTs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs1.regs0 LibSegJu_uboTs1.regs_out0).
Lemma KS_uboTs1_ok : BG.kept_ok 64 LibSegJu_uboTs1.regs0 LibSegJu_uboTs1.regs_out0 KS_uboTs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs1_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#4T,9#2T,:#80T,;#4T,<#2T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs1] fx R M V uboTs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs1] LibSegJu_uboTs1.regs0 LibSegJu_uboTs1.kn0 LibSegJu_uboTs1.BR LibSegJu_uboTs1.PSS LibSegJu_uboTs1.NX0 LibSegJu_uboTs1.F0 230392 LibSegJu_uboTs1.seg_sound_ax fx R M V uboTs1_conc_s. Qed.
Definition KS_uboTs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs2.regs0 LibSegJu_uboTs2.regs_out0).
Lemma KS_uboTs2_ok : BG.kept_ok 64 LibSegJu_uboTs2.regs0 LibSegJu_uboTs2.regs_out0 KS_uboTs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs2_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#8T,9#4T,:#100T,;#8T,<#4T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs2] fx R M V uboTs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs2] LibSegJu_uboTs2.regs0 LibSegJu_uboTs2.kn0 LibSegJu_uboTs2.BR LibSegJu_uboTs2.PSS LibSegJu_uboTs2.NX0 LibSegJu_uboTs2.F0 230392 LibSegJu_uboTs2.seg_sound_ax fx R M V uboTs2_conc_s. Qed.
Definition KS_uboTs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs3.regs0 LibSegJu_uboTs3.regs_out0).
Lemma KS_uboTs3_ok : BG.kept_ok 64 LibSegJu_uboTs3.regs0 LibSegJu_uboTs3.regs_out0 KS_uboTs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs3_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#10T,9#8T,:#200T,;#10T,<#8T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs3] fx R M V uboTs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs3] LibSegJu_uboTs3.regs0 LibSegJu_uboTs3.kn0 LibSegJu_uboTs3.BR LibSegJu_uboTs3.PSS LibSegJu_uboTs3.NX0 LibSegJu_uboTs3.F0 230392 LibSegJu_uboTs3.seg_sound_ax fx R M V uboTs3_conc_s. Qed.
Definition KS_uboTs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs4.regs0 LibSegJu_uboTs4.regs_out0).
Lemma KS_uboTs4_ok : BG.kept_ok 64 LibSegJu_uboTs4.regs0 LibSegJu_uboTs4.regs_out0 KS_uboTs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs4_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#20T,9#10T,:#400T,;#20T,<#10T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs4] fx R M V uboTs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs4] LibSegJu_uboTs4.regs0 LibSegJu_uboTs4.kn0 LibSegJu_uboTs4.BR LibSegJu_uboTs4.PSS LibSegJu_uboTs4.NX0 LibSegJu_uboTs4.F0 230392 LibSegJu_uboTs4.seg_sound_ax fx R M V uboTs4_conc_s. Qed.
Definition KS_uboTs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs5.regs0 LibSegJu_uboTs5.regs_out0).
Lemma KS_uboTs5_ok : BG.kept_ok 64 LibSegJu_uboTs5.regs0 LibSegJu_uboTs5.regs_out0 KS_uboTs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs5_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#40T,9#20T,:#800T,;#40T,<#20T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs5] fx R M V uboTs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs5] LibSegJu_uboTs5.regs0 LibSegJu_uboTs5.kn0 LibSegJu_uboTs5.BR LibSegJu_uboTs5.PSS LibSegJu_uboTs5.NX0 LibSegJu_uboTs5.F0 230392 LibSegJu_uboTs5.seg_sound_ax fx R M V uboTs5_conc_s. Qed.
Definition KS_uboTs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs6.regs0 LibSegJu_uboTs6.regs_out0).
Lemma KS_uboTs6_ok : BG.kept_ok 64 LibSegJu_uboTs6.regs0 LibSegJu_uboTs6.regs_out0 KS_uboTs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs6_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#80T,9#40T,:#1000T,;#80T,<#40T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs6] fx R M V uboTs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs6] LibSegJu_uboTs6.regs0 LibSegJu_uboTs6.kn0 LibSegJu_uboTs6.BR LibSegJu_uboTs6.PSS LibSegJu_uboTs6.NX0 LibSegJu_uboTs6.F0 230392 LibSegJu_uboTs6.seg_sound_ax fx R M V uboTs6_conc_s. Qed.
Definition KS_uboTs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs7.regs0 LibSegJu_uboTs7.regs_out0).
Lemma KS_uboTs7_ok : BG.kept_ok 64 LibSegJu_uboTs7.regs0 LibSegJu_uboTs7.regs_out0 KS_uboTs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs7_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#100T,9#80T,:#2000T,;#100T,<#80T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs7] fx R M V uboTs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs7] LibSegJu_uboTs7.regs0 LibSegJu_uboTs7.kn0 LibSegJu_uboTs7.BR LibSegJu_uboTs7.PSS LibSegJu_uboTs7.NX0 LibSegJu_uboTs7.F0 230392 LibSegJu_uboTs7.seg_sound_ax fx R M V uboTs7_conc_s. Qed.
Definition KS_uboTs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs8.regs0 LibSegJu_uboTs8.regs_out0).
Lemma KS_uboTs8_ok : BG.kept_ok 64 LibSegJu_uboTs8.regs0 LibSegJu_uboTs8.regs_out0 KS_uboTs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs8_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#200T,9#100T,:#4000T,;#200T,<#100T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs8] fx R M V uboTs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs8] LibSegJu_uboTs8.regs0 LibSegJu_uboTs8.kn0 LibSegJu_uboTs8.BR LibSegJu_uboTs8.PSS LibSegJu_uboTs8.NX0 LibSegJu_uboTs8.F0 230392 LibSegJu_uboTs8.seg_sound_ax fx R M V uboTs8_conc_s. Qed.
Definition KS_uboTs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs9.regs0 LibSegJu_uboTs9.regs_out0).
Lemma KS_uboTs9_ok : BG.kept_ok 64 LibSegJu_uboTs9.regs0 LibSegJu_uboTs9.regs_out0 KS_uboTs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs9_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#400T,9#200T,:#8000T,;#400T,<#200T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs9] fx R M V uboTs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs9] LibSegJu_uboTs9.regs0 LibSegJu_uboTs9.kn0 LibSegJu_uboTs9.BR LibSegJu_uboTs9.PSS LibSegJu_uboTs9.NX0 LibSegJu_uboTs9.F0 230392 LibSegJu_uboTs9.seg_sound_ax fx R M V uboTs9_conc_s. Qed.
Definition KS_uboTs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTs10.regs0 LibSegJu_uboTs10.regs_out0).
Lemma KS_uboTs10_ok : BG.kept_ok 64 LibSegJu_uboTs10.regs0 LibSegJu_uboTs10.regs_out0 KS_uboTs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTs10_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2_v2#:0#40_v2#60#28,1,15X#383?8#:?0><Y,T,1#363><T,2_v2#:0T,8#800T,9#400T,:#10000T,;#800T,<#400T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#386><Nb_v2#61v32"%pstring.
Lemma uboTs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTs10] fx R M V uboTs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTs10] LibSegJu_uboTs10.regs0 LibSegJu_uboTs10.kn0 LibSegJu_uboTs10.BR LibSegJu_uboTs10.PSS LibSegJu_uboTs10.NX0 LibSegJu_uboTs10.F0 230392 LibSegJu_uboTs10.seg_sound_ax fx R M V uboTs10_conc_s. Qed.
End PMBOUP3T.
