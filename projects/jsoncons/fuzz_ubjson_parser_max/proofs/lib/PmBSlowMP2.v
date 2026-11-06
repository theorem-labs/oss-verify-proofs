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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bsmS0 LibSegJb_bsmS1 LibSegJb_bsmS2 LibSegJb_bsmS3 LibSegJb_bsmS4 LibSegJb_bsmS5 LibSegJb_bsmS6 LibSegJb_bsmS7 LibSegJb_bsmS8 LibSegJb_bsmS9 LibSegJb_bsmS10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSLMP2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bsmS0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS0.regs0 LibSegJb_bsmS0.regs_out0).
Lemma KS_bsmS0_ok : BG.kept_ok 60 LibSegJb_bsmS0.regs0 LibSegJb_bsmS0.regs_out0 KS_bsmS0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bsmS0_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#20La+v21#10+v24#20B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#2T,:#40T,;#2T,<#13<:38T,=v21T,>#T,12_v2#60T,13#1T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS0] fx R M V bsmS0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS0] LibSegJb_bsmS0.regs0 LibSegJb_bsmS0.kn0 LibSegJb_bsmS0.BR LibSegJb_bsmS0.PSS LibSegJb_bsmS0.NX0 LibSegJb_bsmS0.F0 705708 LibSegJb_bsmS0.seg_sound_ax fx R M V bsmS0_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS1.regs0 LibSegJb_bsmS1.regs_out0).
Lemma KS_bsmS1_ok : BG.kept_ok 60 LibSegJb_bsmS1.regs0 LibSegJb_bsmS1.regs_out0 KS_bsmS1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS1_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#40La+v21#10+v24#40B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#4T,:#80T,;#4T,<#13<:38T,=v21T,>#T,12_v2#60T,13#2T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS1] fx R M V bsmS1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS1] LibSegJb_bsmS1.regs0 LibSegJb_bsmS1.kn0 LibSegJb_bsmS1.BR LibSegJb_bsmS1.PSS LibSegJb_bsmS1.NX0 LibSegJb_bsmS1.F0 705708 LibSegJb_bsmS1.seg_sound_ax fx R M V bsmS1_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS2.regs0 LibSegJb_bsmS2.regs_out0).
Lemma KS_bsmS2_ok : BG.kept_ok 60 LibSegJb_bsmS2.regs0 LibSegJb_bsmS2.regs_out0 KS_bsmS2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS2_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#80La+v21#10+v24#80B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#8T,:#100T,;#8T,<#13<:38T,=v21T,>#T,12_v2#60T,13#4T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS2] fx R M V bsmS2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS2] LibSegJb_bsmS2.regs0 LibSegJb_bsmS2.kn0 LibSegJb_bsmS2.BR LibSegJb_bsmS2.PSS LibSegJb_bsmS2.NX0 LibSegJb_bsmS2.F0 705708 LibSegJb_bsmS2.seg_sound_ax fx R M V bsmS2_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS3.regs0 LibSegJb_bsmS3.regs_out0).
Lemma KS_bsmS3_ok : BG.kept_ok 60 LibSegJb_bsmS3.regs0 LibSegJb_bsmS3.regs_out0 KS_bsmS3 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS3_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#100La+v21#10+v24#100B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#10T,:#200T,;#10T,<#13<:38T,=v21T,>#T,12_v2#60T,13#8T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS3] fx R M V bsmS3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS3] LibSegJb_bsmS3.regs0 LibSegJb_bsmS3.kn0 LibSegJb_bsmS3.BR LibSegJb_bsmS3.PSS LibSegJb_bsmS3.NX0 LibSegJb_bsmS3.F0 705708 LibSegJb_bsmS3.seg_sound_ax fx R M V bsmS3_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS4.regs0 LibSegJb_bsmS4.regs_out0).
Lemma KS_bsmS4_ok : BG.kept_ok 60 LibSegJb_bsmS4.regs0 LibSegJb_bsmS4.regs_out0 KS_bsmS4 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS4_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#200La+v21#10+v24#200B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#20T,:#400T,;#20T,<#13<:38T,=v21T,>#T,12_v2#60T,13#10T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS4] fx R M V bsmS4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS4] LibSegJb_bsmS4.regs0 LibSegJb_bsmS4.kn0 LibSegJb_bsmS4.BR LibSegJb_bsmS4.PSS LibSegJb_bsmS4.NX0 LibSegJb_bsmS4.F0 705708 LibSegJb_bsmS4.seg_sound_ax fx R M V bsmS4_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS5.regs0 LibSegJb_bsmS5.regs_out0).
Lemma KS_bsmS5_ok : BG.kept_ok 60 LibSegJb_bsmS5.regs0 LibSegJb_bsmS5.regs_out0 KS_bsmS5 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS5_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#400La+v21#10+v24#400B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#40T,:#800T,;#40T,<#13<:38T,=v21T,>#T,12_v2#60T,13#20T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS5] fx R M V bsmS5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS5] LibSegJb_bsmS5.regs0 LibSegJb_bsmS5.kn0 LibSegJb_bsmS5.BR LibSegJb_bsmS5.PSS LibSegJb_bsmS5.NX0 LibSegJb_bsmS5.F0 705708 LibSegJb_bsmS5.seg_sound_ax fx R M V bsmS5_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS6.regs0 LibSegJb_bsmS6.regs_out0).
Lemma KS_bsmS6_ok : BG.kept_ok 60 LibSegJb_bsmS6.regs0 LibSegJb_bsmS6.regs_out0 KS_bsmS6 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS6_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#800La+v21#10+v24#800B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#80T,:#1000T,;#80T,<#13<:38T,=v21T,>#T,12_v2#60T,13#40T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS6] fx R M V bsmS6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS6] LibSegJb_bsmS6.regs0 LibSegJb_bsmS6.kn0 LibSegJb_bsmS6.BR LibSegJb_bsmS6.PSS LibSegJb_bsmS6.NX0 LibSegJb_bsmS6.F0 705708 LibSegJb_bsmS6.seg_sound_ax fx R M V bsmS6_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS7.regs0 LibSegJb_bsmS7.regs_out0).
Lemma KS_bsmS7_ok : BG.kept_ok 60 LibSegJb_bsmS7.regs0 LibSegJb_bsmS7.regs_out0 KS_bsmS7 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS7_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#1000La+v21#10+v24#1000B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#100T,:#2000T,;#100T,<#13<:38T,=v21T,>#T,12_v2#60T,13#80T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS7] fx R M V bsmS7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS7] LibSegJb_bsmS7.regs0 LibSegJb_bsmS7.kn0 LibSegJb_bsmS7.BR LibSegJb_bsmS7.PSS LibSegJb_bsmS7.NX0 LibSegJb_bsmS7.F0 705708 LibSegJb_bsmS7.seg_sound_ax fx R M V bsmS7_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS8.regs0 LibSegJb_bsmS8.regs_out0).
Lemma KS_bsmS8_ok : BG.kept_ok 60 LibSegJb_bsmS8.regs0 LibSegJb_bsmS8.regs_out0 KS_bsmS8 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS8_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#2000La+v21#10+v24#2000B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#200T,:#4000T,;#200T,<#13<:38T,=v21T,>#T,12_v2#60T,13#100T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS8] fx R M V bsmS8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS8] LibSegJb_bsmS8.regs0 LibSegJb_bsmS8.kn0 LibSegJb_bsmS8.BR LibSegJb_bsmS8.PSS LibSegJb_bsmS8.NX0 LibSegJb_bsmS8.F0 705708 LibSegJb_bsmS8.seg_sound_ax fx R M V bsmS8_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS9.regs0 LibSegJb_bsmS9.regs_out0).
Lemma KS_bsmS9_ok : BG.kept_ok 60 LibSegJb_bsmS9.regs0 LibSegJb_bsmS9.regs_out0 KS_bsmS9 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS9_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#4000La+v21#10+v24#4000B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#400T,:#8000T,;#400T,<#13<:38T,=v21T,>#T,12_v2#60T,13#200T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS9] fx R M V bsmS9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS9] LibSegJb_bsmS9.regs0 LibSegJb_bsmS9.kn0 LibSegJb_bsmS9.BR LibSegJb_bsmS9.PSS LibSegJb_bsmS9.NX0 LibSegJb_bsmS9.F0 705708 LibSegJb_bsmS9.seg_sound_ax fx R M V bsmS9_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bsmS10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bsmS10.regs0 LibSegJb_bsmS10.regs_out0).
Lemma KS_bsmS10_ok : BG.kept_ok 60 LibSegJb_bsmS10.regs0 LibSegJb_bsmS10.regs_out0 KS_bsmS10 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bsmS10_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#8000La+v21#10+v24#8000B#1000v24#7?????????>0Hv24#10,1_v2#;0#;0,1,1?X#:<4:<#12=21<Y,T,1#:<900T,2_v2#:0T,8_v2#48T,9#800T,:#10000T,;#800T,<#13<:38T,=v21T,>#T,12_v2#60T,13#400T,14+/_v2#48#8#7???8000T,15#7???8000Lb_v2#40v21Lb_v2#48#Lb_v2#98#7???8000Lb_v2#90+/+v21#8#8#7???8000Lb_v2#88v22Lb_v2#80v23Lb_v2#78v21Lb_v2#70+v21#8Lb_v2#68#:<56<Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bsmS10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsmS10] fx R M V bsmS10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsmS10] LibSegJb_bsmS10.regs0 LibSegJb_bsmS10.kn0 LibSegJb_bsmS10.BR LibSegJb_bsmS10.PSS LibSegJb_bsmS10.NX0 LibSegJb_bsmS10.F0 705708 LibSegJb_bsmS10.seg_sound_ax fx R M V bsmS10_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMBSLMP2.
