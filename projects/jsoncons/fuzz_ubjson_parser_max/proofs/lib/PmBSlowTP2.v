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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bstS0 LibSegJb_bstS1 LibSegJb_bstS2 LibSegJb_bstS3 LibSegJb_bstS4 LibSegJb_bstS5 LibSegJb_bstS6 LibSegJb_bstS7 LibSegJb_bstS8 LibSegJb_bstS9 LibSegJb_bstS10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSLTP2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bstS0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS0.regs0 LibSegJb_bstS0.regs_out0).
Lemma KS_bstS0_ok : BG.kept_ok 60 LibSegJb_bstS0.regs0 LibSegJb_bstS0.regs_out0 KS_bstS0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bstS0_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#20La+v21#10+v24#20B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#2T,:#40T,;#2T,<#13<:38T,=v21T,>#T,12_v2#68T,13#1T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS0] fx R M V bstS0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS0] LibSegJb_bstS0.regs0 LibSegJb_bstS0.kn0 LibSegJb_bstS0.BR LibSegJb_bstS0.PSS LibSegJb_bstS0.NX0 LibSegJb_bstS0.F0 735104 LibSegJb_bstS0.seg_sound_ax fx R M V bstS0_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS1.regs0 LibSegJb_bstS1.regs_out0).
Lemma KS_bstS1_ok : BG.kept_ok 60 LibSegJb_bstS1.regs0 LibSegJb_bstS1.regs_out0 KS_bstS1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS1_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#40La+v21#10+v24#40B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#4T,:#80T,;#4T,<#13<:38T,=v21T,>#T,12_v2#68T,13#2T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS1] fx R M V bstS1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS1] LibSegJb_bstS1.regs0 LibSegJb_bstS1.kn0 LibSegJb_bstS1.BR LibSegJb_bstS1.PSS LibSegJb_bstS1.NX0 LibSegJb_bstS1.F0 735104 LibSegJb_bstS1.seg_sound_ax fx R M V bstS1_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS2.regs0 LibSegJb_bstS2.regs_out0).
Lemma KS_bstS2_ok : BG.kept_ok 60 LibSegJb_bstS2.regs0 LibSegJb_bstS2.regs_out0 KS_bstS2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS2_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#80La+v21#10+v24#80B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#8T,:#100T,;#8T,<#13<:38T,=v21T,>#T,12_v2#68T,13#4T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS2] fx R M V bstS2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS2] LibSegJb_bstS2.regs0 LibSegJb_bstS2.kn0 LibSegJb_bstS2.BR LibSegJb_bstS2.PSS LibSegJb_bstS2.NX0 LibSegJb_bstS2.F0 735104 LibSegJb_bstS2.seg_sound_ax fx R M V bstS2_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS3.regs0 LibSegJb_bstS3.regs_out0).
Lemma KS_bstS3_ok : BG.kept_ok 60 LibSegJb_bstS3.regs0 LibSegJb_bstS3.regs_out0 KS_bstS3 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS3_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#100La+v21#10+v24#100B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#10T,:#200T,;#10T,<#13<:38T,=v21T,>#T,12_v2#68T,13#8T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS3] fx R M V bstS3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS3] LibSegJb_bstS3.regs0 LibSegJb_bstS3.kn0 LibSegJb_bstS3.BR LibSegJb_bstS3.PSS LibSegJb_bstS3.NX0 LibSegJb_bstS3.F0 735104 LibSegJb_bstS3.seg_sound_ax fx R M V bstS3_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS4.regs0 LibSegJb_bstS4.regs_out0).
Lemma KS_bstS4_ok : BG.kept_ok 60 LibSegJb_bstS4.regs0 LibSegJb_bstS4.regs_out0 KS_bstS4 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS4_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#200La+v21#10+v24#200B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#20T,:#400T,;#20T,<#13<:38T,=v21T,>#T,12_v2#68T,13#10T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS4] fx R M V bstS4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS4] LibSegJb_bstS4.regs0 LibSegJb_bstS4.kn0 LibSegJb_bstS4.BR LibSegJb_bstS4.PSS LibSegJb_bstS4.NX0 LibSegJb_bstS4.F0 735104 LibSegJb_bstS4.seg_sound_ax fx R M V bstS4_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS5.regs0 LibSegJb_bstS5.regs_out0).
Lemma KS_bstS5_ok : BG.kept_ok 60 LibSegJb_bstS5.regs0 LibSegJb_bstS5.regs_out0 KS_bstS5 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS5_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#400La+v21#10+v24#400B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#40T,:#800T,;#40T,<#13<:38T,=v21T,>#T,12_v2#68T,13#20T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS5] fx R M V bstS5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS5] LibSegJb_bstS5.regs0 LibSegJb_bstS5.kn0 LibSegJb_bstS5.BR LibSegJb_bstS5.PSS LibSegJb_bstS5.NX0 LibSegJb_bstS5.F0 735104 LibSegJb_bstS5.seg_sound_ax fx R M V bstS5_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS6.regs0 LibSegJb_bstS6.regs_out0).
Lemma KS_bstS6_ok : BG.kept_ok 60 LibSegJb_bstS6.regs0 LibSegJb_bstS6.regs_out0 KS_bstS6 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS6_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#800La+v21#10+v24#800B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#80T,:#1000T,;#80T,<#13<:38T,=v21T,>#T,12_v2#68T,13#40T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS6] fx R M V bstS6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS6] LibSegJb_bstS6.regs0 LibSegJb_bstS6.kn0 LibSegJb_bstS6.BR LibSegJb_bstS6.PSS LibSegJb_bstS6.NX0 LibSegJb_bstS6.F0 735104 LibSegJb_bstS6.seg_sound_ax fx R M V bstS6_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS7.regs0 LibSegJb_bstS7.regs_out0).
Lemma KS_bstS7_ok : BG.kept_ok 60 LibSegJb_bstS7.regs0 LibSegJb_bstS7.regs_out0 KS_bstS7 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS7_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#1000La+v21#10+v24#1000B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#100T,:#2000T,;#100T,<#13<:38T,=v21T,>#T,12_v2#68T,13#80T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS7] fx R M V bstS7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS7] LibSegJb_bstS7.regs0 LibSegJb_bstS7.kn0 LibSegJb_bstS7.BR LibSegJb_bstS7.PSS LibSegJb_bstS7.NX0 LibSegJb_bstS7.F0 735104 LibSegJb_bstS7.seg_sound_ax fx R M V bstS7_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS8.regs0 LibSegJb_bstS8.regs_out0).
Lemma KS_bstS8_ok : BG.kept_ok 60 LibSegJb_bstS8.regs0 LibSegJb_bstS8.regs_out0 KS_bstS8 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS8_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#2000La+v21#10+v24#2000B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#200T,:#4000T,;#200T,<#13<:38T,=v21T,>#T,12_v2#68T,13#100T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS8] fx R M V bstS8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS8] LibSegJb_bstS8.regs0 LibSegJb_bstS8.kn0 LibSegJb_bstS8.BR LibSegJb_bstS8.PSS LibSegJb_bstS8.NX0 LibSegJb_bstS8.F0 735104 LibSegJb_bstS8.seg_sound_ax fx R M V bstS8_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS9.regs0 LibSegJb_bstS9.regs_out0).
Lemma KS_bstS9_ok : BG.kept_ok 60 LibSegJb_bstS9.regs0 LibSegJb_bstS9.regs_out0 KS_bstS9 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS9_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#4000La+v21#10+v24#4000B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#400T,:#8000T,;#400T,<#13<:38T,=v21T,>#T,12_v2#68T,13#200T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS9] fx R M V bstS9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS9] LibSegJb_bstS9.regs0 LibSegJb_bstS9.kn0 LibSegJb_bstS9.BR LibSegJb_bstS9.PSS LibSegJb_bstS9.NX0 LibSegJb_bstS9.F0 735104 LibSegJb_bstS9.seg_sound_ax fx R M V bstS9_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstS10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstS10.regs0 LibSegJb_bstS10.regs_out0).
Lemma KS_bstS10_ok : BG.kept_ok 60 LibSegJb_bstS10.regs0 LibSegJb_bstS10.regs_out0 KS_bstS10 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstS10_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24#8000La+v21#10+v24#8000B#1000v24#7?????????>0Hv24#10,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#800T,:#10000T,;#800T,<#13<:38T,=v21T,>#T,12_v2#68T,13#400T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstS10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstS10] fx R M V bstS10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstS10] LibSegJb_bstS10.regs0 LibSegJb_bstS10.kn0 LibSegJb_bstS10.BR LibSegJb_bstS10.PSS LibSegJb_bstS10.NX0 LibSegJb_bstS10.F0 735104 LibSegJb_bstS10.seg_sound_ax fx R M V bstS10_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMBSLTP2.
