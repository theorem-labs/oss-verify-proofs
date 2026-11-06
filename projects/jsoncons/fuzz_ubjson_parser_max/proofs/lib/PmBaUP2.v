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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_ubaIf LibSegJu_ubaIH LibSegJu_ubaIT LibSegJu_ubaCf LibSegJu_ubaCH LibSegJu_ubaTH LibSegJu_ubaCT LibSegJu_ubaTf.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAUP2.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_ubaIf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaIf.regs0 LibSegJu_ubaIf.regs_out0).
Lemma KS_ubaIf_ok : BG.kept_ok 64 LibSegJu_ubaIf.regs0 LibSegJu_ubaIf.regs_out0 KS_ubaIf = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ubaIf_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#:0#:0v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20,2+v35##20+v24#170#8,1,:X#37?=<#380;4Y,T,:v35T,;#3T,13+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8#Mbv35#3"%pstring.
Lemma ubaIf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaIf] fx R M V ubaIf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaIf] LibSegJu_ubaIf.regs0 LibSegJu_ubaIf.kn0 LibSegJu_ubaIf.BR LibSegJu_ubaIf.PSS LibSegJu_ubaIf.NX0 LibSegJu_ubaIf.F0 229340 LibSegJu_ubaIf.seg_sound_ax fx R M V ubaIf_conc_s. Qed.
Definition KS_ubaIH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaIH.regs0 LibSegJu_ubaIH.regs_out0).
Lemma KS_ubaIH_ok : BG.kept_ok 64 LibSegJu_ubaIH.regs0 LibSegJu_ubaIH.regs_out0 KS_ubaIH = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaIH_conc_s := ",30A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v34p#2#40S,2_v2#90S,8_v2#60S,9+v24#168S,12v34S,13+v24#168S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000La_v2#60v34La_v2#58+v34v23La_v2#50++v34v23#20La_v2#48+v34*#2v23La_v2#40+v24#168La_v2#78#380:8La_v2#80v24La_v2#88v26La_v2#90v25,2+v24#168#18_v2#90#58,1,18X#36308#55454Y,T,1#380;4T,2_v2#70T,8v24T,9v26T,:v22T,;v23T,<v22T,=v22T,12v25T,13++v34v23#20Lb_v2#48+v22v23Lb_v2#60v22Lb+v24#178+v34*#2v23Lb_v2#50v22Lb+v24#170++v34v23#20Lb_v2#58v22Lb+v24#168v34Lb_v2#40+v24#168Lb_v2#78#380:8Lb_v2#80v24Lb_v2#88v26Lb_v2#90v25"%pstring.
Lemma ubaIH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaIH] fx R M V ubaIH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaIH] LibSegJu_ubaIH.regs0 LibSegJu_ubaIH.kn0 LibSegJu_ubaIH.BR LibSegJu_ubaIH.PSS LibSegJu_ubaIH.NX0 LibSegJu_ubaIH.F0 221960 LibSegJu_ubaIH.seg_sound_ax fx R M V ubaIH_conc_s. Qed.
Definition KS_ubaIT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaIT.regs0 LibSegJu_ubaIT.regs_out0).
Lemma KS_ubaIT_ok : BG.kept_ok 64 LibSegJu_ubaIT.regs0 LibSegJu_ubaIT.regs_out0 KS_ubaIT = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaIT_conc_s := ",30A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v35S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#;0238Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La+v24#170v35B#1020v35#7??????00000Hv35#10,3+v24#170#8_v2#80#10+v24#8#1,1,11X#380;4#382>8Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#1T,<v24T,=v26T,>#3484<T,12v2;T,13v2<T,14v2=T,15v2>Nb+v24#8#1Lb+v24#170v35"%pstring.
Lemma ubaIT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaIT] fx R M V ubaIT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaIT] LibSegJu_ubaIT.regs0 LibSegJu_ubaIT.kn0 LibSegJu_ubaIT.BR LibSegJu_ubaIT.PSS LibSegJu_ubaIT.NX0 LibSegJu_ubaIT.F0 229556 LibSegJu_ubaIT.seg_sound_ax fx R M V ubaIT_conc_s. Qed.
Definition KS_ubaCf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCf.regs0 LibSegJu_ubaCf.regs_out0).
Lemma KS_ubaCf_ok : BG.kept_ok 64 LibSegJu_ubaCf.regs0 LibSegJu_ubaCf.regs_out0 KS_ubaCf = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCf_conc_s := ",30A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#:0#:0v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000,2+v35##20+v24#170#8,1,;X#37?;<#38274Y,T,:v35T,;#2T,13v30T,14+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8v30Mbv35#2"%pstring.
Lemma ubaCf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCf] fx R M V ubaCf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCf] LibSegJu_ubaCf.regs0 LibSegJu_ubaCf.kn0 LibSegJu_ubaCf.BR LibSegJu_ubaCf.PSS LibSegJu_ubaCf.NX0 LibSegJu_ubaCf.F0 229308 LibSegJu_ubaCf.seg_sound_ax fx R M V ubaCf_conc_s. Qed.
Definition KS_ubaCH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCH.regs0 LibSegJu_ubaCH.regs_out0).
Lemma KS_ubaCH_ok : BG.kept_ok 64 LibSegJu_ubaCH.regs0 LibSegJu_ubaCH.regs_out0 KS_ubaCH = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCH_conc_s := ",33A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40S,2_v2#90S,8_v2#60S,9+v24#168S,12v34S,13v30S,14+v24#168S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000La_v2#60v34La_v2#58+v34v23La_v2#50++v34v23#20La_v2#48+v34*#2v23La_v2#40+v24#168La_v2#78#381=4La_v2#80v24La_v2#88v26La_v2#90v25B#v30#1000000,2+v24#168#18_v2#90#58,1,18X#36308#55454Y,T,1#38274T,2_v2#70T,8v24T,9v26T,:v22T,;v23T,<v22T,=v22T,12v25T,14++v34v23#20Lb_v2#48+v22v23Lb_v2#60v22Lb+v24#178+v34*#2v23Lb_v2#50v22Lb+v24#170++v34v23#20Lb_v2#58v22Lb+v24#168v34Lb_v2#40+v24#168Lb_v2#78#381=4Lb_v2#80v24Lb_v2#88v26Lb_v2#90v25"%pstring.
Lemma ubaCH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCH] fx R M V ubaCH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCH] LibSegJu_ubaCH.regs0 LibSegJu_ubaCH.kn0 LibSegJu_ubaCH.BR LibSegJu_ubaCH.PSS LibSegJu_ubaCH.NX0 LibSegJu_ubaCH.F0 221960 LibSegJu_ubaCH.seg_sound_ax fx R M V ubaCH_conc_s. Qed.
Definition KS_ubaTH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaTH.regs0 LibSegJu_ubaTH.regs_out0).
Lemma KS_ubaTH_ok : BG.kept_ok 64 LibSegJu_ubaTH.regs0 LibSegJu_ubaTH.regs_out0 KS_ubaTH = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaTH_conc_s := ",33A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40S,2_v2#90S,8_v2#60S,9+v24#168S,12v34S,13v30S,14+v24#168S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000La_v2#60v34La_v2#58+v34v23La_v2#50++v34v23#20La_v2#48+v34*#2v23La_v2#40+v24#168La_v2#78#38268La_v2#80v24La_v2#88v26La_v2#90v25B#v30#1000000,2+v24#168#18_v2#90#58,1,18X#36308#55454Y,T,1#38274T,2_v2#70T,8v24T,9v26T,:v22T,;v23T,<v22T,=v22T,12v25T,14++v34v23#20Lb_v2#48+v22v23Lb_v2#60v22Lb+v24#178+v34*#2v23Lb_v2#50v22Lb+v24#170++v34v23#20Lb_v2#58v22Lb+v24#168v34Lb_v2#40+v24#168Lb_v2#78#38268Lb_v2#80v24Lb_v2#88v26Lb_v2#90v25"%pstring.
Lemma ubaTH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaTH] fx R M V ubaTH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaTH] LibSegJu_ubaTH.regs0 LibSegJu_ubaTH.kn0 LibSegJu_ubaTH.BR LibSegJu_ubaTH.PSS LibSegJu_ubaTH.NX0 LibSegJu_ubaTH.F0 221960 LibSegJu_ubaTH.seg_sound_ax fx R M V ubaTH_conc_s. Qed.
Definition KS_ubaCT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCT.regs0 LibSegJu_ubaCT.regs_out0).
Lemma KS_ubaCT_ok : BG.kept_ok 64 LibSegJu_ubaCT.regs0 LibSegJu_ubaCT.regs_out0 KS_ubaCT = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCT_conc_s := ",33A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v30p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v30S,14v35S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#;0238Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La+v24#170v35B#1020v35#7??????00000Hv35#10B#v30#1000000,3+v24#170#8_v2#80#10+v24#8#1,1,13X#38274#382>8Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#1T,<v24T,=v26T,>v26T,?#3484<T,12v2;T,13v2<T,14v2=T,15v2>Nb+v24#8#1Lb_v2#78#382;0Lb+v24#170v35"%pstring.
Lemma ubaCT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCT] fx R M V ubaCT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCT] LibSegJu_ubaCT.regs0 LibSegJu_ubaCT.kn0 LibSegJu_ubaCT.BR LibSegJu_ubaCT.PSS LibSegJu_ubaCT.NX0 LibSegJu_ubaCT.F0 230004 LibSegJu_ubaCT.seg_sound_ax fx R M V ubaCT_conc_s. Qed.
Definition KS_ubaTf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaTf.regs0 LibSegJu_ubaTf.regs_out0).
Lemma KS_ubaTf_ok : BG.kept_ok 64 LibSegJu_ubaTf.regs0 LibSegJu_ubaTf.regs_out0 KS_ubaTf = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaTf_conc_s := ",34A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#:0#:0v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2+v35##20+v24#170#8,1,<X#37?54#38274Y,T,:v35T,;v32T,<#4T,13v30T,14+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10v32Lb+v35#8v30Mbv35#4"%pstring.
Lemma ubaTf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaTf] fx R M V ubaTf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaTf] LibSegJu_ubaTf.regs0 LibSegJu_ubaTf.kn0 LibSegJu_ubaTf.BR LibSegJu_ubaTf.PSS LibSegJu_ubaTf.NX0 LibSegJu_ubaTf.F0 229204 LibSegJu_ubaTf.seg_sound_ax fx R M V ubaTf_conc_s. Qed.
End PMBAUP2.
