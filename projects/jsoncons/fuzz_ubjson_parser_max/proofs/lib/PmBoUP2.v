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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uboIf LibSegJu_uboIH LibSegJu_uboIT LibSegJu_uboCf LibSegJu_uboCH LibSegJu_uboTH LibSegJu_uboCT LibSegJu_uboTf.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOUP2.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uboIf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboIf.regs0 LibSegJu_uboIf.regs_out0).
Lemma KS_uboIf_ok : BG.kept_ok 64 LibSegJu_uboIf.regs0 LibSegJu_uboIf.regs_out0 KS_uboIf = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uboIf_conc_s := ",2;A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#:0#:0v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20,2+v35##20+v24#170#8,1,:X#384:4#38594Y,T,:v35T,;#9T,13+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8#Mbv35#9"%pstring.
Lemma uboIf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboIf] fx R M V uboIf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboIf] LibSegJu_uboIf.regs0 LibSegJu_uboIf.kn0 LibSegJu_uboIf.BR LibSegJu_uboIf.PSS LibSegJu_uboIf.NX0 LibSegJu_uboIf.F0 230564 LibSegJu_uboIf.seg_sound_ax fx R M V uboIf_conc_s. Qed.
Definition KS_uboIH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboIH.regs0 LibSegJu_uboIH.regs_out0).
Lemma KS_uboIH_ok : BG.kept_ok 64 LibSegJu_uboIH.regs0 LibSegJu_uboIH.regs_out0 KS_uboIH = true. Proof. vm_compute. reflexivity. Qed.
Definition uboIH_conc_s := ",30A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v34p#2#40S,2_v2#90S,8_v2#60S,9+v24#168S,12v34S,13+v24#168S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000La_v2#60v34La_v2#58+v34v23La_v2#50++v34v23#20La_v2#48+v34*#2v23La_v2#40+v24#168La_v2#78#38588La_v2#80v24La_v2#88v26La_v2#90v25,2+v24#168#18_v2#90#58,1,18X#36308#55454Y,T,1#38594T,2_v2#70T,8v24T,9v26T,:v22T,;v23T,<v22T,=v22T,12v25T,13++v34v23#20Lb_v2#48+v22v23Lb_v2#60v22Lb+v24#178+v34*#2v23Lb_v2#50v22Lb+v24#170++v34v23#20Lb_v2#58v22Lb+v24#168v34Lb_v2#40+v24#168Lb_v2#78#38588Lb_v2#80v24Lb_v2#88v26Lb_v2#90v25"%pstring.
Lemma uboIH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboIH] fx R M V uboIH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboIH] LibSegJu_uboIH.regs0 LibSegJu_uboIH.kn0 LibSegJu_uboIH.BR LibSegJu_uboIH.PSS LibSegJu_uboIH.NX0 LibSegJu_uboIH.F0 221960 LibSegJu_uboIH.seg_sound_ax fx R M V uboIH_conc_s. Qed.
Definition KS_uboIT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboIT.regs0 LibSegJu_uboIT.regs_out0).
Lemma KS_uboIT_ok : BG.kept_ok 64 LibSegJu_uboIT.regs0 LibSegJu_uboIT.regs_out0 KS_uboIT = true. Proof. vm_compute. reflexivity. Qed.
Definition uboIT_conc_s := ",30A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v35S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#;0238Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La+v24#170v35B#1020v35#7??????00000Hv35#10,3+v24#170#8_v2#80#10+v24#8#1,1,11X#38594#387;0Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#1T,<v24T,=v26T,>#3480<T,12v2;T,13v2<T,14v2=T,15v2>Nb+v24#8#1Lb+v24#170v35"%pstring.
Lemma uboIT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboIT] fx R M V uboIT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboIT] LibSegJu_uboIT.regs0 LibSegJu_uboIT.kn0 LibSegJu_uboIT.BR LibSegJu_uboIT.PSS LibSegJu_uboIT.NX0 LibSegJu_uboIT.F0 230804 LibSegJu_uboIT.seg_sound_ax fx R M V uboIT_conc_s. Qed.
Definition KS_uboCf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCf.regs0 LibSegJu_uboCf.regs_out0).
Lemma KS_uboCf_ok : BG.kept_ok 64 LibSegJu_uboCf.regs0 LibSegJu_uboCf.regs_out0 KS_uboCf = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCf_conc_s := ",30A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#:0#:0v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000,2+v35##20+v24#170#8,1,;X#38484#3873<Y,T,:v35T,;#5T,13v30T,14+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8v30Mbv35#5"%pstring.
Lemma uboCf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCf] fx R M V uboCf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCf] LibSegJu_uboCf.regs0 LibSegJu_uboCf.kn0 LibSegJu_uboCf.BR LibSegJu_uboCf.PSS LibSegJu_uboCf.NX0 LibSegJu_uboCf.F0 230532 LibSegJu_uboCf.seg_sound_ax fx R M V uboCf_conc_s. Qed.
Definition KS_uboCH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCH.regs0 LibSegJu_uboCH.regs_out0).
Lemma KS_uboCH_ok : BG.kept_ok 64 LibSegJu_uboCH.regs0 LibSegJu_uboCH.regs_out0 KS_uboCH = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCH_conc_s := ",33A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40S,2_v2#90S,8_v2#60S,9+v24#168S,12v34S,13v30S,14+v24#168S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000La_v2#60v34La_v2#58+v34v23La_v2#50++v34v23#20La_v2#48+v34*#2v23La_v2#40+v24#168La_v2#78#3869<La_v2#80v24La_v2#88v26La_v2#90v25B#v30#1000000,2+v24#168#18_v2#90#58,1,18X#36308#55454Y,T,1#3873<T,2_v2#70T,8v24T,9v26T,:v22T,;v23T,<v22T,=v22T,12v25T,14++v34v23#20Lb_v2#48+v22v23Lb_v2#60v22Lb+v24#178+v34*#2v23Lb_v2#50v22Lb+v24#170++v34v23#20Lb_v2#58v22Lb+v24#168v34Lb_v2#40+v24#168Lb_v2#78#3869<Lb_v2#80v24Lb_v2#88v26Lb_v2#90v25"%pstring.
Lemma uboCH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCH] fx R M V uboCH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCH] LibSegJu_uboCH.regs0 LibSegJu_uboCH.kn0 LibSegJu_uboCH.BR LibSegJu_uboCH.PSS LibSegJu_uboCH.NX0 LibSegJu_uboCH.F0 221960 LibSegJu_uboCH.seg_sound_ax fx R M V uboCH_conc_s. Qed.
Definition KS_uboTH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTH.regs0 LibSegJu_uboTH.regs_out0).
Lemma KS_uboTH_ok : BG.kept_ok 64 LibSegJu_uboTH.regs0 LibSegJu_uboTH.regs_out0 KS_uboTH = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTH_conc_s := ",33A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40S,2_v2#90S,8_v2#60S,9+v24#168S,12v34S,13v30S,14+v24#168S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000La_v2#60v34La_v2#58+v34v23La_v2#50++v34v23#20La_v2#48+v34*#2v23La_v2#40+v24#168La_v2#78#38730La_v2#80v24La_v2#88v26La_v2#90v25B#v30#1000000,2+v24#168#18_v2#90#58,1,18X#36308#55454Y,T,1#3873<T,2_v2#70T,8v24T,9v26T,:v22T,;v23T,<v22T,=v22T,12v25T,14++v34v23#20Lb_v2#48+v22v23Lb_v2#60v22Lb+v24#178+v34*#2v23Lb_v2#50v22Lb+v24#170++v34v23#20Lb_v2#58v22Lb+v24#168v34Lb_v2#40+v24#168Lb_v2#78#38730Lb_v2#80v24Lb_v2#88v26Lb_v2#90v25"%pstring.
Lemma uboTH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTH] fx R M V uboTH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTH] LibSegJu_uboTH.regs0 LibSegJu_uboTH.kn0 LibSegJu_uboTH.BR LibSegJu_uboTH.PSS LibSegJu_uboTH.NX0 LibSegJu_uboTH.F0 221960 LibSegJu_uboTH.seg_sound_ax fx R M V uboTH_conc_s. Qed.
Definition KS_uboCT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCT.regs0 LibSegJu_uboCT.regs_out0).
Lemma KS_uboCT_ok : BG.kept_ok 64 LibSegJu_uboCT.regs0 LibSegJu_uboCT.regs_out0 KS_uboCT = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCT_conc_s := ",33A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v30p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v30S,14v35S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#;0238Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La+v24#170v35B#1020v35#7??????00000Hv35#10B#v30#1000000,3+v24#170#8_v2#80#10+v24#8#1,1,13X#3873<#387;0Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#1T,<v24T,=v26T,>v26T,?#3480<T,12v2;T,13v2<T,14v2=T,15v2>Nb+v24#8#1Lb_v2#78#38778Lb+v24#170v35"%pstring.
Lemma uboCT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCT] fx R M V uboCT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCT] LibSegJu_uboCT.regs0 LibSegJu_uboCT.kn0 LibSegJu_uboCT.BR LibSegJu_uboCT.PSS LibSegJu_uboCT.NX0 LibSegJu_uboCT.F0 231228 LibSegJu_uboCT.seg_sound_ax fx R M V uboCT_conc_s. Qed.
Definition KS_uboTf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTf.regs0 LibSegJu_uboTf.regs_out0).
Lemma KS_uboTf_ok : BG.kept_ok 64 LibSegJu_uboTf.regs0 LibSegJu_uboTf.regs_out0 KS_uboTf = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTf_conc_s := ",34A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#:0#:0v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000Na_v2#61v32B#v32#??,2+v35##20+v24#170#8,1,<X#383?8#3873<Y,T,:v35T,;v32T,<#7T,13v30T,14+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10v32Lb+v35#8v30Mbv35#7"%pstring.
Lemma uboTf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTf] fx R M V uboTf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTf] LibSegJu_uboTf.regs0 LibSegJu_uboTf.kn0 LibSegJu_uboTf.BR LibSegJu_uboTf.PSS LibSegJu_uboTf.NX0 LibSegJu_uboTf.F0 230392 LibSegJu_uboTf.seg_sound_ax fx R M V uboTf_conc_s. Qed.
End PMBOUP2.
