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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_baIf LibSegJs_baIG LibSegJs_baIH LibSegJs_baI1 LibSegJs_baIT LibSegJs_baCf LibSegJs_baCG LibSegJs_baTG LibSegJs_baH LibSegJs_baC1s LibSegJs_baCT LibSegJs_baTf.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAP2.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_baIf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIf.regs0 LibSegJs_baIf.regs_out0).
Lemma KS_baIf_ok : BG.kept_ok 64 LibSegJs_baIf.regs0 LibSegJs_baIf.regs_out0 KS_baIf = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition baIf_conc_s := ",2:A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#80#80v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20,2+v35##20+v24#170#8,1,;X#371<4#372:4Y,T,:#3T,;v35T,<+v35v33T,14+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8#Mbv35#3"%pstring.
Lemma baIf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIf] fx R M V baIf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIf] LibSegJs_baIf.regs0 LibSegJs_baIf.kn0 LibSegJs_baIf.BR LibSegJs_baIf.PSS LibSegJs_baIf.NX0 LibSegJs_baIf.F0 225732 LibSegJs_baIf.seg_sound_ax fx R M V baIf_conc_s. Qed.
Definition KS_baIG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIG.regs0 LibSegJs_baIG.regs_out0).
Lemma KS_baIG_ok : BG.kept_ok 64 LibSegJs_baIG.regs0 LibSegJs_baIG.regs_out0 KS_baIG = true. Proof. vm_compute. reflexivity. Qed.
Definition baIG_conc_s := ",31A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8v36S,9v26S,:v34S,12v25S,13v23B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000Hv34#10Iv34*#2v23P_v2#80#80v34*#2v23Pv24#180v34*#2v23Pv26#10v34*#2v23Pv25#8v34*#2v23La_v2#78#37234La_v2#80v24B#2v36#800,1++v34v23##20,1,?X#3596<#:9160Y,T,1#37274T,2_v2#70T,8v24T,;v22T,<v23T,=v22T,13v34T,14++v23v34#20T,15+v34*#20v36Lb++v23v34#18#Nb++v23v34#10#Lb++v23v34#8#Mb+v23v34#3"%pstring.
Lemma baIG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIG] fx R M V baIG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIG] LibSegJs_baIG.regs0 LibSegJs_baIG.kn0 LibSegJs_baIG.BR LibSegJs_baIG.PSS LibSegJs_baIG.NX0 LibSegJs_baIG.F0 219500 LibSegJs_baIG.seg_sound_ax fx R M V baIG_conc_s. Qed.
Definition KS_baIH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIH.regs0 LibSegJs_baIH.regs_out0).
Lemma KS_baIH_ok : BG.kept_ok 64 LibSegJs_baIH.regs0 LibSegJs_baIH.regs_out0 KS_baIH = true. Proof. vm_compute. reflexivity. Qed.
Definition baIH_conc_s := ",2:A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v34S,14++v34v23#20S,15+v34*#20v36B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000B#2v36#800,2+v24#168#18_v2#68#20,1,=X#37274#54400Y,T,1#372:0T,:v22T,;v23T,<v22Lb_v2#50+v22v23Lb_v2#58v22Lb_v2#60v22Lb_v2#68v22Lb+v24#178+v34*#20v36Lb+v24#170++v34v23#20Lb+v24#168v34"%pstring.
Lemma baIH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIH] fx R M V baIH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIH] LibSegJs_baIH.regs0 LibSegJs_baIH.kn0 LibSegJs_baIH.BR LibSegJs_baIH.PSS LibSegJs_baIH.NX0 LibSegJs_baIH.F0 225908 LibSegJs_baIH.seg_sound_ax fx R M V baIH_conc_s. Qed.
Definition KS_baI1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baI1.regs0 LibSegJs_baI1.regs_out0).
Lemma KS_baI1_ok : BG.kept_ok 64 LibSegJs_baI1.regs0 LibSegJs_baI1.regs_out0 KS_baI1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baI1_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,1+v24#170#8,1,3X#372:0#372:4Y,Lb+v24#170r14"%pstring.
Lemma baI1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baI1] fx R M V baI1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baI1] LibSegJs_baI1.regs0 LibSegJs_baI1.kn0 LibSegJs_baI1.BR LibSegJs_baI1.PSS LibSegJs_baI1.NX0 LibSegJs_baI1.F0 225952 LibSegJs_baI1.seg_sound_ax fx R M V baI1_conc_s. Qed.
Definition KS_baIT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIT.regs0 LibSegJs_baIT.regs_out0).
Lemma KS_baIT_ok : BG.kept_ok 64 LibSegJs_baIT.regs0 LibSegJs_baIT.regs_out0 KS_baIT = true. Proof. vm_compute. reflexivity. Qed.
Definition baIT_conc_s := ",2<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#:?1>8Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?,1+v24#8#1,1,11X#372:4#37488Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#T,<v24T,=v26T,>#34598T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?Nb+v24#8#1"%pstring.
Lemma baIT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIT] fx R M V baIT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIT] LibSegJs_baIT.regs0 LibSegJs_baIT.kn0 LibSegJs_baIT.BR LibSegJs_baIT.PSS LibSegJs_baIT.NX0 LibSegJs_baIT.F0 225956 LibSegJs_baIT.seg_sound_ax fx R M V baIT_conc_s. Qed.
Definition KS_baCf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCf.regs0 LibSegJs_baCf.regs_out0).
Lemma KS_baCf_ok : BG.kept_ok 64 LibSegJs_baCf.regs0 LibSegJs_baCf.regs_out0 KS_baCf = true. Proof. vm_compute. reflexivity. Qed.
Definition baCf_conc_s := ",2?A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#80#80v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000,2+v35##20+v24#170#8,1,<X#371:4#37438Y,T,:#2T,;v35T,<+v35v33T,13v30T,15+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8v30Mbv35#2"%pstring.
Lemma baCf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCf] fx R M V baCf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCf] LibSegJs_baCf.regs0 LibSegJs_baCf.kn0 LibSegJs_baCf.BR LibSegJs_baCf.PSS LibSegJs_baCf.NX0 LibSegJs_baCf.F0 225700 LibSegJs_baCf.seg_sound_ax fx R M V baCf_conc_s. Qed.
Definition KS_baCG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCG.regs0 LibSegJs_baCG.regs_out0).
Lemma KS_baCG_ok : BG.kept_ok 64 LibSegJs_baCG.regs0 LibSegJs_baCG.regs_out0 KS_baCG = true. Proof. vm_compute. reflexivity. Qed.
Definition baCG_conc_s := ",34A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8v36S,9v26S,:v34S,12v25S,13v30S,14v23B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000Hv34#10Iv34*#2v23P_v2#80#80v34*#2v23Pv24#180v34*#2v23Pv26#10v34*#2v23Pv25#8v34*#2v23La_v2#78#3734<La_v2#80v24B#2v36#800B#v30#1000000,1++v34v23##20,1,?X#3596<#:9160Y,T,1#37408T,2_v2#70T,8v24T,;v22T,<v23T,=v22T,14v34T,15++v23v34#20T,16+v34*#20v36Lb++v23v34#18#Nb++v23v34#10#Lb++v23v34#8v30Mb+v23v34#2"%pstring.
Lemma baCG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCG] fx R M V baCG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCG] LibSegJs_baCG.regs0 LibSegJs_baCG.kn0 LibSegJs_baCG.BR LibSegJs_baCG.PSS LibSegJs_baCG.NX0 LibSegJs_baCG.F0 219500 LibSegJs_baCG.seg_sound_ax fx R M V baCG_conc_s. Qed.
Definition KS_baTG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTG.regs0 LibSegJs_baTG.regs_out0).
Lemma KS_baTG_ok : BG.kept_ok 64 LibSegJs_baTG.regs0 LibSegJs_baTG.regs_out0 KS_baTG = true. Proof. vm_compute. reflexivity. Qed.
Definition baTG_conc_s := ",37A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8v36S,9v26S,:v34S,12v25S,13v30S,14v23B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000Hv34#10Iv34*#2v23P_v2#80#80v34*#2v23Pv24#180v34*#2v23Pv26#10v34*#2v23Pv25#8v34*#2v23La_v2#78#373<4La_v2#80v24Na_v2#69v32B#v32#??B#2v36#800B#v30#1000000,1++v34v23##20,1,10X#3596<#:9160Y,T,1#37408T,2_v2#70T,8v24T,;v22T,<v23T,=v22T,>v32T,14v34T,15++v23v34#20T,16+v34*#20v36Lb++v23v34#18#Nb++v23v34#10v32Lb++v23v34#8v30Mb+v23v34#4"%pstring.
Lemma baTG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTG] fx R M V baTG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTG] LibSegJs_baTG.regs0 LibSegJs_baTG.kn0 LibSegJs_baTG.BR LibSegJs_baTG.PSS LibSegJs_baTG.NX0 LibSegJs_baTG.F0 219500 LibSegJs_baTG.seg_sound_ax fx R M V baTG_conc_s. Qed.
Definition KS_baH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baH.regs0 LibSegJs_baH.regs_out0).
Lemma KS_baH_ok : BG.kept_ok 64 LibSegJs_baH.regs0 LibSegJs_baH.regs_out0 KS_baH = true. Proof. vm_compute. reflexivity. Qed.
Definition baH_conc_s := ",2<A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v30S,14v34S,15++v34v23#20S,16+v34*#20v36B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000B#2v36#800,2+v24#168#18_v2#68#20,1,=X#37408#54400Y,T,1#37434T,:v22T,;v23T,<v22Lb_v2#50+v22v23Lb_v2#58v22Lb_v2#60v22Lb_v2#68v22Lb+v24#178+v34*#20v36Lb+v24#170++v34v23#20Lb+v24#168v34"%pstring.
Lemma baH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baH] fx R M V baH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baH] LibSegJs_baH.regs0 LibSegJs_baH.kn0 LibSegJs_baH.BR LibSegJs_baH.PSS LibSegJs_baH.NX0 LibSegJs_baH.F0 226312 LibSegJs_baH.seg_sound_ax fx R M V baH_conc_s. Qed.
Definition KS_baC1s : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baC1s.regs0 LibSegJs_baC1s.regs_out0).
Lemma KS_baC1s_ok : BG.kept_ok 64 LibSegJs_baC1s.regs0 LibSegJs_baC1s.regs_out0 KS_baC1s = true. Proof. vm_compute. reflexivity. Qed.
Definition baC1s_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,1+v24#170#8,1,3X#37434#37438Y,Lb+v24#170r15"%pstring.
Lemma baC1s_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baC1s] fx R M V baC1s_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baC1s] LibSegJs_baC1s.regs0 LibSegJs_baC1s.kn0 LibSegJs_baC1s.BR LibSegJs_baC1s.PSS LibSegJs_baC1s.NX0 LibSegJs_baC1s.F0 226356 LibSegJs_baC1s.seg_sound_ax fx R M V baC1s_conc_s. Qed.
Definition KS_baCT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCT.regs0 LibSegJs_baCT.regs_out0).
Lemma KS_baCT_ok : BG.kept_ok 64 LibSegJs_baCT.regs0 LibSegJs_baCT.regs_out0 KS_baCT = true. Proof. vm_compute. reflexivity. Qed.
Definition baCT_conc_s := ",2?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v30B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#:?1>8Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?B#v30#1000000,2_v2#80#10+v24#8#1,1,13X#37438#37488Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#T,<v24T,=v26T,>v26T,?#34598T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?Nb+v24#8#1Lb_v2#78#37458"%pstring.
Lemma baCT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCT] fx R M V baCT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCT] LibSegJs_baCT.regs0 LibSegJs_baCT.kn0 LibSegJs_baCT.BR LibSegJs_baCT.PSS LibSegJs_baCT.NX0 LibSegJs_baCT.F0 226360 LibSegJs_baCT.seg_sound_ax fx R M V baCT_conc_s. Qed.
Definition KS_baTf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTf.regs0 LibSegJs_baTf.regs_out0).
Lemma KS_baTf_ok : BG.kept_ok 64 LibSegJs_baTf.regs0 LibSegJs_baTf.regs_out0 KS_baTf = true. Proof. vm_compute. reflexivity. Qed.
Definition baTf_conc_s := ",33A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#80#80v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000Na_v2#69v32B#v32#??,2+v35##20+v24#170#8,1,<X#37154#37438Y,T,:v32T,;v35T,<#4T,13v30T,15+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10v32Lb+v35#8v30Mbv35#4"%pstring.
Lemma baTf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTf] fx R M V baTf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTf] LibSegJs_baTf.regs0 LibSegJs_baTf.kn0 LibSegJs_baTf.BR LibSegJs_baTf.PSS LibSegJs_baTf.NX0 LibSegJs_baTf.F0 225620 LibSegJs_baTf.seg_sound_ax fx R M V baTf_conc_s. Qed.
End PMBAP2.
