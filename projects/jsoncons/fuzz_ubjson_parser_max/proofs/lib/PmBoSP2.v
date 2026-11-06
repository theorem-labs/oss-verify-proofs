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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_boIf LibSegJs_boIG LibSegJs_boIH LibSegJs_boI1 LibSegJs_boIT LibSegJs_boCf LibSegJs_boCG LibSegJs_boTG LibSegJs_boH LibSegJs_boC1s LibSegJs_boCT LibSegJs_boTf.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOP2.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_boIf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIf.regs0 LibSegJs_boIf.regs_out0).
Lemma KS_boIf_ok : BG.kept_ok 64 LibSegJs_boIf.regs0 LibSegJs_boIf.regs_out0 KS_boIf = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition boIf_conc_s := ",2:A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#80#80v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20,2+v35##20+v24#170#8,1,;X#375>8#376>0Y,T,:#9T,;v35T,<+v35v33T,14+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8#Mbv35#9"%pstring.
Lemma boIf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIf] fx R M V boIf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIf] LibSegJs_boIf.regs0 LibSegJs_boIf.kn0 LibSegJs_boIf.BR LibSegJs_boIf.PSS LibSegJs_boIf.NX0 LibSegJs_boIf.F0 226792 LibSegJs_boIf.seg_sound_ax fx R M V boIf_conc_s. Qed.
Definition KS_boIG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIG.regs0 LibSegJs_boIG.regs_out0).
Lemma KS_boIG_ok : BG.kept_ok 64 LibSegJs_boIG.regs0 LibSegJs_boIG.regs_out0 KS_boIG = true. Proof. vm_compute. reflexivity. Qed.
Definition boIG_conc_s := ",31A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8v36S,9v26S,:v34S,12v25S,13v23B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000Hv34#10Iv34*#2v23P_v2#80#80v34*#2v23Pv24#180v34*#2v23Pv26#10v34*#2v23Pv25#8v34*#2v23La_v2#78#37670La_v2#80v24B#2v36#800,1++v34v23##20,1,?X#3596<#:9160Y,T,1#376;0T,2_v2#70T,8v24T,;v22T,<v23T,=v22T,13v34T,14++v23v34#20T,15+v34*#20v36Lb++v23v34#18#Nb++v23v34#10#Lb++v23v34#8#Mb+v23v34#9"%pstring.
Lemma boIG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIG] fx R M V boIG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIG] LibSegJs_boIG.regs0 LibSegJs_boIG.kn0 LibSegJs_boIG.BR LibSegJs_boIG.PSS LibSegJs_boIG.NX0 LibSegJs_boIG.F0 219500 LibSegJs_boIG.seg_sound_ax fx R M V boIG_conc_s. Qed.
Definition KS_boIH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIH.regs0 LibSegJs_boIH.regs_out0).
Lemma KS_boIH_ok : BG.kept_ok 64 LibSegJs_boIH.regs0 LibSegJs_boIH.regs_out0 KS_boIH = true. Proof. vm_compute. reflexivity. Qed.
Definition boIH_conc_s := ",2:A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v34S,14++v34v23#20S,15+v34*#20v36B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000B#2v36#800,2+v24#168#18_v2#68#20,1,=X#376;0#54400Y,T,1#376=<T,:v22T,;v23T,<v22Lb_v2#50+v22v23Lb_v2#58v22Lb_v2#60v22Lb_v2#68v22Lb+v24#178+v34*#20v36Lb+v24#170++v34v23#20Lb+v24#168v34"%pstring.
Lemma boIH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIH] fx R M V boIH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIH] LibSegJs_boIH.regs0 LibSegJs_boIH.kn0 LibSegJs_boIH.BR LibSegJs_boIH.PSS LibSegJs_boIH.NX0 LibSegJs_boIH.F0 226992 LibSegJs_boIH.seg_sound_ax fx R M V boIH_conc_s. Qed.
Definition KS_boI1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boI1.regs0 LibSegJs_boI1.regs_out0).
Lemma KS_boI1_ok : BG.kept_ok 64 LibSegJs_boI1.regs0 LibSegJs_boI1.regs_out0 KS_boI1 = true. Proof. vm_compute. reflexivity. Qed.
Definition boI1_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,1+v24#170#8,1,3X#376=<#376>0Y,Lb+v24#170r14"%pstring.
Lemma boI1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boI1] fx R M V boI1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boI1] LibSegJs_boI1.regs0 LibSegJs_boI1.kn0 LibSegJs_boI1.BR LibSegJs_boI1.PSS LibSegJs_boI1.NX0 LibSegJs_boI1.F0 227036 LibSegJs_boI1.seg_sound_ax fx R M V boI1_conc_s. Qed.
Definition KS_boIT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIT.regs0 LibSegJs_boIT.regs_out0).
Lemma KS_boIT_ok : BG.kept_ok 64 LibSegJs_boIT.regs0 LibSegJs_boIT.regs_out0 KS_boIT = true. Proof. vm_compute. reflexivity. Qed.
Definition boIT_conc_s := ",2<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#:?1>8Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?,1+v24#8#1,1,11X#376>0#378:<Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#T,<v24T,=v26T,>#34558T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?Nb+v24#8#1"%pstring.
Lemma boIT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIT] fx R M V boIT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIT] LibSegJs_boIT.regs0 LibSegJs_boIT.kn0 LibSegJs_boIT.BR LibSegJs_boIT.PSS LibSegJs_boIT.NX0 LibSegJs_boIT.F0 227040 LibSegJs_boIT.seg_sound_ax fx R M V boIT_conc_s. Qed.
Definition KS_boCf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boCf.regs0 LibSegJs_boCf.regs_out0).
Lemma KS_boCf_ok : BG.kept_ok 64 LibSegJs_boCf.regs0 LibSegJs_boCf.regs_out0 KS_boCf = true. Proof. vm_compute. reflexivity. Qed.
Definition boCf_conc_s := ",2?A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#80#80v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000,2+v35##20+v24#170#8,1,<X#375<8#3785<Y,T,:#5T,;v35T,<+v35v33T,13v30T,15+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10#Lb+v35#8v30Mbv35#5"%pstring.
Lemma boCf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boCf] fx R M V boCf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boCf] LibSegJs_boCf.regs0 LibSegJs_boCf.kn0 LibSegJs_boCf.BR LibSegJs_boCf.PSS LibSegJs_boCf.NX0 LibSegJs_boCf.F0 226760 LibSegJs_boCf.seg_sound_ax fx R M V boCf_conc_s. Qed.
Definition KS_boCG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boCG.regs0 LibSegJs_boCG.regs_out0).
Lemma KS_boCG_ok : BG.kept_ok 64 LibSegJs_boCG.regs0 LibSegJs_boCG.regs_out0 KS_boCG = true. Proof. vm_compute. reflexivity. Qed.
Definition boCG_conc_s := ",34A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8v36S,9v26S,:v34S,12v25S,13v30S,14v23B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000Hv34#10Iv34*#2v23P_v2#80#80v34*#2v23Pv24#180v34*#2v23Pv26#10v34*#2v23Pv25#8v34*#2v23La_v2#78#37770La_v2#80v24B#2v36#800B#v30#1000000,1++v34v23##20,1,?X#3596<#:9160Y,T,1#3782<T,2_v2#70T,8v24T,;v22T,<v23T,=v22T,14v34T,15++v23v34#20T,16+v34*#20v36Lb++v23v34#18#Nb++v23v34#10#Lb++v23v34#8v30Mb+v23v34#5"%pstring.
Lemma boCG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boCG] fx R M V boCG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boCG] LibSegJs_boCG.regs0 LibSegJs_boCG.kn0 LibSegJs_boCG.BR LibSegJs_boCG.PSS LibSegJs_boCG.NX0 LibSegJs_boCG.F0 219500 LibSegJs_boCG.seg_sound_ax fx R M V boCG_conc_s. Qed.
Definition KS_boTG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boTG.regs0 LibSegJs_boTG.regs_out0).
Lemma KS_boTG_ok : BG.kept_ok 64 LibSegJs_boTG.regs0 LibSegJs_boTG.regs_out0 KS_boTG = true. Proof. vm_compute. reflexivity. Qed.
Definition boTG_conc_s := ",37A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8v36S,9v26S,:v34S,12v25S,13v30S,14v23B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000Hv34#10Iv34*#2v23P_v2#80#80v34*#2v23Pv24#180v34*#2v23Pv26#10v34*#2v23Pv25#8v34*#2v23La_v2#78#377>8La_v2#80v24Na_v2#69v32B#v32#??B#2v36#800B#v30#1000000,1++v34v23##20,1,10X#3596<#:9160Y,T,1#3782<T,2_v2#70T,8v24T,;v22T,<v23T,=v22T,>v32T,14v34T,15++v23v34#20T,16+v34*#20v36Lb++v23v34#18#Nb++v23v34#10v32Lb++v23v34#8v30Mb+v23v34#7"%pstring.
Lemma boTG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boTG] fx R M V boTG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boTG] LibSegJs_boTG.regs0 LibSegJs_boTG.kn0 LibSegJs_boTG.BR LibSegJs_boTG.PSS LibSegJs_boTG.NX0 LibSegJs_boTG.F0 219500 LibSegJs_boTG.seg_sound_ax fx R M V boTG_conc_s. Qed.
Definition KS_boH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boH.regs0 LibSegJs_boH.regs_out0).
Lemma KS_boH_ok : BG.kept_ok 64 LibSegJs_boH.regs0 LibSegJs_boH.regs_out0 KS_boH = true. Proof. vm_compute. reflexivity. Qed.
Definition boH_conc_s := ",2<A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v30S,14v34S,15++v34v23#20S,16+v34*#20v36B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22v23La+v24#178+v22v23B#1000v22#7??????00000Hv22#10B#20v23#8000Hv23#20B#1000v34#7??????00000B#2v36#800,2+v24#168#18_v2#68#20,1,=X#3782<#54400Y,T,1#37858T,:v22T,;v23T,<v22Lb_v2#50+v22v23Lb_v2#58v22Lb_v2#60v22Lb_v2#68v22Lb+v24#178+v34*#20v36Lb+v24#170++v34v23#20Lb+v24#168v34"%pstring.
Lemma boH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boH] fx R M V boH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boH] LibSegJs_boH.regs0 LibSegJs_boH.kn0 LibSegJs_boH.BR LibSegJs_boH.PSS LibSegJs_boH.NX0 LibSegJs_boH.F0 227372 LibSegJs_boH.seg_sound_ax fx R M V boH_conc_s. Qed.
Definition KS_boC1s : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boC1s.regs0 LibSegJs_boC1s.regs_out0).
Lemma KS_boC1s_ok : BG.kept_ok 64 LibSegJs_boC1s.regs0 LibSegJs_boC1s.regs_out0 KS_boC1s = true. Proof. vm_compute. reflexivity. Qed.
Definition boC1s_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,1+v24#170#8,1,3X#37858#3785<Y,Lb+v24#170r15"%pstring.
Lemma boC1s_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boC1s] fx R M V boC1s_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boC1s] LibSegJs_boC1s.regs0 LibSegJs_boC1s.kn0 LibSegJs_boC1s.BR LibSegJs_boC1s.PSS LibSegJs_boC1s.NX0 LibSegJs_boC1s.F0 227416 LibSegJs_boC1s.seg_sound_ax fx R M V boC1s_conc_s. Qed.
Definition KS_boCT : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boCT.regs0 LibSegJs_boCT.regs_out0).
Lemma KS_boCT_ok : BG.kept_ok 64 LibSegJs_boCT.regs0 LibSegJs_boCT.regs_out0 KS_boCT = true. Proof. vm_compute. reflexivity. Qed.
Definition boCT_conc_s := ",2?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13v30B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Lav25#:?1>8Na+v24#10#La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?B#v30#1000000,2_v2#80#10+v24#8#1,1,13X#3785<#378:<Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#T,<v24T,=v26T,>v26T,?#34558T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?Nb+v24#8#1Lb_v2#78#3787<"%pstring.
Lemma boCT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boCT] fx R M V boCT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boCT] LibSegJs_boCT.regs0 LibSegJs_boCT.kn0 LibSegJs_boCT.BR LibSegJs_boCT.PSS LibSegJs_boCT.NX0 LibSegJs_boCT.F0 227420 LibSegJs_boCT.seg_sound_ax fx R M V boCT_conc_s. Qed.
Definition KS_boTf : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boTf.regs0 LibSegJs_boTf.regs_out0).
Lemma KS_boTf_ok : BG.kept_ok 64 LibSegJs_boTf.regs0 LibSegJs_boTf.regs_out0 KS_boTf = true. Proof. vm_compute. reflexivity. Qed.
Definition boTf_conc_s := ",33A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40A#v32p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170v35La+v24#178+v35v33B#20v33#10000Hv33#20B#1000v35#7??????00000Hv35#10Iv35#20P_v2#80#80v35#20Pv24#180v35#20Pv26#10v35#20Pv25#8v35#20Mav26#La+v24#148#1000000B#v30#1000000Na_v2#69v32B#v32#??,2+v35##20+v24#170#8,1,<X#3755<#3785<Y,T,:v32T,;v35T,<#7T,13v30T,15+v35#20Lb+v24#170+v35#20Lb+v35#18#Nb+v35#10v32Lb+v35#8v30Mbv35#7"%pstring.
Lemma boTf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boTf] fx R M V boTf_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boTf] LibSegJs_boTf.regs0 LibSegJs_boTf.kn0 LibSegJs_boTf.BR LibSegJs_boTf.PSS LibSegJs_boTf.NX0 LibSegJs_boTf.F0 226652 LibSegJs_boTf.seg_sound_ax fx R M V boTf_conc_s. Qed.
End PMBOP2.
