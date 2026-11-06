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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_baTs0 LibSegJs_baTs1 LibSegJs_baTs2 LibSegJs_baTs3 LibSegJs_baTs4 LibSegJs_baTs5 LibSegJs_baTs6 LibSegJs_baTs7 LibSegJs_baTs8 LibSegJs_baTs9 LibSegJs_baTs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAP3T.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_baTs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs0.regs0 LibSegJs_baTs0.regs_out0).
Lemma KS_baTs0_ok : BG.kept_ok 64 LibSegJs_baTs0.regs0 LibSegJs_baTs0.regs_out0 KS_baTs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition baTs0_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#2T,:#40T,;#2T,<#20T,=^#7#?????????????>0T,>v22T,13v30T,14#20Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs0] fx R M V baTs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs0] LibSegJs_baTs0.regs0 LibSegJs_baTs0.kn0 LibSegJs_baTs0.BR LibSegJs_baTs0.PSS LibSegJs_baTs0.NX0 LibSegJs_baTs0.F0 225620 LibSegJs_baTs0.seg_sound_ax fx R M V baTs0_conc_s. Qed.
Definition KS_baTs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs1.regs0 LibSegJs_baTs1.regs_out0).
Lemma KS_baTs1_ok : BG.kept_ok 64 LibSegJs_baTs1.regs0 LibSegJs_baTs1.regs_out0 KS_baTs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs1_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#4T,:#80T,;#4T,<#40T,=^#7#?????????????>0T,>v22T,13v30T,14#40Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs1] fx R M V baTs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs1] LibSegJs_baTs1.regs0 LibSegJs_baTs1.kn0 LibSegJs_baTs1.BR LibSegJs_baTs1.PSS LibSegJs_baTs1.NX0 LibSegJs_baTs1.F0 225620 LibSegJs_baTs1.seg_sound_ax fx R M V baTs1_conc_s. Qed.
Definition KS_baTs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs2.regs0 LibSegJs_baTs2.regs_out0).
Lemma KS_baTs2_ok : BG.kept_ok 64 LibSegJs_baTs2.regs0 LibSegJs_baTs2.regs_out0 KS_baTs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs2_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#8T,:#100T,;#8T,<#80T,=^#7#?????????????>0T,>v22T,13v30T,14#80Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs2] fx R M V baTs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs2] LibSegJs_baTs2.regs0 LibSegJs_baTs2.kn0 LibSegJs_baTs2.BR LibSegJs_baTs2.PSS LibSegJs_baTs2.NX0 LibSegJs_baTs2.F0 225620 LibSegJs_baTs2.seg_sound_ax fx R M V baTs2_conc_s. Qed.
Definition KS_baTs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs3.regs0 LibSegJs_baTs3.regs_out0).
Lemma KS_baTs3_ok : BG.kept_ok 64 LibSegJs_baTs3.regs0 LibSegJs_baTs3.regs_out0 KS_baTs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs3_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#10T,:#200T,;#10T,<#100T,=^#7#?????????????>0T,>v22T,13v30T,14#100Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs3] fx R M V baTs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs3] LibSegJs_baTs3.regs0 LibSegJs_baTs3.kn0 LibSegJs_baTs3.BR LibSegJs_baTs3.PSS LibSegJs_baTs3.NX0 LibSegJs_baTs3.F0 225620 LibSegJs_baTs3.seg_sound_ax fx R M V baTs3_conc_s. Qed.
Definition KS_baTs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs4.regs0 LibSegJs_baTs4.regs_out0).
Lemma KS_baTs4_ok : BG.kept_ok 64 LibSegJs_baTs4.regs0 LibSegJs_baTs4.regs_out0 KS_baTs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs4_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#20T,:#400T,;#20T,<#200T,=^#7#?????????????>0T,>v22T,13v30T,14#200Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs4] fx R M V baTs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs4] LibSegJs_baTs4.regs0 LibSegJs_baTs4.kn0 LibSegJs_baTs4.BR LibSegJs_baTs4.PSS LibSegJs_baTs4.NX0 LibSegJs_baTs4.F0 225620 LibSegJs_baTs4.seg_sound_ax fx R M V baTs4_conc_s. Qed.
Definition KS_baTs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs5.regs0 LibSegJs_baTs5.regs_out0).
Lemma KS_baTs5_ok : BG.kept_ok 64 LibSegJs_baTs5.regs0 LibSegJs_baTs5.regs_out0 KS_baTs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs5_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#40T,:#800T,;#40T,<#400T,=^#7#?????????????>0T,>v22T,13v30T,14#400Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs5] fx R M V baTs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs5] LibSegJs_baTs5.regs0 LibSegJs_baTs5.kn0 LibSegJs_baTs5.BR LibSegJs_baTs5.PSS LibSegJs_baTs5.NX0 LibSegJs_baTs5.F0 225620 LibSegJs_baTs5.seg_sound_ax fx R M V baTs5_conc_s. Qed.
Definition KS_baTs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs6.regs0 LibSegJs_baTs6.regs_out0).
Lemma KS_baTs6_ok : BG.kept_ok 64 LibSegJs_baTs6.regs0 LibSegJs_baTs6.regs_out0 KS_baTs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs6_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#80T,:#1000T,;#80T,<#800T,=^#7#?????????????>0T,>v22T,13v30T,14#800Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs6] fx R M V baTs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs6] LibSegJs_baTs6.regs0 LibSegJs_baTs6.kn0 LibSegJs_baTs6.BR LibSegJs_baTs6.PSS LibSegJs_baTs6.NX0 LibSegJs_baTs6.F0 225620 LibSegJs_baTs6.seg_sound_ax fx R M V baTs6_conc_s. Qed.
Definition KS_baTs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs7.regs0 LibSegJs_baTs7.regs_out0).
Lemma KS_baTs7_ok : BG.kept_ok 64 LibSegJs_baTs7.regs0 LibSegJs_baTs7.regs_out0 KS_baTs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs7_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#100T,:#2000T,;#100T,<#1000T,=^#7#?????????????>0T,>v22T,13v30T,14#1000Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs7] fx R M V baTs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs7] LibSegJs_baTs7.regs0 LibSegJs_baTs7.kn0 LibSegJs_baTs7.BR LibSegJs_baTs7.PSS LibSegJs_baTs7.NX0 LibSegJs_baTs7.F0 225620 LibSegJs_baTs7.seg_sound_ax fx R M V baTs7_conc_s. Qed.
Definition KS_baTs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs8.regs0 LibSegJs_baTs8.regs_out0).
Lemma KS_baTs8_ok : BG.kept_ok 64 LibSegJs_baTs8.regs0 LibSegJs_baTs8.regs_out0 KS_baTs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs8_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#200T,:#4000T,;#200T,<#2000T,=^#7#?????????????>0T,>v22T,13v30T,14#2000Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs8] fx R M V baTs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs8] LibSegJs_baTs8.regs0 LibSegJs_baTs8.kn0 LibSegJs_baTs8.BR LibSegJs_baTs8.PSS LibSegJs_baTs8.NX0 LibSegJs_baTs8.F0 225620 LibSegJs_baTs8.seg_sound_ax fx R M V baTs8_conc_s. Qed.
Definition KS_baTs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs9.regs0 LibSegJs_baTs9.regs_out0).
Lemma KS_baTs9_ok : BG.kept_ok 64 LibSegJs_baTs9.regs0 LibSegJs_baTs9.regs_out0 KS_baTs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs9_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#400T,:#8000T,;#400T,<#4000T,=^#7#?????????????>0T,>v22T,13v30T,14#4000Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs9] fx R M V baTs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs9] LibSegJs_baTs9.regs0 LibSegJs_baTs9.kn0 LibSegJs_baTs9.BR LibSegJs_baTs9.PSS LibSegJs_baTs9.NX0 LibSegJs_baTs9.F0 225620 LibSegJs_baTs9.seg_sound_ax fx R M V baTs9_conc_s. Qed.
Definition KS_baTs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTs10.regs0 LibSegJs_baTs10.regs_out0).
Lemma KS_baTs10_ok : BG.kept_ok 64 LibSegJs_baTs10.regs0 LibSegJs_baTs10.regs_out0 KS_baTs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition baTs10_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#37154#:>098Y,T,1#3596<T,2_v2#80T,8#800T,:#10000T,;#800T,<#8000T,=^#7#?????????????>0T,>v22T,13v30T,14#8000Lb_v2#80v24Lb_v2#78#373<4Lb_v2#48+v24#168"%pstring.
Lemma baTs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTs10] fx R M V baTs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTs10] LibSegJs_baTs10.regs0 LibSegJs_baTs10.kn0 LibSegJs_baTs10.BR LibSegJs_baTs10.PSS LibSegJs_baTs10.NX0 LibSegJs_baTs10.F0 225620 LibSegJs_baTs10.seg_sound_ax fx R M V baTs10_conc_s. Qed.
End PMBAP3T.
