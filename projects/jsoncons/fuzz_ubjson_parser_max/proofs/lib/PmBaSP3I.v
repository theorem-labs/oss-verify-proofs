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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_baIs0 LibSegJs_baIs1 LibSegJs_baIs2 LibSegJs_baIs3 LibSegJs_baIs4 LibSegJs_baIs5 LibSegJs_baIs6 LibSegJs_baIs7 LibSegJs_baIs8 LibSegJs_baIs9 LibSegJs_baIs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAP3I.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_baIs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs0.regs0 LibSegJs_baIs0.regs_out0).
Lemma KS_baIs0_ok : BG.kept_ok 64 LibSegJs_baIs0.regs0 LibSegJs_baIs0.regs_out0 KS_baIs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition baIs0_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#2T,:#40T,;#2T,<#20T,=^#7#?????????????>0T,>v22T,13#20Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs0] fx R M V baIs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs0] LibSegJs_baIs0.regs0 LibSegJs_baIs0.kn0 LibSegJs_baIs0.BR LibSegJs_baIs0.PSS LibSegJs_baIs0.NX0 LibSegJs_baIs0.F0 225732 LibSegJs_baIs0.seg_sound_ax fx R M V baIs0_conc_s. Qed.
Definition KS_baIs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs1.regs0 LibSegJs_baIs1.regs_out0).
Lemma KS_baIs1_ok : BG.kept_ok 64 LibSegJs_baIs1.regs0 LibSegJs_baIs1.regs_out0 KS_baIs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs1_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#4T,:#80T,;#4T,<#40T,=^#7#?????????????>0T,>v22T,13#40Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs1] fx R M V baIs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs1] LibSegJs_baIs1.regs0 LibSegJs_baIs1.kn0 LibSegJs_baIs1.BR LibSegJs_baIs1.PSS LibSegJs_baIs1.NX0 LibSegJs_baIs1.F0 225732 LibSegJs_baIs1.seg_sound_ax fx R M V baIs1_conc_s. Qed.
Definition KS_baIs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs2.regs0 LibSegJs_baIs2.regs_out0).
Lemma KS_baIs2_ok : BG.kept_ok 64 LibSegJs_baIs2.regs0 LibSegJs_baIs2.regs_out0 KS_baIs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs2_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#8T,:#100T,;#8T,<#80T,=^#7#?????????????>0T,>v22T,13#80Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs2] fx R M V baIs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs2] LibSegJs_baIs2.regs0 LibSegJs_baIs2.kn0 LibSegJs_baIs2.BR LibSegJs_baIs2.PSS LibSegJs_baIs2.NX0 LibSegJs_baIs2.F0 225732 LibSegJs_baIs2.seg_sound_ax fx R M V baIs2_conc_s. Qed.
Definition KS_baIs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs3.regs0 LibSegJs_baIs3.regs_out0).
Lemma KS_baIs3_ok : BG.kept_ok 64 LibSegJs_baIs3.regs0 LibSegJs_baIs3.regs_out0 KS_baIs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs3_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#10T,:#200T,;#10T,<#100T,=^#7#?????????????>0T,>v22T,13#100Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs3] fx R M V baIs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs3] LibSegJs_baIs3.regs0 LibSegJs_baIs3.kn0 LibSegJs_baIs3.BR LibSegJs_baIs3.PSS LibSegJs_baIs3.NX0 LibSegJs_baIs3.F0 225732 LibSegJs_baIs3.seg_sound_ax fx R M V baIs3_conc_s. Qed.
Definition KS_baIs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs4.regs0 LibSegJs_baIs4.regs_out0).
Lemma KS_baIs4_ok : BG.kept_ok 64 LibSegJs_baIs4.regs0 LibSegJs_baIs4.regs_out0 KS_baIs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs4_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#20T,:#400T,;#20T,<#200T,=^#7#?????????????>0T,>v22T,13#200Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs4] fx R M V baIs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs4] LibSegJs_baIs4.regs0 LibSegJs_baIs4.kn0 LibSegJs_baIs4.BR LibSegJs_baIs4.PSS LibSegJs_baIs4.NX0 LibSegJs_baIs4.F0 225732 LibSegJs_baIs4.seg_sound_ax fx R M V baIs4_conc_s. Qed.
Definition KS_baIs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs5.regs0 LibSegJs_baIs5.regs_out0).
Lemma KS_baIs5_ok : BG.kept_ok 64 LibSegJs_baIs5.regs0 LibSegJs_baIs5.regs_out0 KS_baIs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs5_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#40T,:#800T,;#40T,<#400T,=^#7#?????????????>0T,>v22T,13#400Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs5] fx R M V baIs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs5] LibSegJs_baIs5.regs0 LibSegJs_baIs5.kn0 LibSegJs_baIs5.BR LibSegJs_baIs5.PSS LibSegJs_baIs5.NX0 LibSegJs_baIs5.F0 225732 LibSegJs_baIs5.seg_sound_ax fx R M V baIs5_conc_s. Qed.
Definition KS_baIs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs6.regs0 LibSegJs_baIs6.regs_out0).
Lemma KS_baIs6_ok : BG.kept_ok 64 LibSegJs_baIs6.regs0 LibSegJs_baIs6.regs_out0 KS_baIs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs6_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#80T,:#1000T,;#80T,<#800T,=^#7#?????????????>0T,>v22T,13#800Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs6] fx R M V baIs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs6] LibSegJs_baIs6.regs0 LibSegJs_baIs6.kn0 LibSegJs_baIs6.BR LibSegJs_baIs6.PSS LibSegJs_baIs6.NX0 LibSegJs_baIs6.F0 225732 LibSegJs_baIs6.seg_sound_ax fx R M V baIs6_conc_s. Qed.
Definition KS_baIs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs7.regs0 LibSegJs_baIs7.regs_out0).
Lemma KS_baIs7_ok : BG.kept_ok 64 LibSegJs_baIs7.regs0 LibSegJs_baIs7.regs_out0 KS_baIs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs7_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#100T,:#2000T,;#100T,<#1000T,=^#7#?????????????>0T,>v22T,13#1000Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs7] fx R M V baIs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs7] LibSegJs_baIs7.regs0 LibSegJs_baIs7.kn0 LibSegJs_baIs7.BR LibSegJs_baIs7.PSS LibSegJs_baIs7.NX0 LibSegJs_baIs7.F0 225732 LibSegJs_baIs7.seg_sound_ax fx R M V baIs7_conc_s. Qed.
Definition KS_baIs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs8.regs0 LibSegJs_baIs8.regs_out0).
Lemma KS_baIs8_ok : BG.kept_ok 64 LibSegJs_baIs8.regs0 LibSegJs_baIs8.regs_out0 KS_baIs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs8_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#200T,:#4000T,;#200T,<#2000T,=^#7#?????????????>0T,>v22T,13#2000Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs8] fx R M V baIs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs8] LibSegJs_baIs8.regs0 LibSegJs_baIs8.kn0 LibSegJs_baIs8.BR LibSegJs_baIs8.PSS LibSegJs_baIs8.NX0 LibSegJs_baIs8.F0 225732 LibSegJs_baIs8.seg_sound_ax fx R M V baIs8_conc_s. Qed.
Definition KS_baIs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs9.regs0 LibSegJs_baIs9.regs_out0).
Lemma KS_baIs9_ok : BG.kept_ok 64 LibSegJs_baIs9.regs0 LibSegJs_baIs9.regs_out0 KS_baIs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs9_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#400T,:#8000T,;#400T,<#4000T,=^#7#?????????????>0T,>v22T,13#4000Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs9] fx R M V baIs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs9] LibSegJs_baIs9.regs0 LibSegJs_baIs9.kn0 LibSegJs_baIs9.BR LibSegJs_baIs9.PSS LibSegJs_baIs9.NX0 LibSegJs_baIs9.F0 225732 LibSegJs_baIs9.seg_sound_ax fx R M V baIs9_conc_s. Qed.
Definition KS_baIs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baIs10.regs0 LibSegJs_baIs10.regs_out0).
Lemma KS_baIs10_ok : BG.kept_ok 64 LibSegJs_baIs10.regs0 LibSegJs_baIs10.regs_out0 KS_baIs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition baIs10_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#371<4#:>098Y,T,1#3596<T,2_v2#80T,8#800T,:#10000T,;#800T,<#8000T,=^#7#?????????????>0T,>v22T,13#8000Lb_v2#80v24Lb_v2#78#37234Lb_v2#48+v24#168"%pstring.
Lemma baIs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baIs10] fx R M V baIs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baIs10] LibSegJs_baIs10.regs0 LibSegJs_baIs10.kn0 LibSegJs_baIs10.BR LibSegJs_baIs10.PSS LibSegJs_baIs10.NX0 LibSegJs_baIs10.F0 225732 LibSegJs_baIs10.seg_sound_ax fx R M V baIs10_conc_s. Qed.
End PMBAP3I.
