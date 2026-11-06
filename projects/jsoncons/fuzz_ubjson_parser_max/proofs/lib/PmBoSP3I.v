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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_boIs0 LibSegJs_boIs1 LibSegJs_boIs2 LibSegJs_boIs3 LibSegJs_boIs4 LibSegJs_boIs5 LibSegJs_boIs6 LibSegJs_boIs7 LibSegJs_boIs8 LibSegJs_boIs9 LibSegJs_boIs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOP3I.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_boIs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs0.regs0 LibSegJs_boIs0.regs_out0).
Lemma KS_boIs0_ok : BG.kept_ok 64 LibSegJs_boIs0.regs0 LibSegJs_boIs0.regs_out0 KS_boIs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition boIs0_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#2T,:#40T,;#2T,<#20T,=^#7#?????????????>0T,>v22T,13#20Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs0] fx R M V boIs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs0] LibSegJs_boIs0.regs0 LibSegJs_boIs0.kn0 LibSegJs_boIs0.BR LibSegJs_boIs0.PSS LibSegJs_boIs0.NX0 LibSegJs_boIs0.F0 226792 LibSegJs_boIs0.seg_sound_ax fx R M V boIs0_conc_s. Qed.
Definition KS_boIs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs1.regs0 LibSegJs_boIs1.regs_out0).
Lemma KS_boIs1_ok : BG.kept_ok 64 LibSegJs_boIs1.regs0 LibSegJs_boIs1.regs_out0 KS_boIs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs1_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#4T,:#80T,;#4T,<#40T,=^#7#?????????????>0T,>v22T,13#40Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs1] fx R M V boIs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs1] LibSegJs_boIs1.regs0 LibSegJs_boIs1.kn0 LibSegJs_boIs1.BR LibSegJs_boIs1.PSS LibSegJs_boIs1.NX0 LibSegJs_boIs1.F0 226792 LibSegJs_boIs1.seg_sound_ax fx R M V boIs1_conc_s. Qed.
Definition KS_boIs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs2.regs0 LibSegJs_boIs2.regs_out0).
Lemma KS_boIs2_ok : BG.kept_ok 64 LibSegJs_boIs2.regs0 LibSegJs_boIs2.regs_out0 KS_boIs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs2_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#8T,:#100T,;#8T,<#80T,=^#7#?????????????>0T,>v22T,13#80Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs2] fx R M V boIs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs2] LibSegJs_boIs2.regs0 LibSegJs_boIs2.kn0 LibSegJs_boIs2.BR LibSegJs_boIs2.PSS LibSegJs_boIs2.NX0 LibSegJs_boIs2.F0 226792 LibSegJs_boIs2.seg_sound_ax fx R M V boIs2_conc_s. Qed.
Definition KS_boIs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs3.regs0 LibSegJs_boIs3.regs_out0).
Lemma KS_boIs3_ok : BG.kept_ok 64 LibSegJs_boIs3.regs0 LibSegJs_boIs3.regs_out0 KS_boIs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs3_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#10T,:#200T,;#10T,<#100T,=^#7#?????????????>0T,>v22T,13#100Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs3] fx R M V boIs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs3] LibSegJs_boIs3.regs0 LibSegJs_boIs3.kn0 LibSegJs_boIs3.BR LibSegJs_boIs3.PSS LibSegJs_boIs3.NX0 LibSegJs_boIs3.F0 226792 LibSegJs_boIs3.seg_sound_ax fx R M V boIs3_conc_s. Qed.
Definition KS_boIs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs4.regs0 LibSegJs_boIs4.regs_out0).
Lemma KS_boIs4_ok : BG.kept_ok 64 LibSegJs_boIs4.regs0 LibSegJs_boIs4.regs_out0 KS_boIs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs4_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#20T,:#400T,;#20T,<#200T,=^#7#?????????????>0T,>v22T,13#200Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs4] fx R M V boIs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs4] LibSegJs_boIs4.regs0 LibSegJs_boIs4.kn0 LibSegJs_boIs4.BR LibSegJs_boIs4.PSS LibSegJs_boIs4.NX0 LibSegJs_boIs4.F0 226792 LibSegJs_boIs4.seg_sound_ax fx R M V boIs4_conc_s. Qed.
Definition KS_boIs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs5.regs0 LibSegJs_boIs5.regs_out0).
Lemma KS_boIs5_ok : BG.kept_ok 64 LibSegJs_boIs5.regs0 LibSegJs_boIs5.regs_out0 KS_boIs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs5_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#40T,:#800T,;#40T,<#400T,=^#7#?????????????>0T,>v22T,13#400Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs5] fx R M V boIs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs5] LibSegJs_boIs5.regs0 LibSegJs_boIs5.kn0 LibSegJs_boIs5.BR LibSegJs_boIs5.PSS LibSegJs_boIs5.NX0 LibSegJs_boIs5.F0 226792 LibSegJs_boIs5.seg_sound_ax fx R M V boIs5_conc_s. Qed.
Definition KS_boIs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs6.regs0 LibSegJs_boIs6.regs_out0).
Lemma KS_boIs6_ok : BG.kept_ok 64 LibSegJs_boIs6.regs0 LibSegJs_boIs6.regs_out0 KS_boIs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs6_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#80T,:#1000T,;#80T,<#800T,=^#7#?????????????>0T,>v22T,13#800Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs6] fx R M V boIs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs6] LibSegJs_boIs6.regs0 LibSegJs_boIs6.kn0 LibSegJs_boIs6.BR LibSegJs_boIs6.PSS LibSegJs_boIs6.NX0 LibSegJs_boIs6.F0 226792 LibSegJs_boIs6.seg_sound_ax fx R M V boIs6_conc_s. Qed.
Definition KS_boIs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs7.regs0 LibSegJs_boIs7.regs_out0).
Lemma KS_boIs7_ok : BG.kept_ok 64 LibSegJs_boIs7.regs0 LibSegJs_boIs7.regs_out0 KS_boIs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs7_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#100T,:#2000T,;#100T,<#1000T,=^#7#?????????????>0T,>v22T,13#1000Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs7] fx R M V boIs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs7] LibSegJs_boIs7.regs0 LibSegJs_boIs7.kn0 LibSegJs_boIs7.BR LibSegJs_boIs7.PSS LibSegJs_boIs7.NX0 LibSegJs_boIs7.F0 226792 LibSegJs_boIs7.seg_sound_ax fx R M V boIs7_conc_s. Qed.
Definition KS_boIs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs8.regs0 LibSegJs_boIs8.regs_out0).
Lemma KS_boIs8_ok : BG.kept_ok 64 LibSegJs_boIs8.regs0 LibSegJs_boIs8.regs_out0 KS_boIs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs8_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#200T,:#4000T,;#200T,<#2000T,=^#7#?????????????>0T,>v22T,13#2000Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs8] fx R M V boIs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs8] LibSegJs_boIs8.regs0 LibSegJs_boIs8.kn0 LibSegJs_boIs8.BR LibSegJs_boIs8.PSS LibSegJs_boIs8.NX0 LibSegJs_boIs8.F0 226792 LibSegJs_boIs8.seg_sound_ax fx R M V boIs8_conc_s. Qed.
Definition KS_boIs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs9.regs0 LibSegJs_boIs9.regs_out0).
Lemma KS_boIs9_ok : BG.kept_ok 64 LibSegJs_boIs9.regs0 LibSegJs_boIs9.regs_out0 KS_boIs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs9_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#400T,:#8000T,;#400T,<#4000T,=^#7#?????????????>0T,>v22T,13#4000Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs9] fx R M V boIs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs9] LibSegJs_boIs9.regs0 LibSegJs_boIs9.kn0 LibSegJs_boIs9.BR LibSegJs_boIs9.PSS LibSegJs_boIs9.NX0 LibSegJs_boIs9.F0 226792 LibSegJs_boIs9.seg_sound_ax fx R M V boIs9_conc_s. Qed.
Definition KS_boIs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boIs10.regs0 LibSegJs_boIs10.regs_out0).
Lemma KS_boIs10_ok : BG.kept_ok 64 LibSegJs_boIs10.regs0 LibSegJs_boIs10.regs_out0 KS_boIs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition boIs10_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10,2_v2#80#10_v2#48#8,1,>X#375>8#:>098Y,T,1#3596<T,2_v2#80T,8#800T,:#10000T,;#800T,<#8000T,=^#7#?????????????>0T,>v22T,13#8000Lb_v2#80v24Lb_v2#78#37670Lb_v2#48+v24#168"%pstring.
Lemma boIs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boIs10] fx R M V boIs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boIs10] LibSegJs_boIs10.regs0 LibSegJs_boIs10.kn0 LibSegJs_boIs10.BR LibSegJs_boIs10.PSS LibSegJs_boIs10.NX0 LibSegJs_boIs10.F0 226792 LibSegJs_boIs10.seg_sound_ax fx R M V boIs10_conc_s. Qed.
End PMBOP3I.
