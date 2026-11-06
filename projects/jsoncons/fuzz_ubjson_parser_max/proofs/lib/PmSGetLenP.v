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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_glA LibSegJs_glE0 LibSegJs_glB LibSegJs_glTi_c1 LibSegJs_glTU LibSegJs_glTI LibSegJs_glTl_c1 LibSegJs_glTL LibSegJs_glTd1 LibSegJs_glTd2 LibSegJs_glTd3 LibSegJs_glTd4 LibSegJs_glTd5 LibSegJs_glTd6 LibSegJs_glNi_c1 LibSegJs_glNU LibSegJs_glNI LibSegJs_glNl_c1 LibSegJs_glNL LibSegJs_glVi_c1 LibSegJs_glVU LibSegJs_glVI LibSegJs_glVl_c1 LibSegJs_glVL LibSegJs_glSi_c1 LibSegJs_glSI LibSegJs_glSl_c1 LibSegJs_glSL LibSegJs_glZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSGLP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_glA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glA.regs0 LibSegJs_glA.regs_out0).
Lemma KS_glA_ok : BG.kept_ok 48 LibSegJs_glA.regs0 LibSegJs_glA.regs_out0 KS_glA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition glA_conc_s := ",?A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,1_v2#40#40,1,?X#36<?8#36830Y,T,1#36=2<T,2_v2#40T,8v24T,9v25T,:+v24#18T,;_v2#29T,<#1T,12+v24#18Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma glA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glA] fx R M V glA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glA] LibSegJs_glA.regs0 LibSegJs_glA.kn0 LibSegJs_glA.BR LibSegJs_glA.PSS LibSegJs_glA.NX0 LibSegJs_glA.F0 224504 LibSegJs_glA.seg_sound_ax fx R M V glA_conc_s. Qed.
Definition KS_glE0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glE0.regs0 LibSegJs_glE0.regs_out0).
Lemma KS_glE0_ok : BG.kept_ok 48 LibSegJs_glE0.regs0 LibSegJs_glE0.regs_out0 KS_glE0 = true. Proof. vm_compute. reflexivity. Qed.
Definition glE0_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,5X#36=2<#36490Y,T,1#36><0T,:v25T,;#1"%pstring.
Lemma glE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glE0] fx R M V glE0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glE0] LibSegJs_glE0.regs0 LibSegJs_glE0.kn0 LibSegJs_glE0.BR LibSegJs_glE0.PSS LibSegJs_glE0.NX0 LibSegJs_glE0.F0 224556 LibSegJs_glE0.seg_sound_ax fx R M V glE0_conc_s. Qed.
Definition KS_glB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glB.regs0 LibSegJs_glB.regs_out0).
Lemma KS_glB_ok : BG.kept_ok 48 LibSegJs_glB.regs0 LibSegJs_glB.regs_out0 KS_glB = true. Proof. vm_compute. reflexivity. Qed.
Definition glB_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#1S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,2X#36=2<#36=30Y,"%pstring.
Lemma glB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glB] fx R M V glB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glB] LibSegJs_glB.regs0 LibSegJs_glB.kn0 LibSegJs_glB.BR LibSegJs_glB.PSS LibSegJs_glB.NX0 LibSegJs_glB.F0 224556 LibSegJs_glB.seg_sound_ax fx R M V glB_conc_s. Qed.
Definition KS_glTi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTi_c1.regs0 LibSegJs_glTi_c1.regs_out0).
Lemma KS_glTi_ok : BG.kept_ok 48 LibSegJs_glTi_c1.regs0 LibSegJs_glTi_c1.regs_out0 KS_glTi = true. Proof. vm_compute. reflexivity. Qed.
Definition glTi_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#69S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#36=34#36830Y,T,1#36=68T,:+v24#18T,;_v2#38T,<#1T,13#1"%pstring.
Lemma glTi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTi] fx R M V glTi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTi] LibSegJs_glTi_c1.regs0 LibSegJs_glTi_c1.kn0 LibSegJs_glTi_c1.BR LibSegJs_glTi_c1.PSS LibSegJs_glTi_c1.NX0 LibSegJs_glTi_c1.F0 224564 LibSegJs_glTi_c1.seg_sound_ax fx R M V glTi_conc_s. Qed.
Definition KS_glTU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTU.regs0 LibSegJs_glTU.regs_out0).
Lemma KS_glTU_ok : BG.kept_ok 48 LibSegJs_glTU.regs0 LibSegJs_glTU.regs_out0 KS_glTU = true. Proof. vm_compute. reflexivity. Qed.
Definition glTU_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#55S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,6X#36=34#36830Y,T,1#36>24T,:+v24#18T,;_v2#38T,<#1"%pstring.
Lemma glTU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTU] fx R M V glTU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTU] LibSegJs_glTU.regs0 LibSegJs_glTU.kn0 LibSegJs_glTU.BR LibSegJs_glTU.PSS LibSegJs_glTU.NX0 LibSegJs_glTU.F0 224564 LibSegJs_glTU.seg_sound_ax fx R M V glTU_conc_s. Qed.
Definition KS_glTI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTI.regs0 LibSegJs_glTI.regs_out0).
Lemma KS_glTI_ok : BG.kept_ok 48 LibSegJs_glTI.regs0 LibSegJs_glTI.regs_out0 KS_glTI = true. Proof. vm_compute. reflexivity. Qed.
Definition glTI_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#49S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#36=34#36830Y,T,1#36>94T,:+v24#18T,;_v2#38T,<#2T,13#2"%pstring.
Lemma glTI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTI] fx R M V glTI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTI] LibSegJs_glTI.regs0 LibSegJs_glTI.kn0 LibSegJs_glTI.BR LibSegJs_glTI.PSS LibSegJs_glTI.NX0 LibSegJs_glTI.F0 224564 LibSegJs_glTI.seg_sound_ax fx R M V glTI_conc_s. Qed.
Definition KS_glTl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTl_c1.regs0 LibSegJs_glTl_c1.regs_out0).
Lemma KS_glTl_ok : BG.kept_ok 48 LibSegJs_glTl_c1.regs0 LibSegJs_glTl_c1.regs_out0 KS_glTl = true. Proof. vm_compute. reflexivity. Qed.
Definition glTl_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#6<S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#36=34#36830Y,T,1#36>44T,:+v24#18T,;_v2#38T,<#4T,13#4"%pstring.
Lemma glTl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTl] fx R M V glTl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTl] LibSegJs_glTl_c1.regs0 LibSegJs_glTl_c1.kn0 LibSegJs_glTl_c1.BR LibSegJs_glTl_c1.PSS LibSegJs_glTl_c1.NX0 LibSegJs_glTl_c1.F0 224564 LibSegJs_glTl_c1.seg_sound_ax fx R M V glTl_conc_s. Qed.
Definition KS_glTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTL.regs0 LibSegJs_glTL.regs_out0).
Lemma KS_glTL_ok : BG.kept_ok 48 LibSegJs_glTL.regs0 LibSegJs_glTL.regs_out0 KS_glTL = true. Proof. vm_compute. reflexivity. Qed.
Definition glTL_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#4<S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#36=34#36830Y,T,1#36=:0T,:+v24#18T,;_v2#38T,<#8T,13#8"%pstring.
Lemma glTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTL] fx R M V glTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTL] LibSegJs_glTL.regs0 LibSegJs_glTL.kn0 LibSegJs_glTL.BR LibSegJs_glTL.PSS LibSegJs_glTL.NX0 LibSegJs_glTL.F0 224564 LibSegJs_glTL.seg_sound_ax fx R M V glTL_conc_s. Qed.
Definition KS_glTd1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTd1.regs0 LibSegJs_glTd1.regs_out0).
Lemma KS_glTd1_ok : BG.kept_ok 48 LibSegJs_glTd1.regs0 LibSegJs_glTd1.regs_out0 KS_glTd1 = true. Proof. vm_compute. reflexivity. Qed.
Definition glTd1_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#48,,1,5X#36=34#36490Y,T,1#36><0T,:v25T,;#5"%pstring.
Lemma glTd1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTd1] fx R M V glTd1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTd1] LibSegJs_glTd1.regs0 LibSegJs_glTd1.kn0 LibSegJs_glTd1.BR LibSegJs_glTd1.PSS LibSegJs_glTd1.NX0 LibSegJs_glTd1.F0 224564 LibSegJs_glTd1.seg_sound_ax fx R M V glTd1_conc_s. Qed.
Definition KS_glTd2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTd2.regs0 LibSegJs_glTd2.regs_out0).
Lemma KS_glTd2_ok : BG.kept_ok 48 LibSegJs_glTd2.regs0 LibSegJs_glTd2.regs_out0 KS_glTd2 = true. Proof. vm_compute. reflexivity. Qed.
Definition glTd2_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#4:v21#4;,,1,5X#36=34#36490Y,T,1#36><0T,:v25T,;#5"%pstring.
Lemma glTd2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTd2] fx R M V glTd2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTd2] LibSegJs_glTd2.regs0 LibSegJs_glTd2.kn0 LibSegJs_glTd2.BR LibSegJs_glTd2.PSS LibSegJs_glTd2.NX0 LibSegJs_glTd2.F0 224564 LibSegJs_glTd2.seg_sound_ax fx R M V glTd2_conc_s. Qed.
Definition KS_glTd3 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTd3.regs0 LibSegJs_glTd3.regs_out0).
Lemma KS_glTd3_ok : BG.kept_ok 48 LibSegJs_glTd3.regs0 LibSegJs_glTd3.regs_out0 KS_glTd3 = true. Proof. vm_compute. reflexivity. Qed.
Definition glTd3_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#4=v21#54,,1,5X#36=34#36490Y,T,1#36><0T,:v25T,;#5"%pstring.
Lemma glTd3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTd3] fx R M V glTd3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTd3] LibSegJs_glTd3.regs0 LibSegJs_glTd3.kn0 LibSegJs_glTd3.BR LibSegJs_glTd3.PSS LibSegJs_glTd3.NX0 LibSegJs_glTd3.F0 224564 LibSegJs_glTd3.seg_sound_ax fx R M V glTd3_conc_s. Qed.
Definition KS_glTd4 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTd4.regs0 LibSegJs_glTd4.regs_out0).
Lemma KS_glTd4_ok : BG.kept_ok 48 LibSegJs_glTd4.regs0 LibSegJs_glTd4.regs_out0 KS_glTd4 = true. Proof. vm_compute. reflexivity. Qed.
Definition glTd4_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#56v21#68,,1,5X#36=34#36490Y,T,1#36><0T,:v25T,;#5"%pstring.
Lemma glTd4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTd4] fx R M V glTd4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTd4] LibSegJs_glTd4.regs0 LibSegJs_glTd4.kn0 LibSegJs_glTd4.BR LibSegJs_glTd4.PSS LibSegJs_glTd4.NX0 LibSegJs_glTd4.F0 224564 LibSegJs_glTd4.seg_sound_ax fx R M V glTd4_conc_s. Qed.
Definition KS_glTd5 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTd5.regs0 LibSegJs_glTd5.regs_out0).
Lemma KS_glTd5_ok : BG.kept_ok 48 LibSegJs_glTd5.regs0 LibSegJs_glTd5.regs_out0 KS_glTd5 = true. Proof. vm_compute. reflexivity. Qed.
Definition glTd5_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#6:v21#6;,,1,5X#36=34#36490Y,T,1#36><0T,:v25T,;#5"%pstring.
Lemma glTd5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTd5] fx R M V glTd5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTd5] LibSegJs_glTd5.regs0 LibSegJs_glTd5.kn0 LibSegJs_glTd5.BR LibSegJs_glTd5.PSS LibSegJs_glTd5.NX0 LibSegJs_glTd5.F0 224564 LibSegJs_glTd5.seg_sound_ax fx R M V glTd5_conc_s. Qed.
Definition KS_glTd6 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glTd6.regs0 LibSegJs_glTd6.regs_out0).
Lemma KS_glTd6_ok : BG.kept_ok 48 LibSegJs_glTd6.regs0 LibSegJs_glTd6.regs_out0 KS_glTd6 = true. Proof. vm_compute. reflexivity. Qed.
Definition glTd6_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#6=v21#??,,1,5X#36=34#36490Y,T,1#36><0T,:v25T,;#5"%pstring.
Lemma glTd6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glTd6] fx R M V glTd6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glTd6] LibSegJs_glTd6.regs0 LibSegJs_glTd6.kn0 LibSegJs_glTd6.BR LibSegJs_glTd6.PSS LibSegJs_glTd6.NX0 LibSegJs_glTd6.F0 224564 LibSegJs_glTd6.seg_sound_ax fx R M V glTd6_conc_s. Qed.
Definition KS_glNi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glNi_c1.regs0 LibSegJs_glNi_c1.regs_out0).
Lemma KS_glNi_ok : BG.kept_ok 48 LibSegJs_glNi_c1.regs0 LibSegJs_glNi_c1.regs_out0 KS_glNi = true. Proof. vm_compute. reflexivity. Qed.
Definition glNi_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#S,12+v24#18S,13#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,5X#36=68#36490Y,T,1#36><0T,:v25T,;#1"%pstring.
Lemma glNi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glNi] fx R M V glNi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glNi] LibSegJs_glNi_c1.regs0 LibSegJs_glNi_c1.kn0 LibSegJs_glNi_c1.BR LibSegJs_glNi_c1.PSS LibSegJs_glNi_c1.NX0 LibSegJs_glNi_c1.F0 224616 LibSegJs_glNi_c1.seg_sound_ax fx R M V glNi_conc_s. Qed.
Definition KS_glNU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glNU.regs0 LibSegJs_glNU.regs_out0).
Lemma KS_glNU_ok : BG.kept_ok 48 LibSegJs_glNU.regs0 LibSegJs_glNU.regs_out0 KS_glNU = true. Proof. vm_compute. reflexivity. Qed.
Definition glNU_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,5X#36>24#36490Y,T,1#36><0T,:v25T,;#1"%pstring.
Lemma glNU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glNU] fx R M V glNU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glNU] LibSegJs_glNU.regs0 LibSegJs_glNU.kn0 LibSegJs_glNU.BR LibSegJs_glNU.PSS LibSegJs_glNU.NX0 LibSegJs_glNU.F0 224804 LibSegJs_glNU.seg_sound_ax fx R M V glNU_conc_s. Qed.
Definition KS_glNI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glNI.regs0 LibSegJs_glNI.regs_out0).
Lemma KS_glNI_ok : BG.kept_ok 48 LibSegJs_glNI.regs0 LibSegJs_glNI.regs_out0 KS_glNI = true. Proof. vm_compute. reflexivity. Qed.
Definition glNI_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#1,,1,5X#36>94#36490Y,T,1#36><0T,:v25T,;#1"%pstring.
Lemma glNI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glNI] fx R M V glNI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glNI] LibSegJs_glNI.regs0 LibSegJs_glNI.kn0 LibSegJs_glNI.BR LibSegJs_glNI.PSS LibSegJs_glNI.NX0 LibSegJs_glNI.F0 224916 LibSegJs_glNI.seg_sound_ax fx R M V glNI_conc_s. Qed.
Definition KS_glNl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glNl_c1.regs0 LibSegJs_glNl_c1.regs_out0).
Lemma KS_glNl_ok : BG.kept_ok 48 LibSegJs_glNl_c1.regs0 LibSegJs_glNl_c1.regs_out0 KS_glNl = true. Proof. vm_compute. reflexivity. Qed.
Definition glNl_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#4B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#3,,1,6X#36>44#36490Y,T,1#36><0T,:v25T,;#1T,13#1"%pstring.
Lemma glNl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glNl] fx R M V glNl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glNl] LibSegJs_glNl_c1.regs0 LibSegJs_glNl_c1.kn0 LibSegJs_glNl_c1.BR LibSegJs_glNl_c1.PSS LibSegJs_glNl_c1.NX0 LibSegJs_glNl_c1.F0 224836 LibSegJs_glNl_c1.seg_sound_ax fx R M V glNl_conc_s. Qed.
Definition KS_glNL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glNL.regs0 LibSegJs_glNL.regs_out0).
Lemma KS_glNL_ok : BG.kept_ok 48 LibSegJs_glNL.regs0 LibSegJs_glNL.regs_out0 KS_glNL = true. Proof. vm_compute. reflexivity. Qed.
Definition glNL_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#8B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#7,,1,5X#36=:0#36490Y,T,1#36><0T,:v25T,;#1"%pstring.
Lemma glNL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glNL] fx R M V glNL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glNL] LibSegJs_glNL.regs0 LibSegJs_glNL.kn0 LibSegJs_glNL.BR LibSegJs_glNL.PSS LibSegJs_glNL.NX0 LibSegJs_glNL.F0 224672 LibSegJs_glNL.seg_sound_ax fx R M V glNL_conc_s. Qed.
Definition KS_glVi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glVi_c1.regs0 LibSegJs_glVi_c1.regs_out0).
Lemma KS_glVi_ok : BG.kept_ok 48 LibSegJs_glVi_c1.regs0 LibSegJs_glVi_c1.regs_out0 KS_glVi = true. Proof. vm_compute. reflexivity. Qed.
Definition glVi_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#1S,12+v24#18S,13#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#1,,1,2X#36=68#36=70Y,"%pstring.
Lemma glVi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glVi] fx R M V glVi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glVi] LibSegJs_glVi_c1.regs0 LibSegJs_glVi_c1.kn0 LibSegJs_glVi_c1.BR LibSegJs_glVi_c1.PSS LibSegJs_glVi_c1.NX0 LibSegJs_glVi_c1.F0 224616 LibSegJs_glVi_c1.seg_sound_ax fx R M V glVi_conc_s. Qed.
Definition KS_glVU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glVU.regs0 LibSegJs_glVU.regs_out0).
Lemma KS_glVU_ok : BG.kept_ok 48 LibSegJs_glVU.regs0 LibSegJs_glVU.regs_out0 KS_glVU = true. Proof. vm_compute. reflexivity. Qed.
Definition glVU_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:#1S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<Ja_v2#38#1,,1,8X#36>24#36>>0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<"%pstring.
Lemma glVU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glVU] fx R M V glVU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glVU] LibSegJs_glVU.regs0 LibSegJs_glVU.kn0 LibSegJs_glVU.BR LibSegJs_glVU.PSS LibSegJs_glVU.NX0 LibSegJs_glVU.F0 224804 LibSegJs_glVU.seg_sound_ax fx R M V glVU_conc_s. Qed.
Definition KS_glVI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glVI.regs0 LibSegJs_glVI.regs_out0).
Lemma KS_glVI_ok : BG.kept_ok 48 LibSegJs_glVI.regs0 LibSegJs_glVI.regs_out0 KS_glVI = true. Proof. vm_compute. reflexivity. Qed.
Definition glVI_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#2S,12+v24#18S,13#2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#2,,1,2X#36>94#36>:8Y,"%pstring.
Lemma glVI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glVI] fx R M V glVI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glVI] LibSegJs_glVI.regs0 LibSegJs_glVI.kn0 LibSegJs_glVI.BR LibSegJs_glVI.PSS LibSegJs_glVI.NX0 LibSegJs_glVI.F0 224916 LibSegJs_glVI.seg_sound_ax fx R M V glVI_conc_s. Qed.
Definition KS_glVl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glVl_c1.regs0 LibSegJs_glVl_c1.regs_out0).
Lemma KS_glVl_ok : BG.kept_ok 48 LibSegJs_glVl_c1.regs0 LibSegJs_glVl_c1.regs_out0 KS_glVl = true. Proof. vm_compute. reflexivity. Qed.
Definition glVl_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#4S,12+v24#18S,13#4B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#4,,1,2X#36>44#36>78Y,"%pstring.
Lemma glVl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glVl] fx R M V glVl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glVl] LibSegJs_glVl_c1.regs0 LibSegJs_glVl_c1.kn0 LibSegJs_glVl_c1.BR LibSegJs_glVl_c1.PSS LibSegJs_glVl_c1.NX0 LibSegJs_glVl_c1.F0 224836 LibSegJs_glVl_c1.seg_sound_ax fx R M V glVl_conc_s. Qed.
Definition KS_glVL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glVL.regs0 LibSegJs_glVL.regs_out0).
Lemma KS_glVL_ok : BG.kept_ok 48 LibSegJs_glVL.regs0 LibSegJs_glVL.regs_out0 KS_glVL = true. Proof. vm_compute. reflexivity. Qed.
Definition glVL_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#8S,12+v24#18S,13#8B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#8,,1,2X#36=:0#36>0<Y,"%pstring.
Lemma glVL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glVL] fx R M V glVL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glVL] LibSegJs_glVL.regs0 LibSegJs_glVL.kn0 LibSegJs_glVL.BR LibSegJs_glVL.PSS LibSegJs_glVL.NX0 LibSegJs_glVL.F0 224672 LibSegJs_glVL.seg_sound_ax fx R M V glVL_conc_s. Qed.
Definition KS_glSi_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSi_c1.regs0 LibSegJs_glSi_c1.regs_out0).
Lemma KS_glSi_0_ok : BG.kept_ok 48 LibSegJs_glSi_c1.regs0 LibSegJs_glSi_c1.regs_out0 KS_glSi_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_glSi_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSi_c1.regs0 LibSegJs_glSi_c1.regs_out1).
Lemma KS_glSi_1_ok : BG.kept_ok 48 LibSegJs_glSi_c1.regs0 LibSegJs_glSi_c1.regs_out1 KS_glSi_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition glSi_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#36=70#36>>0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,6X#36=70#36490Y,1T,1#36><0T,:v25T,;#4T,13#4"%pstring.
Lemma glSi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glSi_0; KS_glSi_1] fx R M V glSi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glSi_0; KS_glSi_1] LibSegJs_glSi_c1.regs0 LibSegJs_glSi_c1.kn0 LibSegJs_glSi_c1.BR LibSegJs_glSi_c1.PSS LibSegJs_glSi_c1.NX0 LibSegJs_glSi_c1.F0 224624 LibSegJs_glSi_c1.seg_sound_ax fx R M V glSi_conc_s. Qed.
Definition KS_glSI_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSI.regs0 LibSegJs_glSI.regs_out0).
Lemma KS_glSI_0_ok : BG.kept_ok 48 LibSegJs_glSI.regs0 LibSegJs_glSI.regs_out0 KS_glSI_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_glSI_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSI.regs0 LibSegJs_glSI.regs_out1).
Lemma KS_glSI_1_ok : BG.kept_ok 48 LibSegJs_glSI.regs0 LibSegJs_glSI.regs_out1 KS_glSI_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition glSI_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#36>:8#36>>0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,5X#36>:8#36490Y,1T,1#36><0T,:v25T,;#4"%pstring.
Lemma glSI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glSI_0; KS_glSI_1] fx R M V glSI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glSI_0; KS_glSI_1] LibSegJs_glSI.regs0 LibSegJs_glSI.kn0 LibSegJs_glSI.BR LibSegJs_glSI.PSS LibSegJs_glSI.NX0 LibSegJs_glSI.F0 224936 LibSegJs_glSI.seg_sound_ax fx R M V glSI_conc_s. Qed.
Definition KS_glSl_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSl_c1.regs0 LibSegJs_glSl_c1.regs_out0).
Lemma KS_glSl_0_ok : BG.kept_ok 48 LibSegJs_glSl_c1.regs0 LibSegJs_glSl_c1.regs_out0 KS_glSl_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_glSl_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSl_c1.regs0 LibSegJs_glSl_c1.regs_out1).
Lemma KS_glSl_1_ok : BG.kept_ok 48 LibSegJs_glSl_c1.regs0 LibSegJs_glSl_c1.regs_out1 KS_glSl_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition glSl_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#4B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#36>78#36>>0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,5X#36>78#36490Y,1T,1#36><0T,:v25T,;#4"%pstring.
Lemma glSl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glSl_0; KS_glSl_1] fx R M V glSl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glSl_0; KS_glSl_1] LibSegJs_glSl_c1.regs0 LibSegJs_glSl_c1.kn0 LibSegJs_glSl_c1.BR LibSegJs_glSl_c1.PSS LibSegJs_glSl_c1.NX0 LibSegJs_glSl_c1.F0 224888 LibSegJs_glSl_c1.seg_sound_ax fx R M V glSl_conc_s. Qed.
Definition KS_glSL_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSL.regs0 LibSegJs_glSL.regs_out0).
Lemma KS_glSL_0_ok : BG.kept_ok 48 LibSegJs_glSL.regs0 LibSegJs_glSL.regs_out0 KS_glSL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_glSL_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glSL.regs0 LibSegJs_glSL.regs_out1).
Lemma KS_glSL_1_ok : BG.kept_ok 48 LibSegJs_glSL.regs0 LibSegJs_glSL.regs_out1 KS_glSL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition glSL_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#8B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#36>0<#36>>0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,5X#36>0<#36490Y,1T,1#36><0T,:v25T,;#4"%pstring.
Lemma glSL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glSL_0; KS_glSL_1] fx R M V glSL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glSL_0; KS_glSL_1] LibSegJs_glSL.regs0 LibSegJs_glSL.kn0 LibSegJs_glSL.BR LibSegJs_glSL.PSS LibSegJs_glSL.NX0 LibSegJs_glSL.F0 224780 LibSegJs_glSL.seg_sound_ax fx R M V glSL_conc_s. Qed.
Definition KS_glZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_glZ.regs0 LibSegJs_glZ.regs_out0).
Lemma KS_glZ_ok : BG.kept_ok 48 LibSegJs_glZ.regs0 LibSegJs_glZ.regs_out0 KS_glZ = true. Proof. vm_compute. reflexivity. Qed.
Definition glZ_conc_s := ",1;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<I+v24#8#1,1+v24#8#1,1,:X#36><0#36>>0Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,12v2;T,13v2<Nb+v24#8#"%pstring.
Lemma glZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_glZ] fx R M V glZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_glZ] LibSegJs_glZ.regs0 LibSegJs_glZ.kn0 LibSegJs_glZ.BR LibSegJs_glZ.PSS LibSegJs_glZ.NX0 LibSegJs_glZ.F0 224960 LibSegJs_glZ.seg_sound_ax fx R M V glZ_conc_s. Qed.
End PMSGLP.
