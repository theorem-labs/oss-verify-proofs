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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uglA LibSegJu_uglE0 LibSegJu_uglB LibSegJu_uglTi_c1 LibSegJu_uglTU LibSegJu_uglTI LibSegJu_uglTl_c1 LibSegJu_uglTL LibSegJu_uglTd1 LibSegJu_uglTd2 LibSegJu_uglTd3 LibSegJu_uglTd4 LibSegJu_uglTd5 LibSegJu_uglTd6 LibSegJu_uglNi_c1 LibSegJu_uglNU LibSegJu_uglNI LibSegJu_uglNl_c1 LibSegJu_uglNL LibSegJu_uglVi_c1 LibSegJu_uglVU LibSegJu_uglVI LibSegJu_uglVl_c1 LibSegJu_uglVL LibSegJu_uglSi_c1 LibSegJu_uglSI LibSegJu_uglSl_c1 LibSegJu_uglSL LibSegJu_uglZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUGLP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uglA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglA.regs0 LibSegJu_uglA.regs_out0).
Lemma KS_uglA_ok : BG.kept_ok 48 LibSegJu_uglA.regs0 LibSegJu_uglA.regs_out0 KS_uglA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uglA_conc_s := ",?A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,1_v2#40#40,1,?X#37::4#374;8Y,T,1#37:=8T,2_v2#40T,8v24T,9v25T,:+v24#18T,;_v2#29T,<#1T,12+v24#18Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uglA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglA] fx R M V uglA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglA] LibSegJu_uglA.regs0 LibSegJu_uglA.kn0 LibSegJu_uglA.BR LibSegJu_uglA.PSS LibSegJu_uglA.NX0 LibSegJu_uglA.F0 228004 LibSegJu_uglA.seg_sound_ax fx R M V uglA_conc_s. Qed.
Definition KS_uglE0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglE0.regs0 LibSegJu_uglE0.regs_out0).
Lemma KS_uglE0_ok : BG.kept_ok 48 LibSegJu_uglE0.regs0 LibSegJu_uglE0.regs_out0 KS_uglE0 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglE0_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,5X#37:=8#370:<Y,T,1#37<6<T,:v25T,;#1"%pstring.
Lemma uglE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglE0] fx R M V uglE0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglE0] LibSegJu_uglE0.regs0 LibSegJu_uglE0.kn0 LibSegJu_uglE0.BR LibSegJu_uglE0.PSS LibSegJu_uglE0.NX0 LibSegJu_uglE0.F0 228056 LibSegJu_uglE0.seg_sound_ax fx R M V uglE0_conc_s. Qed.
Definition KS_uglB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglB.regs0 LibSegJu_uglB.regs_out0).
Lemma KS_uglB_ok : BG.kept_ok 48 LibSegJu_uglB.regs0 LibSegJu_uglB.regs_out0 KS_uglB = true. Proof. vm_compute. reflexivity. Qed.
Definition uglB_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#1S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,2X#37:=8#37:=<Y,"%pstring.
Lemma uglB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglB] fx R M V uglB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglB] LibSegJu_uglB.regs0 LibSegJu_uglB.kn0 LibSegJu_uglB.BR LibSegJu_uglB.PSS LibSegJu_uglB.NX0 LibSegJu_uglB.F0 228056 LibSegJu_uglB.seg_sound_ax fx R M V uglB_conc_s. Qed.
Definition KS_uglTi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTi_c1.regs0 LibSegJu_uglTi_c1.regs_out0).
Lemma KS_uglTi_ok : BG.kept_ok 48 LibSegJu_uglTi_c1.regs0 LibSegJu_uglTi_c1.regs_out0 KS_uglTi = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTi_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#69S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#37:>0#374;8Y,T,1#37;14T,:+v24#18T,;_v2#38T,<#1T,13#1"%pstring.
Lemma uglTi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTi] fx R M V uglTi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTi] LibSegJu_uglTi_c1.regs0 LibSegJu_uglTi_c1.kn0 LibSegJu_uglTi_c1.BR LibSegJu_uglTi_c1.PSS LibSegJu_uglTi_c1.NX0 LibSegJu_uglTi_c1.F0 228064 LibSegJu_uglTi_c1.seg_sound_ax fx R M V uglTi_conc_s. Qed.
Definition KS_uglTU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTU.regs0 LibSegJu_uglTU.regs_out0).
Lemma KS_uglTU_ok : BG.kept_ok 48 LibSegJu_uglTU.regs0 LibSegJu_uglTU.regs_out0 KS_uglTU = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTU_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#55S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,6X#37:>0#374;8Y,T,1#37;=0T,:+v24#18T,;_v2#38T,<#1"%pstring.
Lemma uglTU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTU] fx R M V uglTU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTU] LibSegJu_uglTU.regs0 LibSegJu_uglTU.kn0 LibSegJu_uglTU.BR LibSegJu_uglTU.PSS LibSegJu_uglTU.NX0 LibSegJu_uglTU.F0 228064 LibSegJu_uglTU.seg_sound_ax fx R M V uglTU_conc_s. Qed.
Definition KS_uglTI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTI.regs0 LibSegJu_uglTI.regs_out0).
Lemma KS_uglTI_ok : BG.kept_ok 48 LibSegJu_uglTI.regs0 LibSegJu_uglTI.regs_out0 KS_uglTI = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTI_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#49S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#37:>0#374;8Y,T,1#37<40T,:+v24#18T,;_v2#38T,<#2T,13#2"%pstring.
Lemma uglTI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTI] fx R M V uglTI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTI] LibSegJu_uglTI.regs0 LibSegJu_uglTI.kn0 LibSegJu_uglTI.BR LibSegJu_uglTI.PSS LibSegJu_uglTI.NX0 LibSegJu_uglTI.F0 228064 LibSegJu_uglTI.seg_sound_ax fx R M V uglTI_conc_s. Qed.
Definition KS_uglTl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTl_c1.regs0 LibSegJu_uglTl_c1.regs_out0).
Lemma KS_uglTl_ok : BG.kept_ok 48 LibSegJu_uglTl_c1.regs0 LibSegJu_uglTl_c1.regs_out0 KS_uglTl = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTl_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#6<S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#37:>0#374;8Y,T,1#37;?0T,:+v24#18T,;_v2#38T,<#4T,13#4"%pstring.
Lemma uglTl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTl] fx R M V uglTl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTl] LibSegJu_uglTl_c1.regs0 LibSegJu_uglTl_c1.kn0 LibSegJu_uglTl_c1.BR LibSegJu_uglTl_c1.PSS LibSegJu_uglTl_c1.NX0 LibSegJu_uglTl_c1.F0 228064 LibSegJu_uglTl_c1.seg_sound_ax fx R M V uglTl_conc_s. Qed.
Definition KS_uglTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTL.regs0 LibSegJu_uglTL.regs_out0).
Lemma KS_uglTL_ok : BG.kept_ok 48 LibSegJu_uglTL.regs0 LibSegJu_uglTL.regs_out0 KS_uglTL = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTL_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#4<S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,7X#37:>0#374;8Y,T,1#37;4<T,:+v24#18T,;_v2#38T,<#8T,13#8"%pstring.
Lemma uglTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTL] fx R M V uglTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTL] LibSegJu_uglTL.regs0 LibSegJu_uglTL.kn0 LibSegJu_uglTL.BR LibSegJu_uglTL.PSS LibSegJu_uglTL.NX0 LibSegJu_uglTL.F0 228064 LibSegJu_uglTL.seg_sound_ax fx R M V uglTL_conc_s. Qed.
Definition KS_uglTd1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTd1.regs0 LibSegJu_uglTd1.regs_out0).
Lemma KS_uglTd1_ok : BG.kept_ok 48 LibSegJu_uglTd1.regs0 LibSegJu_uglTd1.regs_out0 KS_uglTd1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTd1_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#48,,1,5X#37:>0#370:<Y,T,1#37<6<T,:v25T,;#5"%pstring.
Lemma uglTd1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTd1] fx R M V uglTd1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTd1] LibSegJu_uglTd1.regs0 LibSegJu_uglTd1.kn0 LibSegJu_uglTd1.BR LibSegJu_uglTd1.PSS LibSegJu_uglTd1.NX0 LibSegJu_uglTd1.F0 228064 LibSegJu_uglTd1.seg_sound_ax fx R M V uglTd1_conc_s. Qed.
Definition KS_uglTd2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTd2.regs0 LibSegJu_uglTd2.regs_out0).
Lemma KS_uglTd2_ok : BG.kept_ok 48 LibSegJu_uglTd2.regs0 LibSegJu_uglTd2.regs_out0 KS_uglTd2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTd2_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#4:v21#4;,,1,5X#37:>0#370:<Y,T,1#37<6<T,:v25T,;#5"%pstring.
Lemma uglTd2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTd2] fx R M V uglTd2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTd2] LibSegJu_uglTd2.regs0 LibSegJu_uglTd2.kn0 LibSegJu_uglTd2.BR LibSegJu_uglTd2.PSS LibSegJu_uglTd2.NX0 LibSegJu_uglTd2.F0 228064 LibSegJu_uglTd2.seg_sound_ax fx R M V uglTd2_conc_s. Qed.
Definition KS_uglTd3 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTd3.regs0 LibSegJu_uglTd3.regs_out0).
Lemma KS_uglTd3_ok : BG.kept_ok 48 LibSegJu_uglTd3.regs0 LibSegJu_uglTd3.regs_out0 KS_uglTd3 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTd3_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#4=v21#54,,1,5X#37:>0#370:<Y,T,1#37<6<T,:v25T,;#5"%pstring.
Lemma uglTd3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTd3] fx R M V uglTd3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTd3] LibSegJu_uglTd3.regs0 LibSegJu_uglTd3.kn0 LibSegJu_uglTd3.BR LibSegJu_uglTd3.PSS LibSegJu_uglTd3.NX0 LibSegJu_uglTd3.F0 228064 LibSegJu_uglTd3.seg_sound_ax fx R M V uglTd3_conc_s. Qed.
Definition KS_uglTd4 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTd4.regs0 LibSegJu_uglTd4.regs_out0).
Lemma KS_uglTd4_ok : BG.kept_ok 48 LibSegJu_uglTd4.regs0 LibSegJu_uglTd4.regs_out0 KS_uglTd4 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTd4_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#56v21#68,,1,5X#37:>0#370:<Y,T,1#37<6<T,:v25T,;#5"%pstring.
Lemma uglTd4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTd4] fx R M V uglTd4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTd4] LibSegJu_uglTd4.regs0 LibSegJu_uglTd4.kn0 LibSegJu_uglTd4.BR LibSegJu_uglTd4.PSS LibSegJu_uglTd4.NX0 LibSegJu_uglTd4.F0 228064 LibSegJu_uglTd4.seg_sound_ax fx R M V uglTd4_conc_s. Qed.
Definition KS_uglTd5 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTd5.regs0 LibSegJu_uglTd5.regs_out0).
Lemma KS_uglTd5_ok : BG.kept_ok 48 LibSegJu_uglTd5.regs0 LibSegJu_uglTd5.regs_out0 KS_uglTd5 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTd5_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#6:v21#6;,,1,5X#37:>0#370:<Y,T,1#37<6<T,:v25T,;#5"%pstring.
Lemma uglTd5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTd5] fx R M V uglTd5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTd5] LibSegJu_uglTd5.regs0 LibSegJu_uglTd5.kn0 LibSegJu_uglTd5.BR LibSegJu_uglTd5.PSS LibSegJu_uglTd5.NX0 LibSegJu_uglTd5.F0 228064 LibSegJu_uglTd5.seg_sound_ax fx R M V uglTd5_conc_s. Qed.
Definition KS_uglTd6 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglTd6.regs0 LibSegJu_uglTd6.regs_out0).
Lemma KS_uglTd6_ok : BG.kept_ok 48 LibSegJu_uglTd6.regs0 LibSegJu_uglTd6.regs_out0 KS_uglTd6 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglTd6_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#6=v21#??,,1,5X#37:>0#370:<Y,T,1#37<6<T,:v25T,;#5"%pstring.
Lemma uglTd6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglTd6] fx R M V uglTd6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglTd6] LibSegJu_uglTd6.regs0 LibSegJu_uglTd6.kn0 LibSegJu_uglTd6.BR LibSegJu_uglTd6.PSS LibSegJu_uglTd6.NX0 LibSegJu_uglTd6.F0 228064 LibSegJu_uglTd6.seg_sound_ax fx R M V uglTd6_conc_s. Qed.
Definition KS_uglNi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglNi_c1.regs0 LibSegJu_uglNi_c1.regs_out0).
Lemma KS_uglNi_ok : BG.kept_ok 48 LibSegJu_uglNi_c1.regs0 LibSegJu_uglNi_c1.regs_out0 KS_uglNi = true. Proof. vm_compute. reflexivity. Qed.
Definition uglNi_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#S,12+v24#18S,13#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,5X#37;14#370:<Y,T,1#37<6<T,:v25T,;#1"%pstring.
Lemma uglNi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglNi] fx R M V uglNi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglNi] LibSegJu_uglNi_c1.regs0 LibSegJu_uglNi_c1.kn0 LibSegJu_uglNi_c1.BR LibSegJu_uglNi_c1.PSS LibSegJu_uglNi_c1.NX0 LibSegJu_uglNi_c1.F0 228116 LibSegJu_uglNi_c1.seg_sound_ax fx R M V uglNi_conc_s. Qed.
Definition KS_uglNU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglNU.regs0 LibSegJu_uglNU.regs_out0).
Lemma KS_uglNU_ok : BG.kept_ok 48 LibSegJu_uglNU.regs0 LibSegJu_uglNU.regs_out0 KS_uglNU = true. Proof. vm_compute. reflexivity. Qed.
Definition uglNU_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10,,1,5X#37;=0#370:<Y,T,1#37<6<T,:v25T,;#1"%pstring.
Lemma uglNU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglNU] fx R M V uglNU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglNU] LibSegJu_uglNU.regs0 LibSegJu_uglNU.kn0 LibSegJu_uglNU.BR LibSegJu_uglNU.PSS LibSegJu_uglNU.NX0 LibSegJu_uglNU.F0 228304 LibSegJu_uglNU.seg_sound_ax fx R M V uglNU_conc_s. Qed.
Definition KS_uglNI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglNI.regs0 LibSegJu_uglNI.regs_out0).
Lemma KS_uglNI_ok : BG.kept_ok 48 LibSegJu_uglNI.regs0 LibSegJu_uglNI.regs_out0 KS_uglNI = true. Proof. vm_compute. reflexivity. Qed.
Definition uglNI_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#1,,1,5X#37<40#370:<Y,T,1#37<6<T,:v25T,;#1"%pstring.
Lemma uglNI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglNI] fx R M V uglNI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglNI] LibSegJu_uglNI.regs0 LibSegJu_uglNI.kn0 LibSegJu_uglNI.BR LibSegJu_uglNI.PSS LibSegJu_uglNI.NX0 LibSegJu_uglNI.F0 228416 LibSegJu_uglNI.seg_sound_ax fx R M V uglNI_conc_s. Qed.
Definition KS_uglNl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglNl_c1.regs0 LibSegJu_uglNl_c1.regs_out0).
Lemma KS_uglNl_ok : BG.kept_ok 48 LibSegJu_uglNl_c1.regs0 LibSegJu_uglNl_c1.regs_out0 KS_uglNl = true. Proof. vm_compute. reflexivity. Qed.
Definition uglNl_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#4B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#3,,1,6X#37;?0#370:<Y,T,1#37<6<T,:v25T,;#1T,13#1"%pstring.
Lemma uglNl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglNl] fx R M V uglNl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglNl] LibSegJu_uglNl_c1.regs0 LibSegJu_uglNl_c1.kn0 LibSegJu_uglNl_c1.BR LibSegJu_uglNl_c1.PSS LibSegJu_uglNl_c1.NX0 LibSegJu_uglNl_c1.F0 228336 LibSegJu_uglNl_c1.seg_sound_ax fx R M V uglNl_conc_s. Qed.
Definition KS_uglNL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglNL.regs0 LibSegJu_uglNL.regs_out0).
Lemma KS_uglNL_ok : BG.kept_ok 48 LibSegJu_uglNL.regs0 LibSegJu_uglNL.regs_out0 KS_uglNL = true. Proof. vm_compute. reflexivity. Qed.
Definition uglNL_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#8B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10B#v21#7,,1,5X#37;4<#370:<Y,T,1#37<6<T,:v25T,;#1"%pstring.
Lemma uglNL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglNL] fx R M V uglNL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglNL] LibSegJu_uglNL.regs0 LibSegJu_uglNL.kn0 LibSegJu_uglNL.BR LibSegJu_uglNL.PSS LibSegJu_uglNL.NX0 LibSegJu_uglNL.F0 228172 LibSegJu_uglNL.seg_sound_ax fx R M V uglNL_conc_s. Qed.
Definition KS_uglVi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglVi_c1.regs0 LibSegJu_uglVi_c1.regs_out0).
Lemma KS_uglVi_ok : BG.kept_ok 48 LibSegJu_uglVi_c1.regs0 LibSegJu_uglVi_c1.regs_out0 KS_uglVi = true. Proof. vm_compute. reflexivity. Qed.
Definition uglVi_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#1S,12+v24#18S,13#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#1,,1,2X#37;14#37;1<Y,"%pstring.
Lemma uglVi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglVi] fx R M V uglVi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglVi] LibSegJu_uglVi_c1.regs0 LibSegJu_uglVi_c1.kn0 LibSegJu_uglVi_c1.BR LibSegJu_uglVi_c1.PSS LibSegJu_uglVi_c1.NX0 LibSegJu_uglVi_c1.F0 228116 LibSegJu_uglVi_c1.seg_sound_ax fx R M V uglVi_conc_s. Qed.
Definition KS_uglVU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglVU.regs0 LibSegJu_uglVU.regs_out0).
Lemma KS_uglVU_ok : BG.kept_ok 48 LibSegJu_uglVU.regs0 LibSegJu_uglVU.regs_out0 KS_uglVU = true. Proof. vm_compute. reflexivity. Qed.
Definition uglVU_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:#1S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<Ja_v2#38#1,,1,8X#37;=0#37<8<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<"%pstring.
Lemma uglVU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglVU] fx R M V uglVU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglVU] LibSegJu_uglVU.regs0 LibSegJu_uglVU.kn0 LibSegJu_uglVU.BR LibSegJu_uglVU.PSS LibSegJu_uglVU.NX0 LibSegJu_uglVU.F0 228304 LibSegJu_uglVU.seg_sound_ax fx R M V uglVU_conc_s. Qed.
Definition KS_uglVI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglVI.regs0 LibSegJu_uglVI.regs_out0).
Lemma KS_uglVI_ok : BG.kept_ok 48 LibSegJu_uglVI.regs0 LibSegJu_uglVI.regs_out0 KS_uglVI = true. Proof. vm_compute. reflexivity. Qed.
Definition uglVI_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#2S,12+v24#18S,13#2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#2,,1,2X#37<40#37<54Y,"%pstring.
Lemma uglVI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglVI] fx R M V uglVI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglVI] LibSegJu_uglVI.regs0 LibSegJu_uglVI.kn0 LibSegJu_uglVI.BR LibSegJu_uglVI.PSS LibSegJu_uglVI.NX0 LibSegJu_uglVI.F0 228416 LibSegJu_uglVI.seg_sound_ax fx R M V uglVI_conc_s. Qed.
Definition KS_uglVl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglVl_c1.regs0 LibSegJu_uglVl_c1.regs_out0).
Lemma KS_uglVl_ok : BG.kept_ok 48 LibSegJu_uglVl_c1.regs0 LibSegJu_uglVl_c1.regs_out0 KS_uglVl = true. Proof. vm_compute. reflexivity. Qed.
Definition uglVl_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#4S,12+v24#18S,13#4B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#4,,1,2X#37;?0#37<24Y,"%pstring.
Lemma uglVl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglVl] fx R M V uglVl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglVl] LibSegJu_uglVl_c1.regs0 LibSegJu_uglVl_c1.kn0 LibSegJu_uglVl_c1.BR LibSegJu_uglVl_c1.PSS LibSegJu_uglVl_c1.NX0 LibSegJu_uglVl_c1.F0 228336 LibSegJu_uglVl_c1.seg_sound_ax fx R M V uglVl_conc_s. Qed.
Definition KS_uglVL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglVL.regs0 LibSegJu_uglVL.regs_out0).
Lemma KS_uglVL_ok : BG.kept_ok 48 LibSegJu_uglVL.regs0 LibSegJu_uglVL.regs_out0 KS_uglVL = true. Proof. vm_compute. reflexivity. Qed.
Definition uglVL_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v24S,9v25S,:#8S,12+v24#18S,13#8B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10Ja_v2#38#8,,1,2X#37;4<#37;;8Y,"%pstring.
Lemma uglVL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglVL] fx R M V uglVL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglVL] LibSegJu_uglVL.regs0 LibSegJu_uglVL.kn0 LibSegJu_uglVL.BR LibSegJu_uglVL.PSS LibSegJu_uglVL.NX0 LibSegJu_uglVL.F0 228172 LibSegJu_uglVL.seg_sound_ax fx R M V uglVL_conc_s. Qed.
Definition KS_uglSi_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSi_c1.regs0 LibSegJu_uglSi_c1.regs_out0).
Lemma KS_uglSi_0_ok : BG.kept_ok 48 LibSegJu_uglSi_c1.regs0 LibSegJu_uglSi_c1.regs_out0 KS_uglSi_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uglSi_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSi_c1.regs0 LibSegJu_uglSi_c1.regs_out1).
Lemma KS_uglSi_1_ok : BG.kept_ok 48 LibSegJu_uglSi_c1.regs0 LibSegJu_uglSi_c1.regs_out1 KS_uglSi_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglSi_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#37;1<#37<8<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,6X#37;1<#370:<Y,1T,1#37<6<T,:v25T,;#4T,13#4"%pstring.
Lemma uglSi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglSi_0; KS_uglSi_1] fx R M V uglSi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglSi_0; KS_uglSi_1] LibSegJu_uglSi_c1.regs0 LibSegJu_uglSi_c1.kn0 LibSegJu_uglSi_c1.BR LibSegJu_uglSi_c1.PSS LibSegJu_uglSi_c1.NX0 LibSegJu_uglSi_c1.F0 228124 LibSegJu_uglSi_c1.seg_sound_ax fx R M V uglSi_conc_s. Qed.
Definition KS_uglSI_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSI.regs0 LibSegJu_uglSI.regs_out0).
Lemma KS_uglSI_0_ok : BG.kept_ok 48 LibSegJu_uglSI.regs0 LibSegJu_uglSI.regs_out0 KS_uglSI_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uglSI_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSI.regs0 LibSegJu_uglSI.regs_out1).
Lemma KS_uglSI_1_ok : BG.kept_ok 48 LibSegJu_uglSI.regs0 LibSegJu_uglSI.regs_out1 KS_uglSI_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglSI_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#37<54#37<8<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,5X#37<54#370:<Y,1T,1#37<6<T,:v25T,;#4"%pstring.
Lemma uglSI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglSI_0; KS_uglSI_1] fx R M V uglSI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglSI_0; KS_uglSI_1] LibSegJu_uglSI.regs0 LibSegJu_uglSI.kn0 LibSegJu_uglSI.BR LibSegJu_uglSI.PSS LibSegJu_uglSI.NX0 LibSegJu_uglSI.F0 228436 LibSegJu_uglSI.seg_sound_ax fx R M V uglSI_conc_s. Qed.
Definition KS_uglSl_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSl_c1.regs0 LibSegJu_uglSl_c1.regs_out0).
Lemma KS_uglSl_0_ok : BG.kept_ok 48 LibSegJu_uglSl_c1.regs0 LibSegJu_uglSl_c1.regs_out0 KS_uglSl_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uglSl_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSl_c1.regs0 LibSegJu_uglSl_c1.regs_out1).
Lemma KS_uglSl_1_ok : BG.kept_ok 48 LibSegJu_uglSl_c1.regs0 LibSegJu_uglSl_c1.regs_out1 KS_uglSl_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglSl_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#4B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#37<24#37<8<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,5X#37<24#370:<Y,1T,1#37<6<T,:v25T,;#4"%pstring.
Lemma uglSl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglSl_0; KS_uglSl_1] fx R M V uglSl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglSl_0; KS_uglSl_1] LibSegJu_uglSl_c1.regs0 LibSegJu_uglSl_c1.kn0 LibSegJu_uglSl_c1.BR LibSegJu_uglSl_c1.PSS LibSegJu_uglSl_c1.NX0 LibSegJu_uglSl_c1.F0 228388 LibSegJu_uglSl_c1.seg_sound_ax fx R M V uglSl_conc_s. Qed.
Definition KS_uglSL_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSL.regs0 LibSegJu_uglSL.regs_out0).
Lemma KS_uglSL_0_ok : BG.kept_ok 48 LibSegJu_uglSL.regs0 LibSegJu_uglSL.regs_out0 KS_uglSL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uglSL_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglSL.regs0 LibSegJu_uglSL.regs_out1).
Lemma KS_uglSL_1_ok : BG.kept_ok 48 LibSegJu_uglSL.regs0 LibSegJu_uglSL.regs_out1 KS_uglSL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uglSL_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,:v21S,12+v24#18S,13#8B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,2,8X#37;;8#37<8<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<,5X#37;;8#370:<Y,1T,1#37<6<T,:v25T,;#4"%pstring.
Lemma uglSL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglSL_0; KS_uglSL_1] fx R M V uglSL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglSL_0; KS_uglSL_1] LibSegJu_uglSL.regs0 LibSegJu_uglSL.kn0 LibSegJu_uglSL.BR LibSegJu_uglSL.PSS LibSegJu_uglSL.NX0 LibSegJu_uglSL.F0 228280 LibSegJu_uglSL.seg_sound_ax fx R M V uglSL_conc_s. Qed.
Definition KS_uglZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uglZ.regs0 LibSegJu_uglZ.regs_out0).
Lemma KS_uglZ_ok : BG.kept_ok 48 LibSegJu_uglZ.regs0 LibSegJu_uglZ.regs_out0 KS_uglZ = true. Proof. vm_compute. reflexivity. Qed.
Definition uglZ_conc_s := ",1;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8v24S,9v25S,12+v24#18B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v25#7??????????0Hv25#8P_v2#40#40v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<I+v24#8#1,1+v24#8#1,1,:X#37<6<#37<8<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,12v2;T,13v2<Nb+v24#8#"%pstring.
Lemma uglZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uglZ] fx R M V uglZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uglZ] LibSegJu_uglZ.regs0 LibSegJu_uglZ.kn0 LibSegJu_uglZ.BR LibSegJu_uglZ.PSS LibSegJu_uglZ.NX0 LibSegJu_uglZ.F0 228460 LibSegJu_uglZ.seg_sound_ax fx R M V uglZ_conc_s. Qed.
End PMUGLP.
