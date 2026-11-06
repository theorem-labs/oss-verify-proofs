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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rtA0 LibSegJs_rtA2 LibSegJs_rtE0 LibSegJs_rtB LibSegJs_rtC LibSegJs_rtD LibSegJs_rtZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRTVP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_rtA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtA0.regs0 LibSegJs_rtA0.regs_out0).
Lemma KS_rtA0_ok : BG.kept_ok 48 LibSegJs_rtA0.regs0 LibSegJs_rtA0.regs_out0 KS_rtA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rtA0_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;60=0La+v24#108v2=Lav2=#;2:98Ma+v2=#98#Pv24#180v2=#110,1_v2#30#30,1,>X#35>30#36830Y,T,1#35>7<T,2_v2#30T,8v24T,9v26T,:+v24#18T,;_v2#21T,<#1T,12v25Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rtA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtA0] fx R M V rtA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtA0] LibSegJs_rtA0.regs0 LibSegJs_rtA0.kn0 LibSegJs_rtA0.BR LibSegJs_rtA0.PSS LibSegJs_rtA0.NX0 LibSegJs_rtA0.F0 220720 LibSegJs_rtA0.seg_sound_ax fx R M V rtA0_conc_s. Qed.
Definition KS_rtA2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtA2.regs0 LibSegJs_rtA2.regs_out0).
Lemma KS_rtA2_ok : BG.kept_ok 48 LibSegJs_rtA2.regs0 LibSegJs_rtA2.regs_out0 KS_rtA2 = true. Proof. vm_compute. reflexivity. Qed.
Definition rtA2_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;60=0La+v24#108v2=Lav2=#;2:98Ma+v2=#98#2Pv24#180v2=#110,1_v2#30#30,1,>X#35>30#36830Y,T,1#35>7<T,2_v2#30T,8v24T,9v26T,:+v24#18T,;_v2#21T,<#1T,12v25Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rtA2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtA2] fx R M V rtA2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtA2] LibSegJs_rtA2.regs0 LibSegJs_rtA2.kn0 LibSegJs_rtA2.BR LibSegJs_rtA2.PSS LibSegJs_rtA2.NX0 LibSegJs_rtA2.F0 220720 LibSegJs_rtA2.seg_sound_ax fx R M V rtA2_conc_s. Qed.
Definition KS_rtE0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtE0.regs0 LibSegJs_rtE0.regs_out0).
Lemma KS_rtE0_ok : BG.kept_ok 48 LibSegJs_rtE0.regs0 LibSegJs_rtE0.regs_out0 KS_rtE0 = true. Proof. vm_compute. reflexivity. Qed.
Definition rtE0_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#30S,8v24S,9v26S,:#S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10,,1,5X#35>7<#36490Y,T,1#35>:<T,:v26T,;#1"%pstring.
Lemma rtE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtE0] fx R M V rtE0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtE0] LibSegJs_rtE0.regs0 LibSegJs_rtE0.kn0 LibSegJs_rtE0.BR LibSegJs_rtE0.PSS LibSegJs_rtE0.NX0 LibSegJs_rtE0.F0 220796 LibSegJs_rtE0.seg_sound_ax fx R M V rtE0_conc_s. Qed.
Definition KS_rtB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtB.regs0 LibSegJs_rtB.regs_out0).
Lemma KS_rtB_ok : BG.kept_ok 48 LibSegJs_rtB.regs0 LibSegJs_rtB.regs_out0 KS_rtB = true. Proof. vm_compute. reflexivity. Qed.
Definition rtB_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#30S,8v24S,9v26S,:#1S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10,,1,2X#35>7<#35>80Y,"%pstring.
Lemma rtB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtB] fx R M V rtB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtB] LibSegJs_rtB.regs0 LibSegJs_rtB.kn0 LibSegJs_rtB.BR LibSegJs_rtB.PSS LibSegJs_rtB.NX0 LibSegJs_rtB.F0 220796 LibSegJs_rtB.seg_sound_ax fx R M V rtB_conc_s. Qed.
Definition KS_rtC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtC.regs0 LibSegJs_rtC.regs_out0).
Lemma KS_rtC_ok : BG.kept_ok 48 LibSegJs_rtC.regs0 LibSegJs_rtC.regs_out0 KS_rtC = true. Proof. vm_compute. reflexivity. Qed.
Definition rtC_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#30S,8v24S,9v26S,<v21S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10B#v21#??,,1,6X#35>84#35?3<Y,T,1#35>94T,:v24T,;v25T,=v26"%pstring.
Lemma rtC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtC] fx R M V rtC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtC] LibSegJs_rtC.regs0 LibSegJs_rtC.kn0 LibSegJs_rtC.BR LibSegJs_rtC.PSS LibSegJs_rtC.NX0 LibSegJs_rtC.F0 220804 LibSegJs_rtC.seg_sound_ax fx R M V rtC_conc_s. Qed.
Definition KS_rtD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtD.regs0 LibSegJs_rtD.regs_out0).
Lemma KS_rtD_ok : BG.kept_ok 48 LibSegJs_rtD.regs0 LibSegJs_rtD.regs_out0 KS_rtD = true. Proof. vm_compute. reflexivity. Qed.
Definition rtD_conc_s := ",19A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#30S,8v24S,9v26S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,,1,7X#35>94#35><4Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;"%pstring.
Lemma rtD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtD] fx R M V rtD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtD] LibSegJs_rtD.regs0 LibSegJs_rtD.kn0 LibSegJs_rtD.BR LibSegJs_rtD.PSS LibSegJs_rtD.NX0 LibSegJs_rtD.F0 220820 LibSegJs_rtD.seg_sound_ax fx R M V rtD_conc_s. Qed.
Definition KS_rtZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rtZ.regs0 LibSegJs_rtZ.regs_out0).
Lemma KS_rtZ_ok : BG.kept_ok 48 LibSegJs_rtZ.regs0 LibSegJs_rtZ.regs_out0 KS_rtZ = true. Proof. vm_compute. reflexivity. Qed.
Definition rtZ_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#30S,8v24S,9v26S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;I+v24#8#1,1+v24#8#1,1,8X#35>:<#35><4Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;Nb+v24#8#"%pstring.
Lemma rtZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rtZ] fx R M V rtZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rtZ] LibSegJs_rtZ.regs0 LibSegJs_rtZ.kn0 LibSegJs_rtZ.BR LibSegJs_rtZ.PSS LibSegJs_rtZ.NX0 LibSegJs_rtZ.F0 220844 LibSegJs_rtZ.seg_sound_ax fx R M V rtZ_conc_s. Qed.
End PMSRTVP.
