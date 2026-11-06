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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urtA0 LibSegJu_urtA2 LibSegJu_urtB LibSegJu_urtC LibSegJu_urtD LibSegJu_urtE0 LibSegJu_urtZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMURTP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_urtA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtA0.regs0 LibSegJu_urtA0.regs_out0).
Lemma KS_urtA0_ok : BG.kept_ok 48 LibSegJu_urtA0.regs0 LibSegJu_urtA0.regs_out0 KS_urtA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urtA0_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;7120La+v24#108v2=Lav2=#;3:>8Ma+v2=#98#Pv24#180v2=#110,1_v2#30#30,1,>X#369;<#374;8Y,T,1#36:18T,2_v2#30T,8v24T,9v26T,:+v24#18T,;_v2#21T,<#1T,12v25Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urtA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtA0] fx R M V urtA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtA0] LibSegJu_urtA0.regs0 LibSegJu_urtA0.kn0 LibSegJu_urtA0.BR LibSegJu_urtA0.PSS LibSegJu_urtA0.NX0 LibSegJu_urtA0.F0 223676 LibSegJu_urtA0.seg_sound_ax fx R M V urtA0_conc_s. Qed.
Definition KS_urtA2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtA2.regs0 LibSegJu_urtA2.regs_out0).
Lemma KS_urtA2_ok : BG.kept_ok 48 LibSegJu_urtA2.regs0 LibSegJu_urtA2.regs_out0 KS_urtA2 = true. Proof. vm_compute. reflexivity. Qed.
Definition urtA2_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;7120La+v24#108v2=Lav2=#;3:>8Ma+v2=#98#2Pv24#180v2=#110,1_v2#30#30,1,>X#369;<#374;8Y,T,1#36:18T,2_v2#30T,8v24T,9v26T,:+v24#18T,;_v2#21T,<#1T,12v25Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urtA2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtA2] fx R M V urtA2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtA2] LibSegJu_urtA2.regs0 LibSegJu_urtA2.kn0 LibSegJu_urtA2.BR LibSegJu_urtA2.PSS LibSegJu_urtA2.NX0 LibSegJu_urtA2.F0 223676 LibSegJu_urtA2.seg_sound_ax fx R M V urtA2_conc_s. Qed.
Definition KS_urtB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtB.regs0 LibSegJu_urtB.regs_out0).
Lemma KS_urtB_ok : BG.kept_ok 48 LibSegJu_urtB.regs0 LibSegJu_urtB.regs_out0 KS_urtB = true. Proof. vm_compute. reflexivity. Qed.
Definition urtB_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#30S,8v24S,9v26S,:#1S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10,,1,2X#36:18#36:1<Y,"%pstring.
Lemma urtB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtB] fx R M V urtB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtB] LibSegJu_urtB.regs0 LibSegJu_urtB.kn0 LibSegJu_urtB.BR LibSegJu_urtB.PSS LibSegJu_urtB.NX0 LibSegJu_urtB.F0 223768 LibSegJu_urtB.seg_sound_ax fx R M V urtB_conc_s. Qed.
Definition KS_urtC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtC.regs0 LibSegJu_urtC.regs_out0).
Lemma KS_urtC_ok : BG.kept_ok 48 LibSegJu_urtC.regs0 LibSegJu_urtC.regs_out0 KS_urtC = true. Proof. vm_compute. reflexivity. Qed.
Definition urtC_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#30S,8v24S,9v26S,<v21S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10B#v21#??,,1,6X#36:20#36:?<Y,T,1#36:30T,:v24T,;v25T,=v26"%pstring.
Lemma urtC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtC] fx R M V urtC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtC] LibSegJu_urtC.regs0 LibSegJu_urtC.kn0 LibSegJu_urtC.BR LibSegJu_urtC.PSS LibSegJu_urtC.NX0 LibSegJu_urtC.F0 223776 LibSegJu_urtC.seg_sound_ax fx R M V urtC_conc_s. Qed.
Definition KS_urtD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtD.regs0 LibSegJu_urtD.regs_out0).
Lemma KS_urtD_ok : BG.kept_ok 48 LibSegJu_urtD.regs0 LibSegJu_urtD.regs_out0 KS_urtD = true. Proof. vm_compute. reflexivity. Qed.
Definition urtD_conc_s := ",19A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#30S,8v24S,9v26S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,,1,7X#36:30#36:60Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;"%pstring.
Lemma urtD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtD] fx R M V urtD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtD] LibSegJu_urtD.regs0 LibSegJu_urtD.kn0 LibSegJu_urtD.BR LibSegJu_urtD.PSS LibSegJu_urtD.NX0 LibSegJu_urtD.F0 223792 LibSegJu_urtD.seg_sound_ax fx R M V urtD_conc_s. Qed.
Definition KS_urtE0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtE0.regs0 LibSegJu_urtE0.regs_out0).
Lemma KS_urtE0_ok : BG.kept_ok 48 LibSegJu_urtE0.regs0 LibSegJu_urtE0.regs_out0 KS_urtE0 = true. Proof. vm_compute. reflexivity. Qed.
Definition urtE0_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#30S,8v24S,9v26S,:#S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10,,1,5X#36:18#370:<Y,T,1#36:48T,:v26T,;#1"%pstring.
Lemma urtE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtE0] fx R M V urtE0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtE0] LibSegJu_urtE0.regs0 LibSegJu_urtE0.kn0 LibSegJu_urtE0.BR LibSegJu_urtE0.PSS LibSegJu_urtE0.NX0 LibSegJu_urtE0.F0 223768 LibSegJu_urtE0.seg_sound_ax fx R M V urtE0_conc_s. Qed.
Definition KS_urtZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urtZ.regs0 LibSegJu_urtZ.regs_out0).
Lemma KS_urtZ_ok : BG.kept_ok 48 LibSegJu_urtZ.regs0 LibSegJu_urtZ.regs_out0 KS_urtZ = true. Proof. vm_compute. reflexivity. Qed.
Definition urtZ_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#30S,8v24S,9v26S,12v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>80Hv24#8P_v2#30#30v24#180B#7???7?800030v26#7??????????0Hv26#8P_v2#30#30v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;I+v24#8#1,1+v24#8#1,1,8X#36:48#36:60Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;Nb+v24#8#"%pstring.
Lemma urtZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urtZ] fx R M V urtZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urtZ] LibSegJu_urtZ.regs0 LibSegJu_urtZ.kn0 LibSegJu_urtZ.BR LibSegJu_urtZ.PSS LibSegJu_urtZ.NX0 LibSegJu_urtZ.F0 223816 LibSegJu_urtZ.seg_sound_ax fx R M V urtZ_conc_s. Qed.
End PMURTP.
