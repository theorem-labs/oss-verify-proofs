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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urrA LibSegJu_urrB LibSegJu_uvdA LibSegJu_uvdL LibSegJu_uvdM LibSegJu_uvdZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUOP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_urrA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urrA.regs0 LibSegJu_urrA.regs_out0).
Lemma KS_urrA_ok : BG.kept_ok 48 LibSegJu_urrA.regs0 LibSegJu_urrA.regs_out0 KS_urrA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urrA_conc_s := ",5A#v2p#2#40S,2v2B#7???7?800020v2#800000000000Hv2#10I_v2#20#20,1_v2#18#18,1,9X#34664#36408Y,T,1#34680T,2_v2#20U,8,;U,9,:Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urrA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urrA] fx R M V urrA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urrA] LibSegJu_urrA.regs0 LibSegJu_urrA.kn0 LibSegJu_urrA.BR LibSegJu_urrA.PSS LibSegJu_urrA.NX0 LibSegJu_urrA.F0 214628 LibSegJu_urrA.seg_sound_ax fx R M V urrA_conc_s. Qed.
Definition KS_urrB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urrB.regs0 LibSegJu_urrB.regs_out0).
Lemma KS_urrB_ok : BG.kept_ok 48 LibSegJu_urrB.regs0 LibSegJu_urrB.regs_out0 KS_urrB = true. Proof. vm_compute. reflexivity. Qed.
Definition urrB_conc_s := ",14A#v2p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#20S,8v28S,9v29B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v26La_v2#10v27La_v2#18v25B#1000v29#800000000000La+v29#180v2:B#1000v2:#800000000000Hv2:#8,,1,9X#34680#36574Y,T,1v26T,2v2T,8v27T,9v25T,:v29T,;v2:T,<v28"%pstring.
Lemma urrB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urrB] fx R M V urrB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urrB] LibSegJu_urrB.regs0 LibSegJu_urrB.kn0 LibSegJu_urrB.BR LibSegJu_urrB.PSS LibSegJu_urrB.NX0 LibSegJu_urrB.F0 214656 LibSegJu_urrB.seg_sound_ax fx R M V urrB_conc_s. Qed.
Definition KS_uvdA_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uvdA.regs0 LibSegJu_uvdA.regs_out0).
Lemma KS_uvdA_0_ok : BG.kept_ok 48 LibSegJu_uvdA.regs0 LibSegJu_uvdA.regs_out0 KS_uvdA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvdA_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uvdA.regs0 LibSegJu_uvdA.regs_out1).
Lemma KS_uvdA_1_ok : BG.kept_ok 48 LibSegJu_uvdA.regs0 LibSegJu_uvdA.regs_out1 KS_uvdA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvdA_conc_s := ",10A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#1000r:#800000000000Lar:v21B#1000v21#800000000000Hv21#8Lav21v22B#1000v22#800000000000La+v21#8v23B#1000v23#800000000000,,2,7X#35928#3594<Y,T,:v22T,;v23T,<v21T,=#20D#1%_v22v23p#2#40,6X#35928#3595<Y,1T,:v22T,;v23T,<v21C%_v22v23p#2#40#1"%pstring.
Lemma uvdA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvdA_0; KS_uvdA_1] fx R M V uvdA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvdA_0; KS_uvdA_1] LibSegJu_uvdA.regs0 LibSegJu_uvdA.kn0 LibSegJu_uvdA.BR LibSegJu_uvdA.PSS LibSegJu_uvdA.NX0 LibSegJu_uvdA.F0 219432 LibSegJu_uvdA.seg_sound_ax fx R M V uvdA_conc_s. Qed.
Definition KS_uvdL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uvdL.regs0 LibSegJu_uvdL.regs_out0).
Lemma KS_uvdL_ok : BG.kept_ok 48 LibSegJu_uvdL.regs0 LibSegJu_uvdL.regs_out0 KS_uvdL = true. Proof. vm_compute. reflexivity. Qed.
Definition uvdL_conc_s := ",<A#v2p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v22S,;v23S,=#20B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#1000v22#800000000000B#1000v23#800000000000,,1,3X#3594<#35958Y,T,;_v23#20"%pstring.
Lemma uvdL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvdL] fx R M V uvdL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvdL] LibSegJu_uvdL.regs0 LibSegJu_uvdL.kn0 LibSegJu_uvdL.BR LibSegJu_uvdL.PSS LibSegJu_uvdL.NX0 LibSegJu_uvdL.F0 219468 LibSegJu_uvdL.seg_sound_ax fx R M V uvdL_conc_s. Qed.
Definition KS_uvdM_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uvdM.regs0 LibSegJu_uvdM.regs_out0).
Lemma KS_uvdM_0_ok : BG.kept_ok 48 LibSegJu_uvdM.regs0 LibSegJu_uvdM.regs_out0 KS_uvdM_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvdM_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uvdM.regs0 LibSegJu_uvdM.regs_out1).
Lemma KS_uvdM_1_ok : BG.kept_ok 48 LibSegJu_uvdM.regs0 LibSegJu_uvdM.regs_out1 KS_uvdM_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvdM_conc_s := ",9A#v2p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v22S,;v23B#7???7?800010v2#800000000000Hv2#10I_v2#10#10,,2,3X#35958#3594<Y,D#1%_v23v22p#2#40,3X#35958#3595<Y,1C%_v23v22p#2#40#1"%pstring.
Lemma uvdM_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvdM_0; KS_uvdM_1] fx R M V uvdM_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvdM_0; KS_uvdM_1] LibSegJu_uvdM.regs0 LibSegJu_uvdM.kn0 LibSegJu_uvdM.BR LibSegJu_uvdM.PSS LibSegJu_uvdM.NX0 LibSegJu_uvdM.F0 219480 LibSegJu_uvdM.seg_sound_ax fx R M V uvdM_conc_s. Qed.
Definition KS_uvdZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uvdZ.regs0 LibSegJu_uvdZ.regs_out0).
Lemma KS_uvdZ_ok : BG.kept_ok 48 LibSegJu_uvdZ.regs0 LibSegJu_uvdZ.regs_out0 KS_uvdZ = true. Proof. vm_compute. reflexivity. Qed.
Definition uvdZ_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2S,:v22S,<v21B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#1000v21#800000000000Hv21#8Iv21#18La+v21#10v24B#1000v22#800000000000,1+v21#8#8,1,4X#3595<#55454Y,T,;+*-1v22v24Lb+v21#8v22"%pstring.
Lemma uvdZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvdZ] fx R M V uvdZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvdZ] LibSegJu_uvdZ.regs0 LibSegJu_uvdZ.kn0 LibSegJu_uvdZ.BR LibSegJu_uvdZ.PSS LibSegJu_uvdZ.NX0 LibSegJu_uvdZ.F0 219484 LibSegJu_uvdZ.seg_sound_ax fx R M V uvdZ_conc_s. Qed.
End PMUOP.
