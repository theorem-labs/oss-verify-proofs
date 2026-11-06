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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urS LibSegJu_urL LibSegJu_urLp LibSegJu_urM LibSegJu_urZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMURSP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_urS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urS.regs0 LibSegJu_urS.regs_out0).
Lemma KS_urS_ok : BG.kept_ok 48 LibSegJu_urS.regs0 LibSegJu_urS.regs_out0 KS_urS = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urS_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40Ir:#180B#1000r:#800000000000Hr:#8P_v2#40#40r:#180Na+r:#150v21B#v21#??Fv21#fLa+r:#168v22B#1000v22#800000000000Hv22#10B#20v24#10000La+r:#170+v22v24,3_v2#18#18+r:#8#8+r:#150#2,1,<X#36408#36458Y,T,2_v2#40U,8,:T,:v22T,;+v22v24T,<#20QNb+r:#150#Nb++r:#150#1#QNb+r:#8#1Nb++r:#8#1#Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urS] fx R M V urS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urS] LibSegJu_urS.regs0 LibSegJu_urS.kn0 LibSegJu_urS.BR LibSegJu_urS.PSS LibSegJu_urS.NX0 LibSegJu_urS.F0 222216 LibSegJu_urS.seg_sound_ax fx R M V urS_conc_s. Qed.
Definition KS_urL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urL.regs0 LibSegJu_urL.regs_out0).
Lemma KS_urL_ok : BG.kept_ok 48 LibSegJu_urL.regs0 LibSegJu_urL.regs_out0 KS_urL = true. Proof. vm_compute. reflexivity. Qed.
Definition urL_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2v2B#7???7?800040v2#800000000000Hv2#10I_v2#40#40Ir:#180B#1000r:#800000000000Hr:#8P_v2#40#40r:#180Na+r:#150v21B#v21#??Fv21#tLa+r:#160v25B#1000v25#800000000000Iv25#1P_v2#40#40v25#1Pv25#1r:#180La+r:#168v22B#1000v22#800000000000Hv22#10B#20v24#10000La+r:#170+v22v24,4_v2#18#18+r:#8#8+r:#158#8+v25##1,1,=X#36408#36458Y,T,2_v2#40U,8,:T,:v22T,;+v22v24T,<#20Lb+r:#158#Nbv25#QNb+r:#8#1Nb++r:#8#1#Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urL] fx R M V urL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urL] LibSegJu_urL.regs0 LibSegJu_urL.kn0 LibSegJu_urL.BR LibSegJu_urL.PSS LibSegJu_urL.NX0 LibSegJu_urL.F0 222216 LibSegJu_urL.seg_sound_ax fx R M V urL_conc_s. Qed.
Definition KS_urLp : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urLp.regs0 LibSegJu_urLp.regs_out0).
Lemma KS_urLp_ok : BG.kept_ok 48 LibSegJu_urLp.regs0 LibSegJu_urLp.regs_out0 KS_urLp = true. Proof. vm_compute. reflexivity. Qed.
Definition urLp_conc_s := ",<A#v2p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v22S,;v23S,<#20B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#1000v22#800000000000B#1000v23#800000000000,,1,3X#36458#36464Y,T,;_v23#20"%pstring.
Lemma urLp_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urLp] fx R M V urLp_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urLp] LibSegJu_urLp.regs0 LibSegJu_urLp.kn0 LibSegJu_urLp.BR LibSegJu_urLp.PSS LibSegJu_urLp.NX0 LibSegJu_urLp.F0 222296 LibSegJu_urLp.seg_sound_ax fx R M V urLp_conc_s. Qed.
Definition KS_urM_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urM.regs0 LibSegJu_urM.regs_out0).
Lemma KS_urM_0_ok : BG.kept_ok 48 LibSegJu_urM.regs0 LibSegJu_urM.regs_out0 KS_urM_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urM_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urM.regs0 LibSegJu_urM.regs_out1).
Lemma KS_urM_1_ok : BG.kept_ok 48 LibSegJu_urM.regs0 LibSegJu_urM.regs_out1 KS_urM_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition urM_conc_s := ",9A#v2p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v22S,;v23B#7???7?800040v2#800000000000Hv2#10I_v2#40#40,,2,3X#36464#36458Y,D#1%_v23v22p#2#40,3X#36464#36468Y,1C%_v23v22p#2#40#1"%pstring.
Lemma urM_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urM_0; KS_urM_1] fx R M V urM_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urM_0; KS_urM_1] LibSegJu_urM.regs0 LibSegJu_urM.kn0 LibSegJu_urM.BR LibSegJu_urM.PSS LibSegJu_urM.NX0 LibSegJu_urM.F0 222308 LibSegJu_urM.seg_sound_ax fx R M V urM_conc_s. Qed.
Definition KS_urZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urZ.regs0 LibSegJu_urZ.regs_out0).
Lemma KS_urZ_ok : BG.kept_ok 48 LibSegJu_urZ.regs0 LibSegJu_urZ.regs_out0 KS_urZ = true. Proof. vm_compute. reflexivity. Qed.
Definition urZ_conc_s := ",1;A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#40S,8v:S,:v22B#7???7?800040v2#800000000000Hv2#10I_v2#40#40Iv:#180B#1000v:#800000000000Hv:#8P_v2#40#40v:#180La_v2#8v26La_v2#10v27La_v2#18v28B#1000v22#800000000000Hv22#10B#20v23#10000La+v:#178+v22v23Iv22#20P_v2#40#40v22#20Pv22#20v:#180,3+v:#<#4+v:#170#8+v22##20,1,>X#36468#36558Y,T,1v26T,2v2T,8v27T,9v28T,:#20T,;#Mb+v:#<#Lb+v:#170+v22#20Lb+v22#18#Nb+v22#10#Lb+v22#8#Mbv22#"%pstring.
Lemma urZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urZ] fx R M V urZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urZ] LibSegJu_urZ.regs0 LibSegJu_urZ.kn0 LibSegJu_urZ.BR LibSegJu_urZ.PSS LibSegJu_urZ.NX0 LibSegJu_urZ.F0 222312 LibSegJu_urZ.seg_sound_ax fx R M V urZ_conc_s. Qed.
End PMURSP.
