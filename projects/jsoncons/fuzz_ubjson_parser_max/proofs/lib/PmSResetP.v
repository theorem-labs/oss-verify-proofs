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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rsS LibSegJs_rsL.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRSP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_rsS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rsS.regs0 LibSegJs_rsS.regs_out0).
Lemma KS_rsS_ok : BG.kept_ok 48 LibSegJs_rsS.regs0 LibSegJs_rsS.regs_out0 KS_rsS = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rsS_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2B#7???7?800050v2#800000000000Hv2#10I_v2#50#50Ir:#180B#1000r:#800000000000Hr:#8P_v2#50#50r:#180Na+r:#150v21B#v21#??Fv21#fLa+r:#168v22B#1000v22#800000000000Hv22#10B#20v23#10000La+r:#178+v22v23Iv22#20P_v2#50#50v22#20Pv22#20r:#180,5_v2#28#28+r:#8#8+r:#150#2+r:#170#8+v22##20,1,11X#35984#35::8Y,T,:v22T,;+v22v23Mb+r:#<#Lb+r:#170+v22#20Lb+v22#18#Nb+v22#10#Lb+v22#8#Mbv22#QNb+r:#150#Nb++r:#150#1#QNb+r:#8#1Nb++r:#8#1#Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rsS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rsS] fx R M V rsS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rsS] LibSegJs_rsS.regs0 LibSegJs_rsS.kn0 LibSegJs_rsS.BR LibSegJs_rsS.PSS LibSegJs_rsS.NX0 LibSegJs_rsS.F0 219524 LibSegJs_rsS.seg_sound_ax fx R M V rsS_conc_s. Qed.
Definition KS_rsL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rsL.regs0 LibSegJs_rsL.regs_out0).
Lemma KS_rsL_ok : BG.kept_ok 48 LibSegJs_rsL.regs0 LibSegJs_rsL.regs_out0 KS_rsL = true. Proof. vm_compute. reflexivity. Qed.
Definition rsL_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40S,2v2B#7???7?800050v2#800000000000Hv2#10I_v2#50#50Ir:#180B#1000r:#800000000000Hr:#8P_v2#50#50r:#180Na+r:#150v21B#v21#??Fv21#tLa+r:#160v25B#1000v25#800000000000Iv25#1P_v2#50#50v25#1Pv25#1r:#180Pv25#1v22#20La+r:#168v22B#1000v22#800000000000Hv22#10B#20v23#10000La+r:#178+v22v23Iv22#20P_v2#50#50v22#20Pv22#20r:#180,6_v2#28#28+r:#8#8+r:#158#8+r:#170#8+v22##20+v25##1,1,12X#35984#35::8Y,T,:v22T,;+v22v23Mb+r:#<#Lb+r:#170+v22#20Lb+v22#18#Nb+v22#10#Lb+v22#8#Mbv22#Lb+r:#158#Nbv25#QNb+r:#8#1Nb++r:#8#1#Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rsL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rsL] fx R M V rsL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rsL] LibSegJs_rsL.regs0 LibSegJs_rsL.kn0 LibSegJs_rsL.BR LibSegJs_rsL.PSS LibSegJs_rsL.NX0 LibSegJs_rsL.F0 219524 LibSegJs_rsL.seg_sound_ax fx R M V rsL_conc_s. Qed.
End PMSRSP.
