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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ja0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aidA LibSegJa_aidB LibSegJa_aidC LibSegJa_aidD LibSegJa_aidE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAIDP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aidA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aidA.regs0 LibSegJa_aidA.regs_out0).
Lemma KS_aidA_ok : BG.kept_ok 48 LibSegJa_aidA.regs0 LibSegJa_aidA.regs_out0 KS_aidA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aidA_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2v2B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000r:#7?????????68Hr:#8Ir:#8La+r:#30v21B#1000v21#800000000000Ka+r:#38#50P_v2#30#30r:#98,2_v2#28#28+r:##8,1,>X#=5808#?9?><Y,T,1#=52>0T,2_v2#30U,8,:T,9#T,:+r:#30T,;#1300=8Lbr:#1300=8Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aidA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidA] fx R M V aidA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidA] LibSegJa_aidA.regs0 LibSegJa_aidA.kn0 LibSegJa_aidA.BR LibSegJa_aidA.PSS LibSegJa_aidA.NX0 LibSegJa_aidA.F0 874504 LibSegJa_aidA.seg_sound_ax fx R M V aidA_conc_s. Qed.
Definition KS_aidB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aidB.regs0 LibSegJa_aidB.regs_out0).
Lemma KS_aidB_ok : BG.kept_ok 48 LibSegJa_aidB.regs0 LibSegJa_aidB.regs_out0 KS_aidB = true. Proof. vm_compute. reflexivity. Qed.
Definition aidB_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#=52>0#78>;<Y,T,1#=52>8T,:#"%pstring.
Lemma aidB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidB] fx R M V aidB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidB] LibSegJa_aidB.regs0 LibSegJa_aidB.kn0 LibSegJa_aidB.BR LibSegJa_aidB.PSS LibSegJa_aidB.NX0 LibSegJa_aidB.F0 873184 LibSegJa_aidB.seg_sound_ax fx R M V aidB_conc_s. Qed.
Definition KS_aidC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aidC.regs0 LibSegJa_aidC.regs_out0).
Lemma KS_aidC_ok : BG.kept_ok 48 LibSegJa_aidC.regs0 LibSegJa_aidC.regs_out0 KS_aidC = true. Proof. vm_compute. reflexivity. Qed.
Definition aidC_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#=52>8#78>;<Y,T,1#=52?0T,:#"%pstring.
Lemma aidC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidC] fx R M V aidC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidC] LibSegJa_aidC.regs0 LibSegJa_aidC.kn0 LibSegJa_aidC.BR LibSegJa_aidC.PSS LibSegJa_aidC.NX0 LibSegJa_aidC.F0 873192 LibSegJa_aidC.seg_sound_ax fx R M V aidC_conc_s. Qed.
Definition KS_aidD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aidD.regs0 LibSegJa_aidD.regs_out0).
Lemma KS_aidD_ok : BG.kept_ok 48 LibSegJa_aidD.regs0 LibSegJa_aidD.regs_out0 KS_aidD = true. Proof. vm_compute. reflexivity. Qed.
Definition aidD_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#=52?0#78>;<Y,T,1#=52?8T,:#"%pstring.
Lemma aidD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidD] fx R M V aidD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidD] LibSegJa_aidD.regs0 LibSegJa_aidD.kn0 LibSegJa_aidD.BR LibSegJa_aidD.PSS LibSegJa_aidD.NX0 LibSegJa_aidD.F0 873200 LibSegJa_aidD.seg_sound_ax fx R M V aidD_conc_s. Qed.
Definition KS_aidE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aidE.regs0 LibSegJa_aidE.regs_out0).
Lemma KS_aidE_ok : BG.kept_ok 48 LibSegJa_aidE.regs0 LibSegJa_aidE.regs_out0 KS_aidE = true. Proof. vm_compute. reflexivity. Qed.
Definition aidE_conc_s := ",15A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98La_v2#8v26La_v2#10v27La_v2#18v25La_v2#20v24La_v2#28v29,,1,9X#=52?8#78>;<Y,T,1v26T,2v2T,8v27T,9v25T,:#T,12v24T,13v29"%pstring.
Lemma aidE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidE] fx R M V aidE_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidE] LibSegJa_aidE.regs0 LibSegJa_aidE.kn0 LibSegJa_aidE.BR LibSegJa_aidE.PSS LibSegJa_aidE.NX0 LibSegJa_aidE.F0 873208 LibSegJa_aidE.seg_sound_ax fx R M V aidE_conc_s. Qed.
End PMAIDP.
