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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_idA LibSegJs_idB LibSegJs_idC LibSegJs_idD LibSegJs_idE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSIDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_idA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_idA.regs0 LibSegJs_idA.regs_out0).
Lemma KS_idA_ok : BG.kept_ok 48 LibSegJs_idA.regs0 LibSegJs_idA.regs_out0 KS_idA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition idA_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2v2B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000r:#800000000000Hr:#8Ir:#8La+r:#30v21B#1000v21#800000000000Ka+r:#38#50P_v2#30#30r:#98,2_v2#28#28+r:##8,1,>X#5;1;0#7?994Y,T,1#5:<88T,2_v2#30U,8,:T,9#T,:+r:#30T,;#;28<8Lbr:#;28<8Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma idA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_idA] fx R M V idA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_idA] LibSegJs_idA.regs0 LibSegJs_idA.kn0 LibSegJs_idA.BR LibSegJs_idA.PSS LibSegJs_idA.NX0 LibSegJs_idA.F0 373168 LibSegJs_idA.seg_sound_ax fx R M V idA_conc_s. Qed.
Definition KS_idB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_idB.regs0 LibSegJs_idB.regs_out0).
Lemma KS_idB_ok : BG.kept_ok 48 LibSegJs_idB.regs0 LibSegJs_idB.regs_out0 KS_idB = true. Proof. vm_compute. reflexivity. Qed.
Definition idB_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#5:<88#9:974Y,T,1#5:<90T,:#"%pstring.
Lemma idB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_idB] fx R M V idB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_idB] LibSegJs_idB.regs0 LibSegJs_idB.kn0 LibSegJs_idB.BR LibSegJs_idB.PSS LibSegJs_idB.NX0 LibSegJs_idB.F0 371848 LibSegJs_idB.seg_sound_ax fx R M V idB_conc_s. Qed.
Definition KS_idC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_idC.regs0 LibSegJs_idC.regs_out0).
Lemma KS_idC_ok : BG.kept_ok 48 LibSegJs_idC.regs0 LibSegJs_idC.regs_out0 KS_idC = true. Proof. vm_compute. reflexivity. Qed.
Definition idC_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#5:<90#9:974Y,T,1#5:<98T,:#"%pstring.
Lemma idC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_idC] fx R M V idC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_idC] LibSegJs_idC.regs0 LibSegJs_idC.kn0 LibSegJs_idC.BR LibSegJs_idC.PSS LibSegJs_idC.NX0 LibSegJs_idC.F0 371856 LibSegJs_idC.seg_sound_ax fx R M V idC_conc_s. Qed.
Definition KS_idD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_idD.regs0 LibSegJs_idD.regs_out0).
Lemma KS_idD_ok : BG.kept_ok 48 LibSegJs_idD.regs0 LibSegJs_idD.regs_out0 KS_idD = true. Proof. vm_compute. reflexivity. Qed.
Definition idD_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#5:<98#9:974Y,T,1#5:<:0T,:#"%pstring.
Lemma idD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_idD] fx R M V idD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_idD] LibSegJs_idD.regs0 LibSegJs_idD.kn0 LibSegJs_idD.BR LibSegJs_idD.PSS LibSegJs_idD.NX0 LibSegJs_idD.F0 371864 LibSegJs_idD.seg_sound_ax fx R M V idD_conc_s. Qed.
Definition KS_idE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_idE.regs0 LibSegJs_idE.regs_out0).
Lemma KS_idE_ok : BG.kept_ok 48 LibSegJs_idE.regs0 LibSegJs_idE.regs_out0 KS_idE = true. Proof. vm_compute. reflexivity. Qed.
Definition idE_conc_s := ",15A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98La_v2#8v26La_v2#10v27La_v2#18v25La_v2#20v24La_v2#28v29,,1,9X#5:<:0#9:974Y,T,1v26T,2v2T,8v27T,9v25T,:#T,12v24T,13v29"%pstring.
Lemma idE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_idE] fx R M V idE_conc_s).
Proof. r1pf L5KA.zeros_at [KS_idE] LibSegJs_idE.regs0 LibSegJs_idE.kn0 LibSegJs_idE.BR LibSegJs_idE.PSS LibSegJs_idE.NX0 LibSegJs_idE.F0 371872 LibSegJs_idE.seg_sound_ax fx R M V idE_conc_s. Qed.
End PMSIDP.
