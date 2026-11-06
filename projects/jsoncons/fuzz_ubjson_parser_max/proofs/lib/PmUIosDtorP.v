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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uidA LibSegJu_uidB LibSegJu_uidC LibSegJu_uidD LibSegJu_uidE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUIDP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uidA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uidA.regs0 LibSegJu_uidA.regs_out0).
Lemma KS_uidA_ok : BG.kept_ok 48 LibSegJu_uidA.regs0 LibSegJu_uidA.regs_out0 KS_uidA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uidA_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2v2B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000r:#800000000000Hr:#8Ir:#8La+r:#30v21B#1000v21#800000000000Ka+r:#38#50P_v2#30#30r:#98,2_v2#28#28+r:##8,1,>X#5<204#809>8Y,T,1#5;<=<T,2_v2#30U,8,:T,9#T,:+r:#30T,;#;3918Lbr:#;3918Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uidA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uidA] fx R M V uidA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uidA] LibSegJu_uidA.regs0 LibSegJu_uidA.kn0 LibSegJu_uidA.BR LibSegJu_uidA.PSS LibSegJu_uidA.NX0 LibSegJu_uidA.F0 377348 LibSegJu_uidA.seg_sound_ax fx R M V uidA_conc_s. Qed.
Definition KS_uidB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uidB.regs0 LibSegJu_uidB.regs_out0).
Lemma KS_uidB_ok : BG.kept_ok 48 LibSegJu_uidB.regs0 LibSegJu_uidB.regs_out0 KS_uidB = true. Proof. vm_compute. reflexivity. Qed.
Definition uidB_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#5;<=<#9;9<8Y,T,1#5;<>4T,:#"%pstring.
Lemma uidB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uidB] fx R M V uidB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uidB] LibSegJu_uidB.regs0 LibSegJu_uidB.kn0 LibSegJu_uidB.BR LibSegJu_uidB.PSS LibSegJu_uidB.NX0 LibSegJu_uidB.F0 376028 LibSegJu_uidB.seg_sound_ax fx R M V uidB_conc_s. Qed.
Definition KS_uidC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uidC.regs0 LibSegJu_uidC.regs_out0).
Lemma KS_uidC_ok : BG.kept_ok 48 LibSegJu_uidC.regs0 LibSegJu_uidC.regs_out0 KS_uidC = true. Proof. vm_compute. reflexivity. Qed.
Definition uidC_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#5;<>4#9;9<8Y,T,1#5;<><T,:#"%pstring.
Lemma uidC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uidC] fx R M V uidC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uidC] LibSegJu_uidC.regs0 LibSegJu_uidC.kn0 LibSegJu_uidC.BR LibSegJu_uidC.PSS LibSegJu_uidC.NX0 LibSegJu_uidC.F0 376036 LibSegJu_uidC.seg_sound_ax fx R M V uidC_conc_s. Qed.
Definition KS_uidD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uidD.regs0 LibSegJu_uidD.regs_out0).
Lemma KS_uidD_ok : BG.kept_ok 48 LibSegJu_uidD.regs0 LibSegJu_uidD.regs_out0 KS_uidD = true. Proof. vm_compute. reflexivity. Qed.
Definition uidD_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#5;<><#9;9<8Y,T,1#5;<?4T,:#"%pstring.
Lemma uidD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uidD] fx R M V uidD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uidD] LibSegJu_uidD.regs0 LibSegJu_uidD.kn0 LibSegJu_uidD.BR LibSegJu_uidD.PSS LibSegJu_uidD.NX0 LibSegJu_uidD.F0 376044 LibSegJu_uidD.seg_sound_ax fx R M V uidD_conc_s. Qed.
Definition KS_uidE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uidE.regs0 LibSegJu_uidE.regs_out0).
Lemma KS_uidE_ok : BG.kept_ok 48 LibSegJu_uidE.regs0 LibSegJu_uidE.regs_out0 KS_uidE = true. Proof. vm_compute. reflexivity. Qed.
Definition uidE_conc_s := ",15A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#30S,8v28B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#1000v28#800000000000Hv28#8Ka+v28#38#50P_v2#30#30v28#98La_v2#8v26La_v2#10v27La_v2#18v25La_v2#20v24La_v2#28v29,,1,9X#5;<?4#9;9<8Y,T,1v26T,2v2T,8v27T,9v25T,:#T,12v24T,13v29"%pstring.
Lemma uidE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uidE] fx R M V uidE_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uidE] LibSegJu_uidE.regs0 LibSegJu_uidE.kn0 LibSegJu_uidE.BR LibSegJu_uidE.PSS LibSegJu_uidE.NX0 LibSegJu_uidE.F0 376052 LibSegJu_uidE.seg_sound_ax fx R M V uidE_conc_s. Qed.
End PMUIDP.
