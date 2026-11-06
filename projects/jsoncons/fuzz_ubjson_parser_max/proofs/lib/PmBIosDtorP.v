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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Jb0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_aidA LibSegJb_aidB LibSegJb_aidC LibSegJb_aidD LibSegJb_aidE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBIDP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aidA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aidA.regs0 LibSegJb_aidA.regs_out0).
Lemma KS_aidA_ok : BG.kept_ok 48 LibSegJb_aidA.regs0 LibSegJb_aidA.regs_out0 KS_aidA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aidA_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2v2B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000r:#7?????????68Hr:#8Ir:#8La+r:#30v21B#1000v21#800000000000Ka+r:#38#50P_v2#30#30r:#98,2_v2#28#28+r:##8,1,>X#=7640#?;>24Y,T,1#=7118T,2_v2#30U,8,:T,9#T,:+r:#30T,;#131>40Lbr:#131>40Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aidA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidA] fx R M V aidA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidA] LibSegJb_aidA.regs0 LibSegJb_aidA.kn0 LibSegJb_aidA.BR LibSegJb_aidA.PSS LibSegJb_aidA.NX0 LibSegJb_aidA.F0 882240 LibSegJb_aidA.seg_sound_ax fx R M V aidA_conc_s. Qed.
Definition KS_aidB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aidB.regs0 LibSegJb_aidB.regs_out0).
Lemma KS_aidB_ok : BG.kept_ok 48 LibSegJb_aidB.regs0 LibSegJb_aidB.regs_out0 KS_aidB = true. Proof. vm_compute. reflexivity. Qed.
Definition aidB_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#=7118#7918<Y,T,1#=7120T,:#"%pstring.
Lemma aidB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidB] fx R M V aidB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidB] LibSegJb_aidB.regs0 LibSegJb_aidB.kn0 LibSegJb_aidB.BR LibSegJb_aidB.PSS LibSegJb_aidB.NX0 LibSegJb_aidB.F0 880920 LibSegJb_aidB.seg_sound_ax fx R M V aidB_conc_s. Qed.
Definition KS_aidC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aidC.regs0 LibSegJb_aidC.regs_out0).
Lemma KS_aidC_ok : BG.kept_ok 48 LibSegJb_aidC.regs0 LibSegJb_aidC.regs_out0 KS_aidC = true. Proof. vm_compute. reflexivity. Qed.
Definition aidC_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#=7120#7918<Y,T,1#=7128T,:#"%pstring.
Lemma aidC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidC] fx R M V aidC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidC] LibSegJb_aidC.regs0 LibSegJb_aidC.kn0 LibSegJb_aidC.BR LibSegJb_aidC.PSS LibSegJb_aidC.NX0 LibSegJb_aidC.F0 880928 LibSegJb_aidC.seg_sound_ax fx R M V aidC_conc_s. Qed.
Definition KS_aidD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aidD.regs0 LibSegJb_aidD.regs_out0).
Lemma KS_aidD_ok : BG.kept_ok 48 LibSegJb_aidD.regs0 LibSegJb_aidD.regs_out0 KS_aidD = true. Proof. vm_compute. reflexivity. Qed.
Definition aidD_conc_s := ",;A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98,,1,4X#=7128#7918<Y,T,1#=7130T,:#"%pstring.
Lemma aidD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidD] fx R M V aidD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidD] LibSegJb_aidD.regs0 LibSegJb_aidD.kn0 LibSegJb_aidD.BR LibSegJb_aidD.PSS LibSegJb_aidD.NX0 LibSegJb_aidD.F0 880936 LibSegJb_aidD.seg_sound_ax fx R M V aidD_conc_s. Qed.
Definition KS_aidE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aidE.regs0 LibSegJb_aidE.regs_out0).
Lemma KS_aidE_ok : BG.kept_ok 48 LibSegJb_aidE.regs0 LibSegJb_aidE.regs_out0 KS_aidE = true. Proof. vm_compute. reflexivity. Qed.
Definition aidE_conc_s := ",15A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#30S,8v28B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v28#7?????????68Hv28#8Ka+v28#38#50P_v2#30#30v28#98La_v2#8v26La_v2#10v27La_v2#18v25La_v2#20v24La_v2#28v29,,1,9X#=7130#7918<Y,T,1v26T,2v2T,8v27T,9v25T,:#T,12v24T,13v29"%pstring.
Lemma aidE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aidE] fx R M V aidE_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aidE] LibSegJb_aidE.regs0 LibSegJb_aidE.kn0 LibSegJb_aidE.BR LibSegJb_aidE.PSS LibSegJb_aidE.NX0 LibSegJb_aidE.F0 880944 LibSegJb_aidE.seg_sound_ax fx R M V aidE_conc_s. Qed.
End PMBIDP.
