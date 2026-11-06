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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_ufbE LibSegJu_ufbA LibSegJu_ufbB1 LibSegJu_ufbB2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUFBP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_ufbE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ufbE.regs0 LibSegJu_ufbE.regs_out0).
Lemma KS_ufbE_ok : BG.kept_ok 48 LibSegJu_ufbE.regs0 LibSegJu_ufbE.regs_out0 KS_ufbE = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ufbE_conc_s := ",17A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;7120Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;3:>8La+v25#10#;39?8Ma+v25#98#2Ma+v25#9<#La+v25#:0+v25#10,1_v2#20#20,1,8X#37720#37828Y,T,:#T,<#Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ufbE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ufbE] fx R M V ufbE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ufbE] LibSegJu_ufbE.regs0 LibSegJu_ufbE.kn0 LibSegJu_ufbE.BR LibSegJu_ufbE.PSS LibSegJu_ufbE.NX0 LibSegJu_ufbE.F0 227104 LibSegJu_ufbE.seg_sound_ax fx R M V ufbE_conc_s. Qed.
Definition KS_ufbA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ufbA.regs0 LibSegJu_ufbA.regs_out0).
Lemma KS_ufbA_ok : BG.kept_ok 48 LibSegJu_ufbA.regs0 LibSegJu_ufbA.regs_out0 KS_ufbA = true. Proof. vm_compute. reflexivity. Qed.
Definition ufbA_conc_s := ",17A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;7120Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;3:>8La+v25#10#;39?8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10,1_v2#20#20,1,<X#37720#5<2:8Y,T,1#37788T,2_v2#20T,8v24U,9,<T,:+v25#10T,=#5<2:8Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ufbA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ufbA] fx R M V ufbA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ufbA] LibSegJu_ufbA.regs0 LibSegJu_ufbA.kn0 LibSegJu_ufbA.BR LibSegJu_ufbA.PSS LibSegJu_ufbA.NX0 LibSegJu_ufbA.F0 227104 LibSegJu_ufbA.seg_sound_ax fx R M V ufbA_conc_s. Qed.
Definition KS_ufbB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ufbB1.regs0 LibSegJu_ufbB1.regs_out0).
Lemma KS_ufbB1_ok : BG.kept_ok 48 LibSegJu_ufbB1.regs0 LibSegJu_ufbB1.regs_out0 KS_ufbB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ufbB1_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#4000S,:#4000B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;7120Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;3:>8La+v25#10#;39?8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,1_v2#20#20,1,;X#37788#37828Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma ufbB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ufbB1] fx R M V ufbB1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ufbB1] LibSegJu_ufbB1.regs0 LibSegJu_ufbB1.kn0 LibSegJu_ufbB1.BR LibSegJu_ufbB1.PSS LibSegJu_ufbB1.NX0 LibSegJu_ufbB1.F0 227208 LibSegJu_ufbB1.seg_sound_ax fx R M V ufbB1_conc_s. Qed.
Definition KS_ufbB2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ufbB2.regs0 LibSegJu_ufbB2.regs_out0).
Lemma KS_ufbB2_ok : BG.kept_ok 48 LibSegJu_ufbB2.regs0 LibSegJu_ufbB2.regs_out0 KS_ufbB2 = true. Proof. vm_compute. reflexivity. Qed.
Definition ufbB2_conc_s := ",24A#v2p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#4000S,:v23B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;7120Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;3:>8La+v25#10#;39?8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;B#v23#3???I+v25#98#4,2_v2#20#20+v25#98#4,1,?X#37788#37828Y,T,1v28T,2v2T,8v29T,9v2:T,;#2T,<#T,=#T,12v2;Mb+v25#98#2Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma ufbB2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ufbB2] fx R M V ufbB2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ufbB2] LibSegJu_ufbB2.regs0 LibSegJu_ufbB2.kn0 LibSegJu_ufbB2.BR LibSegJu_ufbB2.PSS LibSegJu_ufbB2.NX0 LibSegJu_ufbB2.F0 227208 LibSegJu_ufbB2.seg_sound_ax fx R M V ufbB2_conc_s. Qed.
End PMUFBP.
