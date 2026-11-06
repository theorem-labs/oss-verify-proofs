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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urkA LibSegJu_urkB LibSegJu_urkE LibSegJu_urkF LibSegJu_urkK LibSegJu_urkW LibSegJu_urkZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMURKP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_urkA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkA.regs0 LibSegJu_urkA.regs_out0).
Lemma KS_urkA_ok : BG.kept_ok 48 LibSegJu_urkA.regs0 LibSegJu_urkA.regs_out0 KS_urkA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urkA_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10,1_v2#40#40,1,>X#37238#37::4Y,T,1#37268T,2_v2#40T,8v24T,9v26T,;v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urkA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkA] fx R M V urkA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkA] LibSegJu_urkA.regs0 LibSegJu_urkA.kn0 LibSegJu_urkA.BR LibSegJu_urkA.PSS LibSegJu_urkA.NX0 LibSegJu_urkA.F0 225848 LibSegJu_urkA.seg_sound_ax fx R M V urkA_conc_s. Qed.
Definition KS_urkB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkB.regs0 LibSegJu_urkB.regs_out0).
Lemma KS_urkB_ok : BG.kept_ok 48 LibSegJu_urkB.regs0 LibSegJu_urkB.regs_out0 KS_urkB = true. Proof. vm_compute. reflexivity. Qed.
Definition urkB_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#40S,8v24S,9v26S,:v21S,12v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10Mav26#,,1,7X#37268#37<;0Y,T,1#37284T,:+v24#18T,;v21T,<+v24#150T,13v21"%pstring.
Lemma urkB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkB] fx R M V urkB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkB] LibSegJu_urkB.regs0 LibSegJu_urkB.kn0 LibSegJu_urkB.BR LibSegJu_urkB.PSS LibSegJu_urkB.NX0 LibSegJu_urkB.F0 225896 LibSegJu_urkB.seg_sound_ax fx R M V urkB_conc_s. Qed.
Definition KS_urkE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkE.regs0 LibSegJu_urkE.regs_out0).
Lemma KS_urkE_ok : BG.kept_ok 48 LibSegJu_urkE.regs0 LibSegJu_urkE.regs_out0 KS_urkE = true. Proof. vm_compute. reflexivity. Qed.
Definition urkE_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#40S,8v24S,9v26S,:v21S,12v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10Mav26v27B#1v27#40,,1,5X#37268#370:<Y,T,1#372;0T,:v26T,;#<"%pstring.
Lemma urkE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkE] fx R M V urkE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkE] LibSegJu_urkE.regs0 LibSegJu_urkE.kn0 LibSegJu_urkE.BR LibSegJu_urkE.PSS LibSegJu_urkE.NX0 LibSegJu_urkE.F0 225896 LibSegJu_urkE.seg_sound_ax fx R M V urkE_conc_s. Qed.
Definition KS_urkF_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkF.regs0 LibSegJu_urkF.regs_out0).
Lemma KS_urkF_0_ok : BG.kept_ok 48 LibSegJu_urkF.regs0 LibSegJu_urkF.regs_out0 KS_urkF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urkF_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkF.regs0 LibSegJu_urkF.regs_out1).
Lemma KS_urkF_1_ok : BG.kept_ok 48 LibSegJu_urkF.regs0 LibSegJu_urkF.regs_out1 KS_urkF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition urkF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#40S,8v24S,9v26S,:v22S,;v23S,12v25S,13v21B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10,,2,6X#37284#37844Y,T,1#37294T,;v21T,14v22C%_v23v21p#2#40#1,6X#37284#370:<Y,1T,1#372;0T,:v26T,;#1D#1%_v23v21p#2#40"%pstring.
Lemma urkF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkF_0; KS_urkF_1] fx R M V urkF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkF_0; KS_urkF_1] LibSegJu_urkF.regs0 LibSegJu_urkF.kn0 LibSegJu_urkF.BR LibSegJu_urkF.PSS LibSegJu_urkF.NX0 LibSegJu_urkF.F0 225924 LibSegJu_urkF.seg_sound_ax fx R M V urkF_conc_s. Qed.
Definition KS_urkK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkK.regs0 LibSegJu_urkK.regs_out0).
Lemma KS_urkK_ok : BG.kept_ok 48 LibSegJu_urkK.regs0 LibSegJu_urkK.regs_out0 KS_urkK = true. Proof. vm_compute. reflexivity. Qed.
Definition urkK_conc_s := ",2:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#40S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10B#7???7?800040v25#7??????????8Hv25#8P_v2#40#40v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=,2_v2#40#10+v24#8#1,1,11X#372=4#372=0Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;#2T,<v24T,=v26T,>#34854T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#38v21Lb_v2#40v22"%pstring.
Lemma urkK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkK] fx R M V urkK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkK] LibSegJu_urkK.regs0 LibSegJu_urkK.kn0 LibSegJu_urkK.BR LibSegJu_urkK.PSS LibSegJu_urkK.NX0 LibSegJu_urkK.F0 226004 LibSegJu_urkK.seg_sound_ax fx R M V urkK_conc_s. Qed.
Definition KS_urkW_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkW.regs0 LibSegJu_urkW.regs_out0).
Lemma KS_urkW_0_ok : BG.kept_ok 48 LibSegJu_urkW.regs0 LibSegJu_urkW.regs_out0 KS_urkW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urkW_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkW.regs0 LibSegJu_urkW.regs_out1).
Lemma KS_urkW_1_ok : BG.kept_ok 48 LibSegJu_urkW.regs0 LibSegJu_urkW.regs_out1 KS_urkW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition urkW_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#40S,8v24S,9v26S,;v23S,12v25S,13v21S,14v22B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10,,2,2X#37294#372=4Y,,5X#37294#370:<Y,1T,1#372;0T,:v26T,;#7"%pstring.
Lemma urkW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkW_0; KS_urkW_1] fx R M V urkW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkW_0; KS_urkW_1] LibSegJu_urkW.regs0 LibSegJu_urkW.kn0 LibSegJu_urkW.BR LibSegJu_urkW.PSS LibSegJu_urkW.NX0 LibSegJu_urkW.F0 225940 LibSegJu_urkW.seg_sound_ax fx R M V urkW_conc_s. Qed.
Definition KS_urkZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urkZ.regs0 LibSegJu_urkZ.regs_out0).
Lemma KS_urkZ_ok : BG.kept_ok 48 LibSegJu_urkZ.regs0 LibSegJu_urkZ.regs_out0 KS_urkZ = true. Proof. vm_compute. reflexivity. Qed.
Definition urkZ_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#40S,8v24S,9v26S,12v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=I+v24#8#1,1+v24#8#1,1,:X#372;0#372=0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma urkZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urkZ] fx R M V urkZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urkZ] LibSegJu_urkZ.regs0 LibSegJu_urkZ.kn0 LibSegJu_urkZ.BR LibSegJu_urkZ.PSS LibSegJu_urkZ.NX0 LibSegJu_urkZ.F0 225968 LibSegJu_urkZ.seg_sound_ax fx R M V urkZ_conc_s. Qed.
End PMURKP.
