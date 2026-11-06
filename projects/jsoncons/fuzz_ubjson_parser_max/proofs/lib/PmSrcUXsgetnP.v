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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uxgA0 LibSegJu_uxgA1 LibSegJu_uxgA2 LibSegJu_uxgC1 LibSegJu_uxgC2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUXGP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uxgA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uxgA0.regs0 LibSegJu_uxgA0.regs_out0).
Lemma KS_uxgA0_ok : BG.kept_ok 48 LibSegJu_uxgA0.regs0 LibSegJu_uxgA0.regs_out0 KS_uxgA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uxgA0_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#;7120Lav24#;39?8La+v24#18v21La+v24#20v21La+v24#30#La+v24#58v21Ma+v24#60#8B#1000v21#800000000000,1_v2#50#50,1,10X#5<2:8#5<3;0Y,T,:#T,;^#?#???????????????T,<v21T,=v21Lb_v2#50#Lb_v2#48#5<340Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uxgA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uxgA0] fx R M V uxgA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uxgA0] LibSegJu_uxgA0.regs0 LibSegJu_uxgA0.kn0 LibSegJu_uxgA0.BR LibSegJu_uxgA0.PSS LibSegJu_uxgA0.NX0 LibSegJu_uxgA0.F0 377512 LibSegJu_uxgA0.seg_sound_ax fx R M V uxgA0_conc_s. Qed.
Definition KS_uxgA1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uxgA1.regs0 LibSegJu_uxgA1.regs_out0).
Lemma KS_uxgA1_ok : BG.kept_ok 48 LibSegJu_uxgA1.regs0 LibSegJu_uxgA1.regs_out0 KS_uxgA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uxgA1_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#;7120Lav24#;39?8La+v24#18v21La+v24#20+v21v23La+v24#30#La+v24#58+v21v23Ma+v24#60#8B#1000v21#800000000000B#1v23#4000,1_v2#50#50,1,16X#5<2:8#::5;8Y,T,1#5<37<T,2_v2#40T,8#T,9#4000T,:v25T,;v21T,<v23T,12v25T,13v24T,14v23T,15#7???????T,16^#?#???????????????Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uxgA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uxgA1] fx R M V uxgA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uxgA1] LibSegJu_uxgA1.regs0 LibSegJu_uxgA1.kn0 LibSegJu_uxgA1.BR LibSegJu_uxgA1.PSS LibSegJu_uxgA1.NX0 LibSegJu_uxgA1.F0 377512 LibSegJu_uxgA1.seg_sound_ax fx R M V uxgA1_conc_s. Qed.
Definition KS_uxgA2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uxgA2.regs0 LibSegJu_uxgA2.regs_out0).
Lemma KS_uxgA2_ok : BG.kept_ok 48 LibSegJu_uxgA2.regs0 LibSegJu_uxgA2.regs_out0 KS_uxgA2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uxgA2_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#;7120Lav24#;39?8La+v24#18v21La+v24#20+v21v23La+v24#30#La+v24#58+v21v23Ma+v24#60#8B#1000v21#800000000000B#4001v23#8000000,1_v2#50#50,1,15X#5<2:8#::5;8Y,T,1#5<37<T,2_v2#40T,8#T,9#4000T,:v25T,;v21T,12v25T,13v24T,14#4000T,15#7???????T,16^#?#???????????????Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uxgA2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uxgA2] fx R M V uxgA2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uxgA2] LibSegJu_uxgA2.regs0 LibSegJu_uxgA2.kn0 LibSegJu_uxgA2.BR LibSegJu_uxgA2.PSS LibSegJu_uxgA2.NX0 LibSegJu_uxgA2.F0 377512 LibSegJu_uxgA2.seg_sound_ax fx R M V uxgA2_conc_s. Qed.
Definition KS_uxgC1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uxgC1.regs0 LibSegJu_uxgC1.regs_out0).
Lemma KS_uxgC1_ok : BG.kept_ok 48 LibSegJu_uxgC1.regs0 LibSegJu_uxgC1.regs_out0 KS_uxgC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uxgC1_conc_s := ",2:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8#S,9#4000S,13v24S,14#4000S,15#7???????S,16^#?#???????????????B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#;7120Lav24#;39?8La+v24#18v21La+v24#20v22La+v24#30#La+v24#58v22Ma+v24#60#8I+v24#18#8La_v2#8v25La_v2#10v26La_v2#18v27La_v2#20v28La_v2#28v29La_v2#30v2:La_v2#38v2;La_v2#40v2<B#1000v21#800000000000,2_v2#50#50+v24#18#8,1,16X#5<37<#5<3;0Y,T,1v25T,2v2T,8v26T,9v27T,:#4000T,;v21T,12v28T,13v29T,14v2:T,15v2;T,16v2<Lb+v24#18+v21#4000Lb_v2#8v25Lb_v2#10v26Lb_v2#18v27Lb_v2#20v28Lb_v2#28v29Lb_v2#30v2:Lb_v2#38v2;Lb_v2#40v2<"%pstring.
Lemma uxgC1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uxgC1] fx R M V uxgC1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uxgC1] LibSegJu_uxgC1.regs0 LibSegJu_uxgC1.kn0 LibSegJu_uxgC1.BR LibSegJu_uxgC1.PSS LibSegJu_uxgC1.NX0 LibSegJu_uxgC1.F0 377724 LibSegJu_uxgC1.seg_sound_ax fx R M V uxgC1_conc_s. Qed.
Definition KS_uxgC2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uxgC2.regs0 LibSegJu_uxgC2.regs_out0).
Lemma KS_uxgC2_ok : BG.kept_ok 48 LibSegJu_uxgC2.regs0 LibSegJu_uxgC2.regs_out0 KS_uxgC2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uxgC2_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8#S,9#4000S,13v24S,14v23S,15#7???????S,16^#?#???????????????B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#;7120Lav24#;39?8La+v24#18v21La+v24#20+v21v23La+v24#30#La+v24#58+v21v23Ma+v24#60#8I+v24#18#8La_v2#8v25La_v2#10v26La_v2#18v27La_v2#20v28La_v2#28v29La_v2#30v2:La_v2#38v2;La_v2#40v2<B#1000v21#800000000000B#1v23#3???,2_v2#50#50+v24#18#8,1,1:X#5<37<#5<3;0Y,T,1v25T,2v2T,8v26T,9v27T,:v23T,;^#?#???????????????T,<+v21v23T,=+v21v23T,12v28T,13v29T,14v2:T,15v2;T,16v2<Lb_v2#50v23Lb_v2#48#5<340Lb+v24#18+v21v23Lb_v2#8v25Lb_v2#10v26Lb_v2#18v27Lb_v2#20v28Lb_v2#28v29Lb_v2#30v2:Lb_v2#38v2;Lb_v2#40v2<"%pstring.
Lemma uxgC2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uxgC2] fx R M V uxgC2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uxgC2] LibSegJu_uxgC2.regs0 LibSegJu_uxgC2.kn0 LibSegJu_uxgC2.BR LibSegJu_uxgC2.PSS LibSegJu_uxgC2.NX0 LibSegJu_uxgC2.F0 377724 LibSegJu_uxgC2.seg_sound_ax fx R M V uxgC2_conc_s. Qed.
End PMUXGP.
