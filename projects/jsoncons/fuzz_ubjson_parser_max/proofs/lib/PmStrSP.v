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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_scZ LibSegJs_scS LibSegJs_scH23 LibSegJs_scHg LibSegJs_scN LibSegJs_scT.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSTP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_scZ : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_scZ.regs0 LibSegJs_scZ.regs_out0).
Lemma KS_scZ_ok : BG.kept_ok 52 LibSegJs_scZ.regs0 LibSegJs_scZ.regs_out0 KS_scZ = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition scZ_conc_s := ",<A#v2p#2#40A#v21p#2#40S,2v2S,:v21S,<#B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18,2_v2#30#30+v21##2,1,6X#3422<#342=<Y,T,:#T,;^#?#??????????????8Nb+v21#1#Nbv21#"%pstring.
Lemma scZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_scZ] fx R M V scZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_scZ] LibSegJs_scZ.regs0 LibSegJs_scZ.kn0 LibSegJs_scZ.BR LibSegJs_scZ.PSS LibSegJs_scZ.NX0 LibSegJs_scZ.F0 213548 LibSegJs_scZ.seg_sound_ax fx R M V scZ_conc_s. Qed.
Definition KS_scS : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_scS.regs0 LibSegJs_scS.regs_out0).
Lemma KS_scS_ok : BG.kept_ok 52 LibSegJs_scS.regs0 LibSegJs_scS.regs_out0 KS_scS = true. Proof. vm_compute. reflexivity. Qed.
Definition scS_conc_s := ",10A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18B#1v22#16,2_v2#30#30+v21##1,1,10X#3422<#:9564Y,T,1#342;8T,2_v2#30T,8v22T,9v23T,:+v21#1T,12v21T,13+v21#1Nbv21*#2v22Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma scS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_scS] fx R M V scS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_scS] LibSegJs_scS.regs0 LibSegJs_scS.kn0 LibSegJs_scS.BR LibSegJs_scS.PSS LibSegJs_scS.NX0 LibSegJs_scS.F0 213548 LibSegJs_scS.seg_sound_ax fx R M V scS_conc_s. Qed.
Definition KS_scH23 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_scH23.regs0 LibSegJs_scH23.regs_out0).
Lemma KS_scH23_ok : BG.kept_ok 52 LibSegJs_scH23.regs0 LibSegJs_scH23.regs_out0 KS_scH23 = true. Proof. vm_compute. reflexivity. Qed.
Definition scH23_conc_s := ",>A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<#17B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18,1_v2#30#30,1,10X#3422<#:>098Y,T,1#34294T,2_v2#30T,8#17T,9v23T,:#1:T,;^#?#??????????????8T,12v21T,14#1:Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma scH23_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_scH23] fx R M V scH23_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_scH23] LibSegJs_scH23.regs0 LibSegJs_scH23.kn0 LibSegJs_scH23.BR LibSegJs_scH23.PSS LibSegJs_scH23.NX0 LibSegJs_scH23.F0 213548 LibSegJs_scH23.seg_sound_ax fx R M V scH23_conc_s. Qed.
Definition KS_scHg : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_scHg.regs0 LibSegJs_scHg.regs_out0).
Lemma KS_scHg_ok : BG.kept_ok 52 LibSegJs_scHg.regs0 LibSegJs_scHg.regs_out0 KS_scHg = true. Proof. vm_compute. reflexivity. Qed.
Definition scHg_conc_s := ",11A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18B#18v22#3??????B#18|v22#7#4000007,1_v2#30#30,1,10X#3422<#:>098Y,T,1#34294T,2_v2#30T,8v22T,9v23T,:+*#8/v22#8#8T,;^#?#??????????????8T,12v21T,14+*#8/v22#8#8Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma scHg_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_scHg] fx R M V scHg_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_scHg] LibSegJs_scHg.regs0 LibSegJs_scHg.kn0 LibSegJs_scHg.BR LibSegJs_scHg.PSS LibSegJs_scHg.NX0 LibSegJs_scHg.F0 213548 LibSegJs_scHg.seg_sound_ax fx R M V scHg_conc_s. Qed.
Definition KS_scN : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_scN.regs0 LibSegJs_scN.regs_out0).
Lemma KS_scN_ok : BG.kept_ok 52 LibSegJs_scN.regs0 LibSegJs_scN.regs_out0 KS_scN = true. Proof. vm_compute. reflexivity. Qed.
Definition scN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#30S,8v22S,9v23S,:v24S,12v21S,14v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18B#17v22#3??????B#1:v25#4000008,1+v21##18,1,:X#34294#:9564Y,T,1#342;8T,;v23T,<v22T,13v24T,14+v25#1Lb+v21#10v24Lb+v21#8v22Lbv21+v25#1"%pstring.
Lemma scN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_scN] fx R M V scN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_scN] LibSegJs_scN.regs0 LibSegJs_scN.kn0 LibSegJs_scN.BR LibSegJs_scN.PSS LibSegJs_scN.NX0 LibSegJs_scN.F0 213652 LibSegJs_scN.seg_sound_ax fx R M V scN_conc_s. Qed.
Definition KS_scT : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_scT.regs0 LibSegJs_scT.regs_out0).
Lemma KS_scT_ok : BG.kept_ok 52 LibSegJs_scT.regs0 LibSegJs_scT.regs_out0 KS_scT = true. Proof. vm_compute. reflexivity. Qed.
Definition scT_conc_s := ",19A#v2p#2#40A#v22p#2#40A#v27p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#30S,8v22S,13v27B#7???7?800030v2#800000000000Hv2#10I_v2#30#30La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31B#1000v27#800000000000B#v22#3??????I+v27v22#1P_v2#30#30+v27v22#1,1++v27v22##1,1,:X#342;8#342=<Y,T,1v2<T,2v2T,8v2=T,9v2>T,12v2?T,13v30T,14v31Nb+v22v27#"%pstring.
Lemma scT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_scT] fx R M V scT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_scT] LibSegJs_scT.regs0 LibSegJs_scT.kn0 LibSegJs_scT.BR LibSegJs_scT.PSS LibSegJs_scT.NX0 LibSegJs_scT.F0 213688 LibSegJs_scT.seg_sound_ax fx R M V scT_conc_s. Qed.
End PMSTP.
