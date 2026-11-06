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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uscZ LibSegJu_uscS LibSegJu_uscH23 LibSegJu_uscHg LibSegJu_uscN LibSegJu_uscT.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSTUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uscZ : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uscZ.regs0 LibSegJu_uscZ.regs_out0).
Lemma KS_uscZ_ok : BG.kept_ok 52 LibSegJu_uscZ.regs0 LibSegJu_uscZ.regs_out0 KS_uscZ = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uscZ_conc_s := ",<A#v2p#2#40A#v21p#2#40S,2v2S,:v21S,<#B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18,2_v2#30#30+v21##2,1,6X#34488#34544Y,T,:_*-1v21#2T,;^#?#??????????????8Nb+v21#1#Nbv21#"%pstring.
Lemma uscZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uscZ] fx R M V uscZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uscZ] LibSegJu_uscZ.regs0 LibSegJu_uscZ.kn0 LibSegJu_uscZ.BR LibSegJu_uscZ.PSS LibSegJu_uscZ.NX0 LibSegJu_uscZ.F0 214152 LibSegJu_uscZ.seg_sound_ax fx R M V uscZ_conc_s. Qed.
Definition KS_uscS : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uscS.regs0 LibSegJu_uscS.regs_out0).
Lemma KS_uscS_ok : BG.kept_ok 52 LibSegJu_uscS.regs0 LibSegJu_uscS.regs_out0 KS_uscS = true. Proof. vm_compute. reflexivity. Qed.
Definition uscS_conc_s := ",10A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18B#1v22#16,2_v2#30#30+v21##1,1,10X#34488#::5;8Y,T,1#34518T,2_v2#30T,8v22T,9v23T,:+v21#1T,12v21T,13+v21#1Nbv21*#2v22Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uscS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uscS] fx R M V uscS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uscS] LibSegJu_uscS.regs0 LibSegJu_uscS.kn0 LibSegJu_uscS.BR LibSegJu_uscS.PSS LibSegJu_uscS.NX0 LibSegJu_uscS.F0 214152 LibSegJu_uscS.seg_sound_ax fx R M V uscS_conc_s. Qed.
Definition KS_uscH23 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uscH23.regs0 LibSegJu_uscH23.regs_out0).
Lemma KS_uscH23_ok : BG.kept_ok 52 LibSegJu_uscH23.regs0 LibSegJu_uscH23.regs_out0 KS_uscH23 = true. Proof. vm_compute. reflexivity. Qed.
Definition uscH23_conc_s := ",>A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<#17B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18,1_v2#30#30,1,10X#34488#:?0><Y,T,1#344?4T,2_v2#30T,8#17T,9v23T,:#1:T,;^#?#??????????????8T,12v21T,14#1:Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uscH23_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uscH23] fx R M V uscH23_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uscH23] LibSegJu_uscH23.regs0 LibSegJu_uscH23.kn0 LibSegJu_uscH23.BR LibSegJu_uscH23.PSS LibSegJu_uscH23.NX0 LibSegJu_uscH23.F0 214152 LibSegJu_uscH23.seg_sound_ax fx R M V uscH23_conc_s. Qed.
Definition KS_uscHg : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uscHg.regs0 LibSegJu_uscHg.regs_out0).
Lemma KS_uscHg_ok : BG.kept_ok 52 LibSegJu_uscHg.regs0 LibSegJu_uscHg.regs_out0 KS_uscHg = true. Proof. vm_compute. reflexivity. Qed.
Definition uscHg_conc_s := ",11A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18B#18v22#3??????B#18|v22#7#4000007,1_v2#30#30,1,10X#34488#:?0><Y,T,1#344?4T,2_v2#30T,8v22T,9v23T,:+*#8/v22#8#8T,;^#?#??????????????8T,12v21T,14+*#8/v22#8#8Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uscHg_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uscHg] fx R M V uscHg_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uscHg] LibSegJu_uscHg.regs0 LibSegJu_uscHg.kn0 LibSegJu_uscHg.BR LibSegJu_uscHg.PSS LibSegJu_uscHg.NX0 LibSegJu_uscHg.F0 214152 LibSegJu_uscHg.seg_sound_ax fx R M V uscHg_conc_s. Qed.
Definition KS_uscN : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uscN.regs0 LibSegJu_uscN.regs_out0).
Lemma KS_uscN_ok : BG.kept_ok 52 LibSegJu_uscN.regs0 LibSegJu_uscN.regs_out0 KS_uscN = true. Proof. vm_compute. reflexivity. Qed.
Definition uscN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#30S,8v22S,9v23S,:v24S,12v21S,14v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v21#7?????????>8Hv21#8P_v2#30#30v21#18Iv21#18B#17v22#3??????B#1:v25#4000008,1+v21##18,1,:X#344?4#::5;8Y,T,1#34518T,;v23T,<v22T,13v24T,14+v25#1Lb+v21#10v24Lb+v21#8v22Lbv21+v25#1"%pstring.
Lemma uscN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uscN] fx R M V uscN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uscN] LibSegJu_uscN.regs0 LibSegJu_uscN.kn0 LibSegJu_uscN.BR LibSegJu_uscN.PSS LibSegJu_uscN.NX0 LibSegJu_uscN.F0 214260 LibSegJu_uscN.seg_sound_ax fx R M V uscN_conc_s. Qed.
Definition KS_uscT : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uscT.regs0 LibSegJu_uscT.regs_out0).
Lemma KS_uscT_ok : BG.kept_ok 52 LibSegJu_uscT.regs0 LibSegJu_uscT.regs_out0 KS_uscT = true. Proof. vm_compute. reflexivity. Qed.
Definition uscT_conc_s := ",19A#v2p#2#40A#v22p#2#40A#v27p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#30S,8v22S,13v27B#7???7?800030v2#800000000000Hv2#10I_v2#30#30La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31B#1000v27#800000000000B#v22#3??????I+v27v22#1P_v2#30#30+v27v22#1,1++v27v22##1,1,;X#34518#34544Y,T,1v2<T,2v2T,8v2=T,9v2>T,:_*-1v27#1T,12v2?T,13v30T,14v31Nb+v22v27#"%pstring.
Lemma uscT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uscT] fx R M V uscT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uscT] LibSegJu_uscT.regs0 LibSegJu_uscT.kn0 LibSegJu_uscT.BR LibSegJu_uscT.PSS LibSegJu_uscT.NX0 LibSegJu_uscT.F0 214296 LibSegJu_uscT.seg_sound_ax fx R M V uscT_conc_s. Qed.
End PMSTUP.
