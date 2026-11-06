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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_hnA LibSegJs_hnB LibSegJs_hnC LibSegJs_hnD LibSegJs_hnE LibSegJs_hnF LibSegJs_hnG LibSegJs_hnHs LibSegJs_hnHl LibSegJs_hnI LibSegJs_hnJs LibSegJs_hnJl LibSegJs_hnK LibSegJs_hnL LibSegJs_hnMs LibSegJs_hnMl LibSegJs_hnN.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSHP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_hnA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnA.regs0 LibSegJs_hnA.regs_out0).
Lemma KS_hnA_ok : BG.kept_ok 48 LibSegJs_hnA.regs0 LibSegJs_hnA.regs_out0 KS_hnA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition hnA_conc_s := ",5A#v2p#2#40S,2v2B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,1_v2#10#10,1,9X#3404<#3422<Y,T,1#34068T,2_v2#2?0T,:_v2#28U,;,:U,<,;Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma hnA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnA] fx R M V hnA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnA] LibSegJs_hnA.regs0 LibSegJs_hnA.kn0 LibSegJs_hnA.BR LibSegJs_hnA.PSS LibSegJs_hnA.NX0 LibSegJs_hnA.F0 213068 LibSegJs_hnA.seg_sound_ax fx R M V hnA_conc_s. Qed.
Definition KS_hnB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnB.regs0 LibSegJs_hnB.regs_out0).
Lemma KS_hnB_ok : BG.kept_ok 48 LibSegJs_hnB.regs0 LibSegJs_hnB.regs_out0 KS_hnB = true. Proof. vm_compute. reflexivity. Qed.
Definition hnB_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,,1,6X#34068#342>4Y,T,1#34078T,:_v2#138T,;_v2#28T,<#8"%pstring.
Lemma hnB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnB] fx R M V hnB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnB] LibSegJs_hnB.regs0 LibSegJs_hnB.kn0 LibSegJs_hnB.BR LibSegJs_hnB.PSS LibSegJs_hnB.NX0 LibSegJs_hnB.F0 213096 LibSegJs_hnB.seg_sound_ax fx R M V hnB_conc_s. Qed.
Definition KS_hnC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnC.regs0 LibSegJs_hnC.regs_out0).
Lemma KS_hnC_ok : BG.kept_ok 48 LibSegJs_hnC.regs0 LibSegJs_hnC.regs_out0 KS_hnC = true. Proof. vm_compute. reflexivity. Qed.
Definition hnC_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,2_v2#2>8#20_v2#140#8,1,=X#34078#355?8Y,T,1#340<4T,:_v2#2<8T,;_v2#138T,<_v2#2>8T,=_v2#2>9Mb_v2#2=0#400Mb_v2#2<<#Lb_v2#2=8#:?368Lb_v2#2>0#1000000Lb_v2#2>8#:?340Lb_v2#140#:?1>8"%pstring.
Lemma hnC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnC] fx R M V hnC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnC] LibSegJs_hnC.regs0 LibSegJs_hnC.kn0 LibSegJs_hnC.BR LibSegJs_hnC.PSS LibSegJs_hnC.NX0 LibSegJs_hnC.F0 213112 LibSegJs_hnC.seg_sound_ax fx R M V hnC_conc_s. Qed.
Definition KS_hnD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnD.regs0 LibSegJs_hnD.regs_out0).
Lemma KS_hnD_ok : BG.kept_ok 48 LibSegJs_hnD.regs0 LibSegJs_hnD.regs_out0 KS_hnD = true. Proof. vm_compute. reflexivity. Qed.
Definition hnD_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,2_v2#148#8_v2#2>8#4,1,6X#340<4#59?60Y,T,1#340=4T,:_v2#140Mb_v2#2>8#Lb_v2#148_v2#140"%pstring.
Lemma hnD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnD] fx R M V hnD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnD] LibSegJs_hnD.regs0 LibSegJs_hnD.kn0 LibSegJs_hnD.BR LibSegJs_hnD.PSS LibSegJs_hnD.NX0 LibSegJs_hnD.F0 213188 LibSegJs_hnD.seg_sound_ax fx R M V hnD_conc_s. Qed.
Definition KS_hnE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnE.regs0 LibSegJs_hnE.regs_out0).
Lemma KS_hnE_ok : BG.kept_ok 48 LibSegJs_hnE.regs0 LibSegJs_hnE.regs_out0 KS_hnE = true. Proof. vm_compute. reflexivity. Qed.
Definition hnE_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,1_v2#2>0#8,1,5X#340=4#35984Y,T,1#340>0T,:_v2#2<8Lb_v2#2>0r:"%pstring.
Lemma hnE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnE] fx R M V hnE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnE] LibSegJs_hnE.regs0 LibSegJs_hnE.kn0 LibSegJs_hnE.BR LibSegJs_hnE.PSS LibSegJs_hnE.NX0 LibSegJs_hnE.F0 213204 LibSegJs_hnE.seg_sound_ax fx R M V hnE_conc_s. Qed.
Definition KS_hnF : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnF.regs0 LibSegJs_hnF.regs_out0).
Lemma KS_hnF_ok : BG.kept_ok 48 LibSegJs_hnF.regs0 LibSegJs_hnF.regs_out0 KS_hnF = true. Proof. vm_compute. reflexivity. Qed.
Definition hnF_conc_s := ",7A#v2p#2#40A#v28p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0La_v2#148v28,,1,6X#340>0#35::<Y,T,1#340?0T,:_v2#2<8T,;v28T,<_v2#2>8"%pstring.
Lemma hnF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnF] fx R M V hnF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnF] LibSegJs_hnF.regs0 LibSegJs_hnF.kn0 LibSegJs_hnF.BR LibSegJs_hnF.PSS LibSegJs_hnF.NX0 LibSegJs_hnF.F0 213216 LibSegJs_hnF.seg_sound_ax fx R M V hnF_conc_s. Qed.
Definition KS_hnG : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnG.regs0 LibSegJs_hnG.regs_out0).
Lemma KS_hnG_ok : BG.kept_ok 48 LibSegJs_hnG.regs0 LibSegJs_hnG.regs_out0 KS_hnG = true. Proof. vm_compute. reflexivity. Qed.
Definition hnG_conc_s := ",;A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0La_v2#160v21La_v2#150v22B#1000v21#800000000000Hv21#2,2_v2#2<8#8_v2#158#8,1,7X#340?0#54400Y,T,1#34114T,:v21T,;+*-1v21v22Lb_v2#158v21Lb_v2#2<8#:?3<0"%pstring.
Lemma hnG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnG] fx R M V hnG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnG] LibSegJs_hnG.regs0 LibSegJs_hnG.kn0 LibSegJs_hnG.BR LibSegJs_hnG.PSS LibSegJs_hnG.NX0 LibSegJs_hnG.F0 213232 LibSegJs_hnG.seg_sound_ax fx R M V hnG_conc_s. Qed.
Definition KS_hnHs : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnHs.regs0 LibSegJs_hnHs.regs_out0).
Lemma KS_hnHs_ok : BG.kept_ok 48 LibSegJs_hnHs.regs0 LibSegJs_hnHs.regs_out0 KS_hnHs = true. Proof. vm_compute. reflexivity. Qed.
Definition hnHs_conc_s := ",9A#v2p#2#40A#v23p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#178v23B#v23#??Fv23#f,,1,4X#34114#34?<<Y,T,1#34138T,:_v2#2;0"%pstring.
Lemma hnHs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnHs] fx R M V hnHs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnHs] LibSegJs_hnHs.regs0 LibSegJs_hnHs.kn0 LibSegJs_hnHs.BR LibSegJs_hnHs.PSS LibSegJs_hnHs.NX0 LibSegJs_hnHs.F0 213268 LibSegJs_hnHs.seg_sound_ax fx R M V hnHs_conc_s. Qed.
Definition KS_hnHl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnHl.regs0 LibSegJs_hnHl.regs_out0).
Lemma KS_hnHl_ok : BG.kept_ok 48 LibSegJs_hnHl.regs0 LibSegJs_hnHl.regs_out0 KS_hnHl = true. Proof. vm_compute. reflexivity. Qed.
Definition hnHl_conc_s := ",<A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#178v23B#v23#??Fv23#tJa_v2#177#7La_v2#168v25,,1,4X#34114#54400Y,T,1#34130T,:v25"%pstring.
Lemma hnHl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnHl] fx R M V hnHl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnHl] LibSegJs_hnHl.regs0 LibSegJs_hnHl.kn0 LibSegJs_hnHl.BR LibSegJs_hnHl.PSS LibSegJs_hnHl.NX0 LibSegJs_hnHl.F0 213268 LibSegJs_hnHl.seg_sound_ax fx R M V hnHl_conc_s. Qed.
Definition KS_hnI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnI.regs0 LibSegJs_hnI.regs_out0).
Lemma KS_hnI_ok : BG.kept_ok 48 LibSegJs_hnI.regs0 LibSegJs_hnI.regs_out0 KS_hnI = true. Proof. vm_compute. reflexivity. Qed.
Definition hnI_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,,1,4X#34130#34?<<Y,T,1#34138T,:_v2#2;0"%pstring.
Lemma hnI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnI] fx R M V hnI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnI] LibSegJs_hnI.regs0 LibSegJs_hnI.kn0 LibSegJs_hnI.BR LibSegJs_hnI.PSS LibSegJs_hnI.NX0 LibSegJs_hnI.F0 213296 LibSegJs_hnI.seg_sound_ax fx R M V hnI_conc_s. Qed.
Definition KS_hnJs : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnJs.regs0 LibSegJs_hnJs.regs_out0).
Lemma KS_hnJs_ok : BG.kept_ok 48 LibSegJs_hnJs.regs0 LibSegJs_hnJs.regs_out0 KS_hnJs = true. Proof. vm_compute. reflexivity. Qed.
Definition hnJs_conc_s := ",:A#v2p#2#40A#v23p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0O#10000#;60=0Na_v2#>8v23B#v23#??Fv23#f,3_v2#138#8_v2#128#8_v2#<0#8,1,:X#34138#7?994Y,T,1#341:0T,8#;2:=0T,:_v2#120T,;#T,<#;5158Lb_v2#128#;2928Lb_v2#<0#;2:<0Lb_v2#138#;2:98"%pstring.
Lemma hnJs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnJs] fx R M V hnJs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnJs] LibSegJs_hnJs.regs0 LibSegJs_hnJs.kn0 LibSegJs_hnJs.BR LibSegJs_hnJs.PSS LibSegJs_hnJs.NX0 LibSegJs_hnJs.F0 213304 LibSegJs_hnJs.seg_sound_ax fx R M V hnJs_conc_s. Qed.
Definition KS_hnJl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnJl.regs0 LibSegJs_hnJl.regs_out0).
Lemma KS_hnJl_ok : BG.kept_ok 48 LibSegJs_hnJl.regs0 LibSegJs_hnJl.regs_out0 KS_hnJl = true. Proof. vm_compute. reflexivity. Qed.
Definition hnJl_conc_s := ",=A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0O#10000#;60=0Na_v2#>8v23B#v23#??Fv23#tJa_v2#>7#7La_v2#=8v25,3_v2#138#8_v2#128#8_v2#<0#8,1,9X#34138#54400Y,T,1#34188T,8#;2:=0T,:v25T,<#;5158Lb_v2#128#;29:8Lb_v2#<0#;2:<0Lb_v2#138#;2:98"%pstring.
Lemma hnJl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnJl] fx R M V hnJl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnJl] LibSegJs_hnJl.regs0 LibSegJs_hnJl.kn0 LibSegJs_hnJl.BR LibSegJs_hnJl.PSS LibSegJs_hnJl.NX0 LibSegJs_hnJl.F0 213304 LibSegJs_hnJl.seg_sound_ax fx R M V hnJl_conc_s. Qed.
Definition KS_hnK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnK.regs0 LibSegJs_hnK.regs_out0).
Lemma KS_hnK_ok : BG.kept_ok 48 LibSegJs_hnK.regs0 LibSegJs_hnK.regs_out0 KS_hnK = true. Proof. vm_compute. reflexivity. Qed.
Definition hnK_conc_s := ",6A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0O#10000#;60=0,1_v2#128#8,1,5X#34188#7?994Y,T,1#341:0T,:_v2#120Lb_v2#128#;2928"%pstring.
Lemma hnK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnK] fx R M V hnK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnK] LibSegJs_hnK.regs0 LibSegJs_hnK.kn0 LibSegJs_hnK.BR LibSegJs_hnK.PSS LibSegJs_hnK.NX0 LibSegJs_hnK.F0 213384 LibSegJs_hnK.seg_sound_ax fx R M V hnK_conc_s. Qed.
Definition KS_hnL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnL.regs0 LibSegJs_hnL.regs_out0).
Lemma KS_hnL_ok : BG.kept_ok 48 LibSegJs_hnL.regs0 LibSegJs_hnL.regs_out0 KS_hnL = true. Proof. vm_compute. reflexivity. Qed.
Definition hnL_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,,1,5X#341:0#5;1;0Y,T,1#341;4T,:_v2#<0T,;+r8#8"%pstring.
Lemma hnL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnL] fx R M V hnL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnL] LibSegJs_hnL.regs0 LibSegJs_hnL.kn0 LibSegJs_hnL.BR LibSegJs_hnL.PSS LibSegJs_hnL.NX0 LibSegJs_hnL.F0 213408 LibSegJs_hnL.seg_sound_ax fx R M V hnL_conc_s. Qed.
Definition KS_hnMs : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnMs.regs0 LibSegJs_hnMs.regs_out0).
Lemma KS_hnMs_ok : BG.kept_ok 48 LibSegJs_hnMs.regs0 LibSegJs_hnMs.regs_out0 KS_hnMs = true. Proof. vm_compute. reflexivity. Qed.
Definition hnMs_conc_s := ",=A#v2p#2#40A#v23p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#28v23B#v23#??Fv23#fLa_v2#8v26La_v2#10v27,,1,6X#341;4#341>0Y,T,1v26T,2v2T,8v27T,:#"%pstring.
Lemma hnMs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnMs] fx R M V hnMs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnMs] LibSegJs_hnMs.regs0 LibSegJs_hnMs.kn0 LibSegJs_hnMs.BR LibSegJs_hnMs.PSS LibSegJs_hnMs.NX0 LibSegJs_hnMs.F0 213428 LibSegJs_hnMs.seg_sound_ax fx R M V hnMs_conc_s. Qed.
Definition KS_hnMl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnMl.regs0 LibSegJs_hnMl.regs_out0).
Lemma KS_hnMl_ok : BG.kept_ok 48 LibSegJs_hnMl.regs0 LibSegJs_hnMl.regs_out0 KS_hnMl = true. Proof. vm_compute. reflexivity. Qed.
Definition hnMl_conc_s := ",<A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#28v23B#v23#??Fv23#tJa_v2#27#7La_v2#18v25,,1,4X#341;4#54400Y,T,1#341=0T,:v25"%pstring.
Lemma hnMl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnMl] fx R M V hnMl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnMl] LibSegJs_hnMl.regs0 LibSegJs_hnMl.kn0 LibSegJs_hnMl.BR LibSegJs_hnMl.PSS LibSegJs_hnMl.NX0 LibSegJs_hnMl.F0 213428 LibSegJs_hnMl.seg_sound_ax fx R M V hnMl_conc_s. Qed.
Definition KS_hnN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_hnN.regs0 LibSegJs_hnN.regs_out0).
Lemma KS_hnN_ok : BG.kept_ok 48 LibSegJs_hnN.regs0 LibSegJs_hnN.regs_out0 KS_hnN = true. Proof. vm_compute. reflexivity. Qed.
Definition hnN_conc_s := ",9A#v2p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0La_v2#8v26La_v2#10v27,,1,6X#341=0#341>0Y,T,1v26T,2v2T,8v27T,:#"%pstring.
Lemma hnN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_hnN] fx R M V hnN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_hnN] LibSegJs_hnN.regs0 LibSegJs_hnN.kn0 LibSegJs_hnN.BR LibSegJs_hnN.PSS LibSegJs_hnN.NX0 LibSegJs_hnN.F0 213456 LibSegJs_hnN.seg_sound_ax fx R M V hnN_conc_s. Qed.
End PMSHP.
