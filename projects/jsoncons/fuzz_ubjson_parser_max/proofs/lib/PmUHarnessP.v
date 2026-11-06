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
BigLinkBase BigLinkGlueUb0 L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_huA LibSegJu_huB LibSegJu_huC LibSegJu_huD LibSegJu_huE LibSegJu_huG LibSegJu_huHs LibSegJu_huHl LibSegJu_huI LibSegJu_huJs LibSegJu_huJl LibSegJu_huK LibSegJu_huL LibSegJu_huMs LibSegJu_huMl LibSegJu_huN.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUHP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_huA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huA.regs0 LibSegJu_huA.regs_out0).
Lemma KS_huA_ok : BG.kept_ok 48 LibSegJu_huA.regs0 LibSegJu_huA.regs_out0 KS_huA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition huA_conc_s := ",5A#v2p#2#40S,2v2B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,1_v2#10#10,1,9X#342;<#34488Y,T,1#342=8T,2_v2#2?0T,:_v2#28U,;,:U,<,;Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma huA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huA] fx R M V huA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huA] LibSegJu_huA.regs0 LibSegJu_huA.kn0 LibSegJu_huA.BR LibSegJu_huA.PSS LibSegJu_huA.NX0 LibSegJu_huA.F0 213692 LibSegJu_huA.seg_sound_ax fx R M V huA_conc_s. Qed.
Definition KS_huB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huB.regs0 LibSegJu_huB.regs_out0).
Lemma KS_huB_ok : BG.kept_ok 48 LibSegJu_huB.regs0 LibSegJu_huB.regs_out0 KS_huB = true. Proof. vm_compute. reflexivity. Qed.
Definition huB_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,,1,6X#342=8#34550Y,T,1#342>8T,:_v2#138T,;_v2#28T,<#8"%pstring.
Lemma huB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huB] fx R M V huB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huB] LibSegJu_huB.regs0 LibSegJu_huB.kn0 LibSegJu_huB.BR LibSegJu_huB.PSS LibSegJu_huB.NX0 LibSegJu_huB.F0 213720 LibSegJu_huB.seg_sound_ax fx R M V huB_conc_s. Qed.
Definition KS_huC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huC.regs0 LibSegJu_huC.regs_out0).
Lemma KS_huC_ok : BG.kept_ok 48 LibSegJu_huC.regs0 LibSegJu_huC.regs_out0 KS_huC = true. Proof. vm_compute. reflexivity. Qed.
Definition huC_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,2_v2#2>8#20_v2#140#8,1,=X#342>8#35>;<Y,T,1#34334T,:_v2#2<8T,;_v2#138T,<_v2#2>8T,=_v2#2>9Mb_v2#2=0#400Mb_v2#2<<#Lb_v2#2=8#;03;8Lb_v2#2>0#1000000Lb_v2#2>8#;0390Lb_v2#140#;0238"%pstring.
Lemma huC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huC] fx R M V huC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huC] LibSegJu_huC.regs0 LibSegJu_huC.kn0 LibSegJu_huC.BR LibSegJu_huC.PSS LibSegJu_huC.NX0 LibSegJu_huC.F0 213736 LibSegJu_huC.seg_sound_ax fx R M V huC_conc_s. Qed.
Definition KS_huD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huD.regs0 LibSegJu_huD.regs_out0).
Lemma KS_huD_ok : BG.kept_ok 48 LibSegJu_huD.regs0 LibSegJu_huD.regs_out0 KS_huD = true. Proof. vm_compute. reflexivity. Qed.
Definition huD_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,2_v2#148#8_v2#2>8#4,1,6X#34334#5:?;4Y,T,1#34344T,:_v2#140Mb_v2#2>8#Lb_v2#148_v2#140"%pstring.
Lemma huD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huD] fx R M V huD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huD] LibSegJu_huD.regs0 LibSegJu_huD.kn0 LibSegJu_huD.BR LibSegJu_huD.PSS LibSegJu_huD.NX0 LibSegJu_huD.F0 213812 LibSegJu_huD.seg_sound_ax fx R M V huD_conc_s. Qed.
Definition KS_huE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huE.regs0 LibSegJu_huE.regs_out0).
Lemma KS_huE_ok : BG.kept_ok 48 LibSegJu_huE.regs0 LibSegJu_huE.regs_out0 KS_huE = true. Proof. vm_compute. reflexivity. Qed.
Definition huE_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,1_v2#2>0#8,1,6X#34344#34664Y,T,1#34354T,:_v2#2<8T,;_v2#2>8Lb_v2#2>0r:"%pstring.
Lemma huE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huE] fx R M V huE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huE] LibSegJu_huE.regs0 LibSegJu_huE.kn0 LibSegJu_huE.BR LibSegJu_huE.PSS LibSegJu_huE.NX0 LibSegJu_huE.F0 213828 LibSegJu_huE.seg_sound_ax fx R M V huE_conc_s. Qed.
Definition KS_huG : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huG.regs0 LibSegJu_huG.regs_out0).
Lemma KS_huG_ok : BG.kept_ok 48 LibSegJu_huG.regs0 LibSegJu_huG.regs_out0 KS_huG = true. Proof. vm_compute. reflexivity. Qed.
Definition huG_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,2_v2#2<8#8_v2#2>8#8,1,6X#34354#35928Y,T,1#34370T,:_v2#2>8Lb_v2#2>8_v2#160Lb_v2#2<8#;0410"%pstring.
Lemma huG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huG] fx R M V huG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huG] LibSegJu_huG.regs0 LibSegJu_huG.kn0 LibSegJu_huG.BR LibSegJu_huG.PSS LibSegJu_huG.NX0 LibSegJu_huG.F0 213844 LibSegJu_huG.seg_sound_ax fx R M V huG_conc_s. Qed.
Definition KS_huHs : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huHs.regs0 LibSegJu_huHs.regs_out0).
Lemma KS_huHs_ok : BG.kept_ok 48 LibSegJu_huHs.regs0 LibSegJu_huHs.regs_out0 KS_huHs = true. Proof. vm_compute. reflexivity. Qed.
Definition huHs_conc_s := ",9A#v2p#2#40A#v23p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#178v23B#v23#??Fv23#f,,1,4X#34370#357?4Y,T,1#34394T,:_v2#2;0"%pstring.
Lemma huHs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huHs] fx R M V huHs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huHs] LibSegJu_huHs.regs0 LibSegJu_huHs.kn0 LibSegJu_huHs.BR LibSegJu_huHs.PSS LibSegJu_huHs.NX0 LibSegJu_huHs.F0 213872 LibSegJu_huHs.seg_sound_ax fx R M V huHs_conc_s. Qed.
Definition KS_huHl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huHl.regs0 LibSegJu_huHl.regs_out0).
Lemma KS_huHl_ok : BG.kept_ok 48 LibSegJu_huHl.regs0 LibSegJu_huHl.regs_out0 KS_huHl = true. Proof. vm_compute. reflexivity. Qed.
Definition huHl_conc_s := ",<A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#178v23B#v23#??Fv23#tJa_v2#177#7La_v2#168v25,,1,4X#34370#55454Y,T,1#3438<T,:v25"%pstring.
Lemma huHl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huHl] fx R M V huHl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huHl] LibSegJu_huHl.regs0 LibSegJu_huHl.kn0 LibSegJu_huHl.BR LibSegJu_huHl.PSS LibSegJu_huHl.NX0 LibSegJu_huHl.F0 213872 LibSegJu_huHl.seg_sound_ax fx R M V huHl_conc_s. Qed.
Definition KS_huI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huI.regs0 LibSegJu_huI.regs_out0).
Lemma KS_huI_ok : BG.kept_ok 48 LibSegJu_huI.regs0 LibSegJu_huI.regs_out0 KS_huI = true. Proof. vm_compute. reflexivity. Qed.
Definition huI_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,,1,4X#3438<#357?4Y,T,1#34394T,:_v2#2;0"%pstring.
Lemma huI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huI] fx R M V huI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huI] LibSegJu_huI.regs0 LibSegJu_huI.kn0 LibSegJu_huI.BR LibSegJu_huI.PSS LibSegJu_huI.NX0 LibSegJu_huI.F0 213900 LibSegJu_huI.seg_sound_ax fx R M V huI_conc_s. Qed.
Definition KS_huJs : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huJs.regs0 LibSegJu_huJs.regs_out0).
Lemma KS_huJs_ok : BG.kept_ok 48 LibSegJu_huJs.regs0 LibSegJu_huJs.regs_out0 KS_huJs = true. Proof. vm_compute. reflexivity. Qed.
Definition huJs_conc_s := ",:A#v2p#2#40A#v23p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0O#10000#;7120Na_v2#>8v23B#v23#??Fv23#f,3_v2#138#8_v2#128#8_v2#<0#8,1,:X#34394#809>8Y,T,1#343?<T,8#;3;20T,:_v2#120T,;#T,<#;63;4Lb_v2#128#;3978Lb_v2#<0#;3;10Lb_v2#138#;3:>8"%pstring.
Lemma huJs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huJs] fx R M V huJs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huJs] LibSegJu_huJs.regs0 LibSegJu_huJs.kn0 LibSegJu_huJs.BR LibSegJu_huJs.PSS LibSegJu_huJs.NX0 LibSegJu_huJs.F0 213908 LibSegJu_huJs.seg_sound_ax fx R M V huJs_conc_s. Qed.
Definition KS_huJl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huJl.regs0 LibSegJu_huJl.regs_out0).
Lemma KS_huJl_ok : BG.kept_ok 48 LibSegJu_huJl.regs0 LibSegJu_huJl.regs_out0 KS_huJl = true. Proof. vm_compute. reflexivity. Qed.
Definition huJl_conc_s := ",=A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0O#10000#;7120Na_v2#>8v23B#v23#??Fv23#tJa_v2#>7#7La_v2#=8v25,3_v2#138#8_v2#128#8_v2#<0#8,1,9X#34394#55454Y,T,1#343>4T,8#;3;20T,:v25T,<#;63;4Lb_v2#128#;39?8Lb_v2#<0#;3;10Lb_v2#138#;3:>8"%pstring.
Lemma huJl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huJl] fx R M V huJl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huJl] LibSegJu_huJl.regs0 LibSegJu_huJl.kn0 LibSegJu_huJl.BR LibSegJu_huJl.PSS LibSegJu_huJl.NX0 LibSegJu_huJl.F0 213908 LibSegJu_huJl.seg_sound_ax fx R M V huJl_conc_s. Qed.
Definition KS_huK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huK.regs0 LibSegJu_huK.regs_out0).
Lemma KS_huK_ok : BG.kept_ok 48 LibSegJu_huK.regs0 LibSegJu_huK.regs_out0 KS_huK = true. Proof. vm_compute. reflexivity. Qed.
Definition huK_conc_s := ",6A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0O#10000#;7120,1_v2#128#8,1,5X#343>4#809>8Y,T,1#343?<T,:_v2#120Lb_v2#128#;3978"%pstring.
Lemma huK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huK] fx R M V huK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huK] LibSegJu_huK.regs0 LibSegJu_huK.kn0 LibSegJu_huK.BR LibSegJu_huK.PSS LibSegJu_huK.NX0 LibSegJu_huK.F0 213988 LibSegJu_huK.seg_sound_ax fx R M V huK_conc_s. Qed.
Definition KS_huL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huL.regs0 LibSegJu_huL.regs_out0).
Lemma KS_huL_ok : BG.kept_ok 48 LibSegJu_huL.regs0 LibSegJu_huL.regs_out0 KS_huL = true. Proof. vm_compute. reflexivity. Qed.
Definition huL_conc_s := ",5A#v2p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0,,1,5X#343?<#5<204Y,T,1#34410T,:_v2#<0T,;+r8#8"%pstring.
Lemma huL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huL] fx R M V huL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huL] LibSegJu_huL.regs0 LibSegJu_huL.kn0 LibSegJu_huL.BR LibSegJu_huL.PSS LibSegJu_huL.NX0 LibSegJu_huL.F0 214012 LibSegJu_huL.seg_sound_ax fx R M V huL_conc_s. Qed.
Definition KS_huMs : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huMs.regs0 LibSegJu_huMs.regs_out0).
Lemma KS_huMs_ok : BG.kept_ok 48 LibSegJu_huMs.regs0 LibSegJu_huMs.regs_out0 KS_huMs = true. Proof. vm_compute. reflexivity. Qed.
Definition huMs_conc_s := ",=A#v2p#2#40A#v23p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#28v23B#v23#??Fv23#fLa_v2#8v26La_v2#10v27,,1,6X#34410#3443<Y,T,1v26T,2v2T,8v27T,:#"%pstring.
Lemma huMs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huMs] fx R M V huMs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huMs] LibSegJu_huMs.regs0 LibSegJu_huMs.kn0 LibSegJu_huMs.BR LibSegJu_huMs.PSS LibSegJu_huMs.NX0 LibSegJu_huMs.F0 214032 LibSegJu_huMs.seg_sound_ax fx R M V huMs_conc_s. Qed.
Definition KS_huMl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huMl.regs0 LibSegJu_huMl.regs_out0).
Lemma KS_huMl_ok : BG.kept_ok 48 LibSegJu_huMl.regs0 LibSegJu_huMl.regs_out0 KS_huMl = true. Proof. vm_compute. reflexivity. Qed.
Definition huMl_conc_s := ",<A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0Na_v2#28v23B#v23#??Fv23#tJa_v2#27#7La_v2#18v25,,1,4X#34410#55454Y,T,1#3442<T,:v25"%pstring.
Lemma huMl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huMl] fx R M V huMl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huMl] LibSegJu_huMl.regs0 LibSegJu_huMl.kn0 LibSegJu_huMl.BR LibSegJu_huMl.PSS LibSegJu_huMl.NX0 LibSegJu_huMl.F0 214032 LibSegJu_huMl.seg_sound_ax fx R M V huMl_conc_s. Qed.
Definition KS_huN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_huN.regs0 LibSegJu_huN.regs_out0).
Lemma KS_huN_ok : BG.kept_ok 48 LibSegJu_huN.regs0 LibSegJu_huN.regs_out0 KS_huN = true. Proof. vm_compute. reflexivity. Qed.
Definition huN_conc_s := ",9A#v2p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#2?0B#7???7?8002?0v2#800000000000Hv2#10I_v2#2?0#2?0La_v2#8v26La_v2#10v27,,1,6X#3442<#3443<Y,T,1v26T,2v2T,8v27T,:#"%pstring.
Lemma huN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_huN] fx R M V huN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_huN] LibSegJu_huN.regs0 LibSegJu_huN.kn0 LibSegJu_huN.BR LibSegJu_huN.PSS LibSegJu_huN.NX0 LibSegJu_huN.F0 214060 LibSegJu_huN.seg_sound_ax fx R M V huN_conc_s. Qed.
End PMUHP.
