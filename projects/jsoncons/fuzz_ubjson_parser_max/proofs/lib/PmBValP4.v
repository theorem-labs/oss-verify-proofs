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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bvlR3Z LibSegJb_bvlR3P1 LibSegJb_bvlR3P2 LibSegJb_bvlR3P3 LibSegJb_bvlR3P4 LibSegJb_bvlR3P5 LibSegJb_bvlR3P6 LibSegJb_bvlR3P7 LibSegJb_bvlR2Z LibSegJb_bvlR2P1 LibSegJb_bvlR2P2 LibSegJb_bvlR2P3 LibSegJb_bvlR2P4 LibSegJb_bvlR2P5 LibSegJb_bvlR2P6 LibSegJb_bvlR2P7 LibSegJb_bvlR1Z LibSegJb_bvlR1P1 LibSegJb_bvlR1P2 LibSegJb_bvlR1P3 LibSegJb_bvlR1P4 LibSegJb_bvlR1P5 LibSegJb_bvlR1P6 LibSegJb_bvlR1P7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVALP4.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bvlR3Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3Z.regs0 LibSegJb_bvlR3Z.regs_out0).
Lemma KS_bvlR3Z_0_ok : BG.kept_ok 60 LibSegJb_bvlR3Z.regs0 LibSegJb_bvlR3Z.regs_out0 KS_bvlR3Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3Z.regs0 LibSegJb_bvlR3Z.regs_out1).
Lemma KS_bvlR3Z_1_ok : BG.kept_ok 60 LibSegJb_bvlR3Z.regs0 LibSegJb_bvlR3Z.regs_out1 KS_bvlR3Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bvlR3Z_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Ka+/+v21#3#8#7???8000#1,,2,4X#;13?<#;1574Y,T,1+v21#3T,;#2,3X#;13?<#;141<Y,1T,1+v21#3"%pstring.
Lemma bvlR3Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlR3Z_0; KS_bvlR3Z_1] fx R M V bvlR3Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlR3Z_0; KS_bvlR3Z_1] LibSegJb_bvlR3Z.regs0 LibSegJb_bvlR3Z.kn0 LibSegJb_bvlR3Z.BR LibSegJb_bvlR3Z.PSS LibSegJb_bvlR3Z.NX0 LibSegJb_bvlR3Z.F0 726012 LibSegJb_bvlR3Z.seg_sound_ax fx R M V bvlR3Z_conc_s. Qed.
Definition KS_bvlR3P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P1.regs0 LibSegJb_bvlR3P1.regs_out0).
Lemma KS_bvlR3P1_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P1.regs0 LibSegJb_bvlR3P1.regs_out0 KS_bvlR3P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P1.regs0 LibSegJb_bvlR3P1.regs_out1).
Lemma KS_bvlR3P1_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P1.regs0 LibSegJb_bvlR3P1.regs_out1 KS_bvlR3P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P1_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#1B#&%+v21#3p#2#40#7#,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2T,1;#,4X#;13?<#;141<Y,1T,1+v21#3T,1;#"%pstring.
Lemma bvlR3P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P1_0; KS_bvlR3P1_1] fx R M V bvlR3P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P1_0; KS_bvlR3P1_1] LibSegJb_bvlR3P1.regs0 LibSegJb_bvlR3P1.kn0 LibSegJb_bvlR3P1.BR LibSegJb_bvlR3P1.PSS LibSegJb_bvlR3P1.NX0 LibSegJb_bvlR3P1.F0 726012 LibSegJb_bvlR3P1.seg_sound_ax fx R M V bvlR3P1_conc_s. Qed.
Definition KS_bvlR3P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P2.regs0 LibSegJb_bvlR3P2.regs_out0).
Lemma KS_bvlR3P2_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P2.regs0 LibSegJb_bvlR3P2.regs_out0 KS_bvlR3P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P2.regs0 LibSegJb_bvlR3P2.regs_out1).
Lemma KS_bvlR3P2_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P2.regs0 LibSegJb_bvlR3P2.regs_out1 KS_bvlR3P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P2_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#2B#&%+v21#3p#2#40#7#1,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2W,1;&%+v21#3p#2#40#7,4X#;13?<#;141<Y,1T,1+v21#3W,1;&%+v21#3p#2#40#7"%pstring.
Lemma bvlR3P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P2_0; KS_bvlR3P2_1] fx R M V bvlR3P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P2_0; KS_bvlR3P2_1] LibSegJb_bvlR3P2.regs0 LibSegJb_bvlR3P2.kn0 LibSegJb_bvlR3P2.BR LibSegJb_bvlR3P2.PSS LibSegJb_bvlR3P2.NX0 LibSegJb_bvlR3P2.F0 726012 LibSegJb_bvlR3P2.seg_sound_ax fx R M V bvlR3P2_conc_s. Qed.
Definition KS_bvlR3P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P3.regs0 LibSegJb_bvlR3P3.regs_out0).
Lemma KS_bvlR3P3_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P3.regs0 LibSegJb_bvlR3P3.regs_out0 KS_bvlR3P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P3.regs0 LibSegJb_bvlR3P3.regs_out1).
Lemma KS_bvlR3P3_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P3.regs0 LibSegJb_bvlR3P3.regs_out1 KS_bvlR3P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P3_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#3B#&%+v21#3p#2#40#7#2,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2W,1;&%+v21#3p#2#40#7,4X#;13?<#;141<Y,1T,1+v21#3W,1;&%+v21#3p#2#40#7"%pstring.
Lemma bvlR3P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P3_0; KS_bvlR3P3_1] fx R M V bvlR3P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P3_0; KS_bvlR3P3_1] LibSegJb_bvlR3P3.regs0 LibSegJb_bvlR3P3.kn0 LibSegJb_bvlR3P3.BR LibSegJb_bvlR3P3.PSS LibSegJb_bvlR3P3.NX0 LibSegJb_bvlR3P3.F0 726012 LibSegJb_bvlR3P3.seg_sound_ax fx R M V bvlR3P3_conc_s. Qed.
Definition KS_bvlR3P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P4.regs0 LibSegJb_bvlR3P4.regs_out0).
Lemma KS_bvlR3P4_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P4.regs0 LibSegJb_bvlR3P4.regs_out0 KS_bvlR3P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P4.regs0 LibSegJb_bvlR3P4.regs_out1).
Lemma KS_bvlR3P4_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P4.regs0 LibSegJb_bvlR3P4.regs_out1 KS_bvlR3P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P4_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#4B#&%+v21#3p#2#40#7#3,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2W,1;&%+v21#3p#2#40#7,4X#;13?<#;141<Y,1T,1+v21#3W,1;&%+v21#3p#2#40#7"%pstring.
Lemma bvlR3P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P4_0; KS_bvlR3P4_1] fx R M V bvlR3P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P4_0; KS_bvlR3P4_1] LibSegJb_bvlR3P4.regs0 LibSegJb_bvlR3P4.kn0 LibSegJb_bvlR3P4.BR LibSegJb_bvlR3P4.PSS LibSegJb_bvlR3P4.NX0 LibSegJb_bvlR3P4.F0 726012 LibSegJb_bvlR3P4.seg_sound_ax fx R M V bvlR3P4_conc_s. Qed.
Definition KS_bvlR3P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P5.regs0 LibSegJb_bvlR3P5.regs_out0).
Lemma KS_bvlR3P5_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P5.regs0 LibSegJb_bvlR3P5.regs_out0 KS_bvlR3P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P5.regs0 LibSegJb_bvlR3P5.regs_out1).
Lemma KS_bvlR3P5_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P5.regs0 LibSegJb_bvlR3P5.regs_out1 KS_bvlR3P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P5_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#5B#&%+v21#3p#2#40#7#4,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2W,1;&%+v21#3p#2#40#7,4X#;13?<#;141<Y,1T,1+v21#3W,1;&%+v21#3p#2#40#7"%pstring.
Lemma bvlR3P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P5_0; KS_bvlR3P5_1] fx R M V bvlR3P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P5_0; KS_bvlR3P5_1] LibSegJb_bvlR3P5.regs0 LibSegJb_bvlR3P5.kn0 LibSegJb_bvlR3P5.BR LibSegJb_bvlR3P5.PSS LibSegJb_bvlR3P5.NX0 LibSegJb_bvlR3P5.F0 726012 LibSegJb_bvlR3P5.seg_sound_ax fx R M V bvlR3P5_conc_s. Qed.
Definition KS_bvlR3P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P6.regs0 LibSegJb_bvlR3P6.regs_out0).
Lemma KS_bvlR3P6_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P6.regs0 LibSegJb_bvlR3P6.regs_out0 KS_bvlR3P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P6.regs0 LibSegJb_bvlR3P6.regs_out1).
Lemma KS_bvlR3P6_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P6.regs0 LibSegJb_bvlR3P6.regs_out1 KS_bvlR3P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P6_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#6B#&%+v21#3p#2#40#7#5,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2W,1;&%+v21#3p#2#40#7,4X#;13?<#;141<Y,1T,1+v21#3W,1;&%+v21#3p#2#40#7"%pstring.
Lemma bvlR3P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P6_0; KS_bvlR3P6_1] fx R M V bvlR3P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P6_0; KS_bvlR3P6_1] LibSegJb_bvlR3P6.regs0 LibSegJb_bvlR3P6.kn0 LibSegJb_bvlR3P6.BR LibSegJb_bvlR3P6.PSS LibSegJb_bvlR3P6.NX0 LibSegJb_bvlR3P6.F0 726012 LibSegJb_bvlR3P6.seg_sound_ax fx R M V bvlR3P6_conc_s. Qed.
Definition KS_bvlR3P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P7.regs0 LibSegJb_bvlR3P7.regs_out0).
Lemma KS_bvlR3P7_0_ok : BG.kept_ok 60 LibSegJb_bvlR3P7.regs0 LibSegJb_bvlR3P7.regs_out0 KS_bvlR3P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR3P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR3P7.regs0 LibSegJb_bvlR3P7.regs_out1).
Lemma KS_bvlR3P7_1_ok : BG.kept_ok 60 LibSegJb_bvlR3P7.regs0 LibSegJb_bvlR3P7.regs_out1 KS_bvlR3P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR3P7_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#4S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#3S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:+v21#4S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#7B#&%+v21#3p#2#40#7#6,,2,5X#;13?<#;1574Y,T,1+v21#3T,;#2W,1;&%+v21#3p#2#40#7,4X#;13?<#;141<Y,1T,1+v21#3W,1;&%+v21#3p#2#40#7"%pstring.
Lemma bvlR3P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR3P7_0; KS_bvlR3P7_1] fx R M V bvlR3P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR3P7_0; KS_bvlR3P7_1] LibSegJb_bvlR3P7.regs0 LibSegJb_bvlR3P7.kn0 LibSegJb_bvlR3P7.BR LibSegJb_bvlR3P7.PSS LibSegJb_bvlR3P7.NX0 LibSegJb_bvlR3P7.F0 726012 LibSegJb_bvlR3P7.seg_sound_ax fx R M V bvlR3P7_conc_s. Qed.
Definition KS_bvlR2Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2Z.regs0 LibSegJb_bvlR2Z.regs_out0).
Lemma KS_bvlR2Z_0_ok : BG.kept_ok 60 LibSegJb_bvlR2Z.regs0 LibSegJb_bvlR2Z.regs_out0 KS_bvlR2Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2Z.regs0 LibSegJb_bvlR2Z.regs_out1).
Lemma KS_bvlR2Z_1_ok : BG.kept_ok 60 LibSegJb_bvlR2Z.regs0 LibSegJb_bvlR2Z.regs_out1 KS_bvlR2Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2Z_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Ka+/+v21#2#8#7???8000#1B#v22#800000000000,,2,4X#;141<#;1574Y,T,;#2T,<+v21#2,3X#;141<#;143<Y,1T,<+v21#2"%pstring.
Lemma bvlR2Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlR2Z_0; KS_bvlR2Z_1] fx R M V bvlR2Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlR2Z_0; KS_bvlR2Z_1] LibSegJb_bvlR2Z.regs0 LibSegJb_bvlR2Z.kn0 LibSegJb_bvlR2Z.BR LibSegJb_bvlR2Z.PSS LibSegJb_bvlR2Z.NX0 LibSegJb_bvlR2Z.F0 726044 LibSegJb_bvlR2Z.seg_sound_ax fx R M V bvlR2Z_conc_s. Qed.
Definition KS_bvlR2P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P1.regs0 LibSegJb_bvlR2P1.regs_out0).
Lemma KS_bvlR2P1_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P1.regs0 LibSegJb_bvlR2P1.regs_out0 KS_bvlR2P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P1.regs0 LibSegJb_bvlR2P1.regs_out1).
Lemma KS_bvlR2P1_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P1.regs0 LibSegJb_bvlR2P1.regs_out1 KS_bvlR2P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P1_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#1B#&%+v21#2p#2#40#7#B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2T,1;#,4X#;141<#;143<Y,1T,<+v21#2T,1;#"%pstring.
Lemma bvlR2P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P1_0; KS_bvlR2P1_1] fx R M V bvlR2P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P1_0; KS_bvlR2P1_1] LibSegJb_bvlR2P1.regs0 LibSegJb_bvlR2P1.kn0 LibSegJb_bvlR2P1.BR LibSegJb_bvlR2P1.PSS LibSegJb_bvlR2P1.NX0 LibSegJb_bvlR2P1.F0 726044 LibSegJb_bvlR2P1.seg_sound_ax fx R M V bvlR2P1_conc_s. Qed.
Definition KS_bvlR2P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P2.regs0 LibSegJb_bvlR2P2.regs_out0).
Lemma KS_bvlR2P2_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P2.regs0 LibSegJb_bvlR2P2.regs_out0 KS_bvlR2P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P2.regs0 LibSegJb_bvlR2P2.regs_out1).
Lemma KS_bvlR2P2_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P2.regs0 LibSegJb_bvlR2P2.regs_out1 KS_bvlR2P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P2_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#2B#&%+v21#2p#2#40#7#1B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2W,1;&%+v21#2p#2#40#7,4X#;141<#;143<Y,1T,<+v21#2W,1;&%+v21#2p#2#40#7"%pstring.
Lemma bvlR2P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P2_0; KS_bvlR2P2_1] fx R M V bvlR2P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P2_0; KS_bvlR2P2_1] LibSegJb_bvlR2P2.regs0 LibSegJb_bvlR2P2.kn0 LibSegJb_bvlR2P2.BR LibSegJb_bvlR2P2.PSS LibSegJb_bvlR2P2.NX0 LibSegJb_bvlR2P2.F0 726044 LibSegJb_bvlR2P2.seg_sound_ax fx R M V bvlR2P2_conc_s. Qed.
Definition KS_bvlR2P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P3.regs0 LibSegJb_bvlR2P3.regs_out0).
Lemma KS_bvlR2P3_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P3.regs0 LibSegJb_bvlR2P3.regs_out0 KS_bvlR2P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P3.regs0 LibSegJb_bvlR2P3.regs_out1).
Lemma KS_bvlR2P3_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P3.regs0 LibSegJb_bvlR2P3.regs_out1 KS_bvlR2P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P3_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#3B#&%+v21#2p#2#40#7#2B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2W,1;&%+v21#2p#2#40#7,4X#;141<#;143<Y,1T,<+v21#2W,1;&%+v21#2p#2#40#7"%pstring.
Lemma bvlR2P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P3_0; KS_bvlR2P3_1] fx R M V bvlR2P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P3_0; KS_bvlR2P3_1] LibSegJb_bvlR2P3.regs0 LibSegJb_bvlR2P3.kn0 LibSegJb_bvlR2P3.BR LibSegJb_bvlR2P3.PSS LibSegJb_bvlR2P3.NX0 LibSegJb_bvlR2P3.F0 726044 LibSegJb_bvlR2P3.seg_sound_ax fx R M V bvlR2P3_conc_s. Qed.
Definition KS_bvlR2P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P4.regs0 LibSegJb_bvlR2P4.regs_out0).
Lemma KS_bvlR2P4_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P4.regs0 LibSegJb_bvlR2P4.regs_out0 KS_bvlR2P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P4.regs0 LibSegJb_bvlR2P4.regs_out1).
Lemma KS_bvlR2P4_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P4.regs0 LibSegJb_bvlR2P4.regs_out1 KS_bvlR2P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P4_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#4B#&%+v21#2p#2#40#7#3B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2W,1;&%+v21#2p#2#40#7,4X#;141<#;143<Y,1T,<+v21#2W,1;&%+v21#2p#2#40#7"%pstring.
Lemma bvlR2P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P4_0; KS_bvlR2P4_1] fx R M V bvlR2P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P4_0; KS_bvlR2P4_1] LibSegJb_bvlR2P4.regs0 LibSegJb_bvlR2P4.kn0 LibSegJb_bvlR2P4.BR LibSegJb_bvlR2P4.PSS LibSegJb_bvlR2P4.NX0 LibSegJb_bvlR2P4.F0 726044 LibSegJb_bvlR2P4.seg_sound_ax fx R M V bvlR2P4_conc_s. Qed.
Definition KS_bvlR2P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P5.regs0 LibSegJb_bvlR2P5.regs_out0).
Lemma KS_bvlR2P5_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P5.regs0 LibSegJb_bvlR2P5.regs_out0 KS_bvlR2P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P5.regs0 LibSegJb_bvlR2P5.regs_out1).
Lemma KS_bvlR2P5_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P5.regs0 LibSegJb_bvlR2P5.regs_out1 KS_bvlR2P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P5_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#5B#&%+v21#2p#2#40#7#4B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2W,1;&%+v21#2p#2#40#7,4X#;141<#;143<Y,1T,<+v21#2W,1;&%+v21#2p#2#40#7"%pstring.
Lemma bvlR2P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P5_0; KS_bvlR2P5_1] fx R M V bvlR2P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P5_0; KS_bvlR2P5_1] LibSegJb_bvlR2P5.regs0 LibSegJb_bvlR2P5.kn0 LibSegJb_bvlR2P5.BR LibSegJb_bvlR2P5.PSS LibSegJb_bvlR2P5.NX0 LibSegJb_bvlR2P5.F0 726044 LibSegJb_bvlR2P5.seg_sound_ax fx R M V bvlR2P5_conc_s. Qed.
Definition KS_bvlR2P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P6.regs0 LibSegJb_bvlR2P6.regs_out0).
Lemma KS_bvlR2P6_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P6.regs0 LibSegJb_bvlR2P6.regs_out0 KS_bvlR2P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P6.regs0 LibSegJb_bvlR2P6.regs_out1).
Lemma KS_bvlR2P6_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P6.regs0 LibSegJb_bvlR2P6.regs_out1 KS_bvlR2P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P6_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#6B#&%+v21#2p#2#40#7#5B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2W,1;&%+v21#2p#2#40#7,4X#;141<#;143<Y,1T,<+v21#2W,1;&%+v21#2p#2#40#7"%pstring.
Lemma bvlR2P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P6_0; KS_bvlR2P6_1] fx R M V bvlR2P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P6_0; KS_bvlR2P6_1] LibSegJb_bvlR2P6.regs0 LibSegJb_bvlR2P6.kn0 LibSegJb_bvlR2P6.BR LibSegJb_bvlR2P6.PSS LibSegJb_bvlR2P6.NX0 LibSegJb_bvlR2P6.F0 726044 LibSegJb_bvlR2P6.seg_sound_ax fx R M V bvlR2P6_conc_s. Qed.
Definition KS_bvlR2P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P7.regs0 LibSegJb_bvlR2P7.regs_out0).
Lemma KS_bvlR2P7_0_ok : BG.kept_ok 60 LibSegJb_bvlR2P7.regs0 LibSegJb_bvlR2P7.regs_out0 KS_bvlR2P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR2P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR2P7.regs0 LibSegJb_bvlR2P7.regs_out1).
Lemma KS_bvlR2P7_1_ok : BG.kept_ok 60 LibSegJb_bvlR2P7.regs0 LibSegJb_bvlR2P7.regs_out1 KS_bvlR2P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR2P7_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,1+v21#3S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#7B#&%+v21#2p#2#40#7#6B#v22#800000000000,,2,5X#;141<#;1574Y,T,;#2T,<+v21#2W,1;&%+v21#2p#2#40#7,4X#;141<#;143<Y,1T,<+v21#2W,1;&%+v21#2p#2#40#7"%pstring.
Lemma bvlR2P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR2P7_0; KS_bvlR2P7_1] fx R M V bvlR2P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR2P7_0; KS_bvlR2P7_1] LibSegJb_bvlR2P7.regs0 LibSegJb_bvlR2P7.kn0 LibSegJb_bvlR2P7.BR LibSegJb_bvlR2P7.PSS LibSegJb_bvlR2P7.NX0 LibSegJb_bvlR2P7.F0 726044 LibSegJb_bvlR2P7.seg_sound_ax fx R M V bvlR2P7_conc_s. Qed.
Definition KS_bvlR1Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1Z.regs0 LibSegJb_bvlR1Z.regs_out0).
Lemma KS_bvlR1Z_0_ok : BG.kept_ok 60 LibSegJb_bvlR1Z.regs0 LibSegJb_bvlR1Z.regs_out0 KS_bvlR1Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1Z.regs0 LibSegJb_bvlR1Z.regs_out1).
Lemma KS_bvlR1Z_1_ok : BG.kept_ok 60 LibSegJb_bvlR1Z.regs0 LibSegJb_bvlR1Z.regs_out1 KS_bvlR1Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1Z_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Ka+/+v21#1#8#7???8000#1B#v22#800000000000,,2,4X#;143<#;1574Y,T,;#2T,<+v21#1,3X#;143<#;145<Y,1T,<+v21#1"%pstring.
Lemma bvlR1Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlR1Z_0; KS_bvlR1Z_1] fx R M V bvlR1Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlR1Z_0; KS_bvlR1Z_1] LibSegJb_bvlR1Z.regs0 LibSegJb_bvlR1Z.kn0 LibSegJb_bvlR1Z.BR LibSegJb_bvlR1Z.PSS LibSegJb_bvlR1Z.NX0 LibSegJb_bvlR1Z.F0 726076 LibSegJb_bvlR1Z.seg_sound_ax fx R M V bvlR1Z_conc_s. Qed.
Definition KS_bvlR1P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P1.regs0 LibSegJb_bvlR1P1.regs_out0).
Lemma KS_bvlR1P1_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P1.regs0 LibSegJb_bvlR1P1.regs_out0 KS_bvlR1P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P1.regs0 LibSegJb_bvlR1P1.regs_out1).
Lemma KS_bvlR1P1_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P1.regs0 LibSegJb_bvlR1P1.regs_out1 KS_bvlR1P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P1_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#1B#&%+v21#1p#2#40#7#B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1T,1;#,4X#;143<#;145<Y,1T,<+v21#1T,1;#"%pstring.
Lemma bvlR1P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P1_0; KS_bvlR1P1_1] fx R M V bvlR1P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P1_0; KS_bvlR1P1_1] LibSegJb_bvlR1P1.regs0 LibSegJb_bvlR1P1.kn0 LibSegJb_bvlR1P1.BR LibSegJb_bvlR1P1.PSS LibSegJb_bvlR1P1.NX0 LibSegJb_bvlR1P1.F0 726076 LibSegJb_bvlR1P1.seg_sound_ax fx R M V bvlR1P1_conc_s. Qed.
Definition KS_bvlR1P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P2.regs0 LibSegJb_bvlR1P2.regs_out0).
Lemma KS_bvlR1P2_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P2.regs0 LibSegJb_bvlR1P2.regs_out0 KS_bvlR1P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P2.regs0 LibSegJb_bvlR1P2.regs_out1).
Lemma KS_bvlR1P2_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P2.regs0 LibSegJb_bvlR1P2.regs_out1 KS_bvlR1P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P2_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#2B#&%+v21#1p#2#40#7#1B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1W,1;&%+v21#1p#2#40#7,4X#;143<#;145<Y,1T,<+v21#1W,1;&%+v21#1p#2#40#7"%pstring.
Lemma bvlR1P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P2_0; KS_bvlR1P2_1] fx R M V bvlR1P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P2_0; KS_bvlR1P2_1] LibSegJb_bvlR1P2.regs0 LibSegJb_bvlR1P2.kn0 LibSegJb_bvlR1P2.BR LibSegJb_bvlR1P2.PSS LibSegJb_bvlR1P2.NX0 LibSegJb_bvlR1P2.F0 726076 LibSegJb_bvlR1P2.seg_sound_ax fx R M V bvlR1P2_conc_s. Qed.
Definition KS_bvlR1P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P3.regs0 LibSegJb_bvlR1P3.regs_out0).
Lemma KS_bvlR1P3_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P3.regs0 LibSegJb_bvlR1P3.regs_out0 KS_bvlR1P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P3.regs0 LibSegJb_bvlR1P3.regs_out1).
Lemma KS_bvlR1P3_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P3.regs0 LibSegJb_bvlR1P3.regs_out1 KS_bvlR1P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P3_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#3B#&%+v21#1p#2#40#7#2B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1W,1;&%+v21#1p#2#40#7,4X#;143<#;145<Y,1T,<+v21#1W,1;&%+v21#1p#2#40#7"%pstring.
Lemma bvlR1P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P3_0; KS_bvlR1P3_1] fx R M V bvlR1P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P3_0; KS_bvlR1P3_1] LibSegJb_bvlR1P3.regs0 LibSegJb_bvlR1P3.kn0 LibSegJb_bvlR1P3.BR LibSegJb_bvlR1P3.PSS LibSegJb_bvlR1P3.NX0 LibSegJb_bvlR1P3.F0 726076 LibSegJb_bvlR1P3.seg_sound_ax fx R M V bvlR1P3_conc_s. Qed.
Definition KS_bvlR1P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P4.regs0 LibSegJb_bvlR1P4.regs_out0).
Lemma KS_bvlR1P4_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P4.regs0 LibSegJb_bvlR1P4.regs_out0 KS_bvlR1P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P4.regs0 LibSegJb_bvlR1P4.regs_out1).
Lemma KS_bvlR1P4_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P4.regs0 LibSegJb_bvlR1P4.regs_out1 KS_bvlR1P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P4_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#4B#&%+v21#1p#2#40#7#3B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1W,1;&%+v21#1p#2#40#7,4X#;143<#;145<Y,1T,<+v21#1W,1;&%+v21#1p#2#40#7"%pstring.
Lemma bvlR1P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P4_0; KS_bvlR1P4_1] fx R M V bvlR1P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P4_0; KS_bvlR1P4_1] LibSegJb_bvlR1P4.regs0 LibSegJb_bvlR1P4.kn0 LibSegJb_bvlR1P4.BR LibSegJb_bvlR1P4.PSS LibSegJb_bvlR1P4.NX0 LibSegJb_bvlR1P4.F0 726076 LibSegJb_bvlR1P4.seg_sound_ax fx R M V bvlR1P4_conc_s. Qed.
Definition KS_bvlR1P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P5.regs0 LibSegJb_bvlR1P5.regs_out0).
Lemma KS_bvlR1P5_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P5.regs0 LibSegJb_bvlR1P5.regs_out0 KS_bvlR1P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P5.regs0 LibSegJb_bvlR1P5.regs_out1).
Lemma KS_bvlR1P5_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P5.regs0 LibSegJb_bvlR1P5.regs_out1 KS_bvlR1P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P5_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#5B#&%+v21#1p#2#40#7#4B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1W,1;&%+v21#1p#2#40#7,4X#;143<#;145<Y,1T,<+v21#1W,1;&%+v21#1p#2#40#7"%pstring.
Lemma bvlR1P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P5_0; KS_bvlR1P5_1] fx R M V bvlR1P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P5_0; KS_bvlR1P5_1] LibSegJb_bvlR1P5.regs0 LibSegJb_bvlR1P5.kn0 LibSegJb_bvlR1P5.BR LibSegJb_bvlR1P5.PSS LibSegJb_bvlR1P5.NX0 LibSegJb_bvlR1P5.F0 726076 LibSegJb_bvlR1P5.seg_sound_ax fx R M V bvlR1P5_conc_s. Qed.
Definition KS_bvlR1P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P6.regs0 LibSegJb_bvlR1P6.regs_out0).
Lemma KS_bvlR1P6_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P6.regs0 LibSegJb_bvlR1P6.regs_out0 KS_bvlR1P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P6.regs0 LibSegJb_bvlR1P6.regs_out1).
Lemma KS_bvlR1P6_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P6.regs0 LibSegJb_bvlR1P6.regs_out1 KS_bvlR1P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P6_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#6B#&%+v21#1p#2#40#7#5B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1W,1;&%+v21#1p#2#40#7,4X#;143<#;145<Y,1T,<+v21#1W,1;&%+v21#1p#2#40#7"%pstring.
Lemma bvlR1P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P6_0; KS_bvlR1P6_1] fx R M V bvlR1P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P6_0; KS_bvlR1P6_1] LibSegJb_bvlR1P6.regs0 LibSegJb_bvlR1P6.kn0 LibSegJb_bvlR1P6.BR LibSegJb_bvlR1P6.PSS LibSegJb_bvlR1P6.NX0 LibSegJb_bvlR1P6.F0 726076 LibSegJb_bvlR1P6.seg_sound_ax fx R M V bvlR1P6_conc_s. Qed.
Definition KS_bvlR1P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P7.regs0 LibSegJb_bvlR1P7.regs_out0).
Lemma KS_bvlR1P7_0_ok : BG.kept_ok 60 LibSegJb_bvlR1P7.regs0 LibSegJb_bvlR1P7.regs_out0 KS_bvlR1P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlR1P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlR1P7.regs0 LibSegJb_bvlR1P7.regs_out1).
Lemma KS_bvlR1P7_1_ok : BG.kept_ok 60 LibSegJb_bvlR1P7.regs0 LibSegJb_bvlR1P7.regs_out1 KS_bvlR1P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlR1P7_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,<+v21#2S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#7B#&%+v21#1p#2#40#7#6B#v22#800000000000,,2,5X#;143<#;1574Y,T,;#2T,<+v21#1W,1;&%+v21#1p#2#40#7,4X#;143<#;145<Y,1T,<+v21#1W,1;&%+v21#1p#2#40#7"%pstring.
Lemma bvlR1P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlR1P7_0; KS_bvlR1P7_1] fx R M V bvlR1P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlR1P7_0; KS_bvlR1P7_1] LibSegJb_bvlR1P7.regs0 LibSegJb_bvlR1P7.kn0 LibSegJb_bvlR1P7.BR LibSegJb_bvlR1P7.PSS LibSegJb_bvlR1P7.NX0 LibSegJb_bvlR1P7.F0 726076 LibSegJb_bvlR1P7.seg_sound_ax fx R M V bvlR1P7_conc_s. Qed.
End PMBVALP4.
