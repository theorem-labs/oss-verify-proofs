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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ja0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_avlR3Z LibSegJa_avlR3P1 LibSegJa_avlR3P2 LibSegJa_avlR3P3 LibSegJa_avlR3P4 LibSegJa_avlR3P5 LibSegJa_avlR3P6 LibSegJa_avlR3P7 LibSegJa_avlR2Z LibSegJa_avlR2P1 LibSegJa_avlR2P2 LibSegJa_avlR2P3 LibSegJa_avlR2P4 LibSegJa_avlR2P5 LibSegJa_avlR2P6 LibSegJa_avlR2P7 LibSegJa_avlR1Z LibSegJa_avlR1P1 LibSegJa_avlR1P2 LibSegJa_avlR1P3 LibSegJa_avlR1P4 LibSegJa_avlR1P5 LibSegJa_avlR1P6 LibSegJa_avlR1P7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAVALP4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_avlR3Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3Z.regs0 LibSegJa_avlR3Z.regs_out0).
Lemma KS_avlR3Z_0_ok : BG.kept_ok 60 LibSegJa_avlR3Z.regs0 LibSegJa_avlR3Z.regs_out0 KS_avlR3Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3Z.regs0 LibSegJa_avlR3Z.regs_out1).
Lemma KS_avlR3Z_1_ok : BG.kept_ok 60 LibSegJa_avlR3Z.regs0 LibSegJa_avlR3Z.regs_out1 KS_avlR3Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition avlR3Z_conc_s := ",26A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Ka+/+v21#3#8#7???8000#1,,2,4X#:?<5<#:?=;8Y,T,;#2T,1:+v21#3,3X#:?<5<#:?<78Y,1T,1:+v21#3"%pstring.
Lemma avlR3Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlR3Z_0; KS_avlR3Z_1] fx R M V avlR3Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlR3Z_0; KS_avlR3Z_1] LibSegJa_avlR3Z.regs0 LibSegJa_avlR3Z.kn0 LibSegJa_avlR3Z.BR LibSegJa_avlR3Z.PSS LibSegJa_avlR3Z.NX0 LibSegJa_avlR3Z.F0 719964 LibSegJa_avlR3Z.seg_sound_ax fx R M V avlR3Z_conc_s. Qed.
Definition KS_avlR3P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P1.regs0 LibSegJa_avlR3P1.regs_out0).
Lemma KS_avlR3P1_0_ok : BG.kept_ok 60 LibSegJa_avlR3P1.regs0 LibSegJa_avlR3P1.regs_out0 KS_avlR3P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P1.regs0 LibSegJa_avlR3P1.regs_out1).
Lemma KS_avlR3P1_1_ok : BG.kept_ok 60 LibSegJa_avlR3P1.regs0 LibSegJa_avlR3P1.regs_out1 KS_avlR3P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P1_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#1B#&%+v21#3p#2#40#7#,,2,5X#:?<5<#:?=;8Y,T,;#2T,19#T,1:+v21#3,4X#:?<5<#:?<78Y,1T,19#T,1:+v21#3"%pstring.
Lemma avlR3P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P1_0; KS_avlR3P1_1] fx R M V avlR3P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P1_0; KS_avlR3P1_1] LibSegJa_avlR3P1.regs0 LibSegJa_avlR3P1.kn0 LibSegJa_avlR3P1.BR LibSegJa_avlR3P1.PSS LibSegJa_avlR3P1.NX0 LibSegJa_avlR3P1.F0 719964 LibSegJa_avlR3P1.seg_sound_ax fx R M V avlR3P1_conc_s. Qed.
Definition KS_avlR3P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P2.regs0 LibSegJa_avlR3P2.regs_out0).
Lemma KS_avlR3P2_0_ok : BG.kept_ok 60 LibSegJa_avlR3P2.regs0 LibSegJa_avlR3P2.regs_out0 KS_avlR3P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P2.regs0 LibSegJa_avlR3P2.regs_out1).
Lemma KS_avlR3P2_1_ok : BG.kept_ok 60 LibSegJa_avlR3P2.regs0 LibSegJa_avlR3P2.regs_out1 KS_avlR3P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P2_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#2B#&%+v21#3p#2#40#7#1,,2,5X#:?<5<#:?=;8Y,T,;#2W,19&%+v21#3p#2#40#7T,1:+v21#3,4X#:?<5<#:?<78Y,1W,19&%+v21#3p#2#40#7T,1:+v21#3"%pstring.
Lemma avlR3P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P2_0; KS_avlR3P2_1] fx R M V avlR3P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P2_0; KS_avlR3P2_1] LibSegJa_avlR3P2.regs0 LibSegJa_avlR3P2.kn0 LibSegJa_avlR3P2.BR LibSegJa_avlR3P2.PSS LibSegJa_avlR3P2.NX0 LibSegJa_avlR3P2.F0 719964 LibSegJa_avlR3P2.seg_sound_ax fx R M V avlR3P2_conc_s. Qed.
Definition KS_avlR3P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P3.regs0 LibSegJa_avlR3P3.regs_out0).
Lemma KS_avlR3P3_0_ok : BG.kept_ok 60 LibSegJa_avlR3P3.regs0 LibSegJa_avlR3P3.regs_out0 KS_avlR3P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P3.regs0 LibSegJa_avlR3P3.regs_out1).
Lemma KS_avlR3P3_1_ok : BG.kept_ok 60 LibSegJa_avlR3P3.regs0 LibSegJa_avlR3P3.regs_out1 KS_avlR3P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P3_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#3B#&%+v21#3p#2#40#7#2,,2,5X#:?<5<#:?=;8Y,T,;#2W,19&%+v21#3p#2#40#7T,1:+v21#3,4X#:?<5<#:?<78Y,1W,19&%+v21#3p#2#40#7T,1:+v21#3"%pstring.
Lemma avlR3P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P3_0; KS_avlR3P3_1] fx R M V avlR3P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P3_0; KS_avlR3P3_1] LibSegJa_avlR3P3.regs0 LibSegJa_avlR3P3.kn0 LibSegJa_avlR3P3.BR LibSegJa_avlR3P3.PSS LibSegJa_avlR3P3.NX0 LibSegJa_avlR3P3.F0 719964 LibSegJa_avlR3P3.seg_sound_ax fx R M V avlR3P3_conc_s. Qed.
Definition KS_avlR3P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P4.regs0 LibSegJa_avlR3P4.regs_out0).
Lemma KS_avlR3P4_0_ok : BG.kept_ok 60 LibSegJa_avlR3P4.regs0 LibSegJa_avlR3P4.regs_out0 KS_avlR3P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P4.regs0 LibSegJa_avlR3P4.regs_out1).
Lemma KS_avlR3P4_1_ok : BG.kept_ok 60 LibSegJa_avlR3P4.regs0 LibSegJa_avlR3P4.regs_out1 KS_avlR3P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P4_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#4B#&%+v21#3p#2#40#7#3,,2,5X#:?<5<#:?=;8Y,T,;#2W,19&%+v21#3p#2#40#7T,1:+v21#3,4X#:?<5<#:?<78Y,1W,19&%+v21#3p#2#40#7T,1:+v21#3"%pstring.
Lemma avlR3P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P4_0; KS_avlR3P4_1] fx R M V avlR3P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P4_0; KS_avlR3P4_1] LibSegJa_avlR3P4.regs0 LibSegJa_avlR3P4.kn0 LibSegJa_avlR3P4.BR LibSegJa_avlR3P4.PSS LibSegJa_avlR3P4.NX0 LibSegJa_avlR3P4.F0 719964 LibSegJa_avlR3P4.seg_sound_ax fx R M V avlR3P4_conc_s. Qed.
Definition KS_avlR3P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P5.regs0 LibSegJa_avlR3P5.regs_out0).
Lemma KS_avlR3P5_0_ok : BG.kept_ok 60 LibSegJa_avlR3P5.regs0 LibSegJa_avlR3P5.regs_out0 KS_avlR3P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P5.regs0 LibSegJa_avlR3P5.regs_out1).
Lemma KS_avlR3P5_1_ok : BG.kept_ok 60 LibSegJa_avlR3P5.regs0 LibSegJa_avlR3P5.regs_out1 KS_avlR3P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P5_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#5B#&%+v21#3p#2#40#7#4,,2,5X#:?<5<#:?=;8Y,T,;#2W,19&%+v21#3p#2#40#7T,1:+v21#3,4X#:?<5<#:?<78Y,1W,19&%+v21#3p#2#40#7T,1:+v21#3"%pstring.
Lemma avlR3P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P5_0; KS_avlR3P5_1] fx R M V avlR3P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P5_0; KS_avlR3P5_1] LibSegJa_avlR3P5.regs0 LibSegJa_avlR3P5.kn0 LibSegJa_avlR3P5.BR LibSegJa_avlR3P5.PSS LibSegJa_avlR3P5.NX0 LibSegJa_avlR3P5.F0 719964 LibSegJa_avlR3P5.seg_sound_ax fx R M V avlR3P5_conc_s. Qed.
Definition KS_avlR3P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P6.regs0 LibSegJa_avlR3P6.regs_out0).
Lemma KS_avlR3P6_0_ok : BG.kept_ok 60 LibSegJa_avlR3P6.regs0 LibSegJa_avlR3P6.regs_out0 KS_avlR3P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P6.regs0 LibSegJa_avlR3P6.regs_out1).
Lemma KS_avlR3P6_1_ok : BG.kept_ok 60 LibSegJa_avlR3P6.regs0 LibSegJa_avlR3P6.regs_out1 KS_avlR3P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P6_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#6B#&%+v21#3p#2#40#7#5,,2,5X#:?<5<#:?=;8Y,T,;#2W,19&%+v21#3p#2#40#7T,1:+v21#3,4X#:?<5<#:?<78Y,1W,19&%+v21#3p#2#40#7T,1:+v21#3"%pstring.
Lemma avlR3P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P6_0; KS_avlR3P6_1] fx R M V avlR3P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P6_0; KS_avlR3P6_1] LibSegJa_avlR3P6.regs0 LibSegJa_avlR3P6.kn0 LibSegJa_avlR3P6.BR LibSegJa_avlR3P6.PSS LibSegJa_avlR3P6.NX0 LibSegJa_avlR3P6.F0 719964 LibSegJa_avlR3P6.seg_sound_ax fx R M V avlR3P6_conc_s. Qed.
Definition KS_avlR3P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P7.regs0 LibSegJa_avlR3P7.regs_out0).
Lemma KS_avlR3P7_0_ok : BG.kept_ok 60 LibSegJa_avlR3P7.regs0 LibSegJa_avlR3P7.regs_out0 KS_avlR3P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR3P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR3P7.regs0 LibSegJa_avlR3P7.regs_out1).
Lemma KS_avlR3P7_1_ok : BG.kept_ok 60 LibSegJa_avlR3P7.regs0 LibSegJa_avlR3P7.regs_out1 KS_avlR3P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR3P7_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21#4S,=+v21#3S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#4S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#3v27B#v27#??Na+/+v21#3#8#7???8000#7B#&%+v21#3p#2#40#7#6,,2,5X#:?<5<#:?=;8Y,T,;#2W,19&%+v21#3p#2#40#7T,1:+v21#3,4X#:?<5<#:?<78Y,1W,19&%+v21#3p#2#40#7T,1:+v21#3"%pstring.
Lemma avlR3P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR3P7_0; KS_avlR3P7_1] fx R M V avlR3P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR3P7_0; KS_avlR3P7_1] LibSegJa_avlR3P7.regs0 LibSegJa_avlR3P7.kn0 LibSegJa_avlR3P7.BR LibSegJa_avlR3P7.PSS LibSegJa_avlR3P7.NX0 LibSegJa_avlR3P7.F0 719964 LibSegJa_avlR3P7.seg_sound_ax fx R M V avlR3P7_conc_s. Qed.
Definition KS_avlR2Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2Z.regs0 LibSegJa_avlR2Z.regs_out0).
Lemma KS_avlR2Z_0_ok : BG.kept_ok 60 LibSegJa_avlR2Z.regs0 LibSegJa_avlR2Z.regs_out0 KS_avlR2Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2Z.regs0 LibSegJa_avlR2Z.regs_out1).
Lemma KS_avlR2Z_1_ok : BG.kept_ok 60 LibSegJa_avlR2Z.regs0 LibSegJa_avlR2Z.regs_out1 KS_avlR2Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2Z_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Ka+/+v21#2#8#7???8000#1B#v22#800000000000,,2,4X#:?<78#:?=;8Y,T,;#2T,=+v21#2,3X#:?<78#:?<94Y,1T,=+v21#2"%pstring.
Lemma avlR2Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlR2Z_0; KS_avlR2Z_1] fx R M V avlR2Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlR2Z_0; KS_avlR2Z_1] LibSegJa_avlR2Z.regs0 LibSegJa_avlR2Z.kn0 LibSegJa_avlR2Z.BR LibSegJa_avlR2Z.PSS LibSegJa_avlR2Z.NX0 LibSegJa_avlR2Z.F0 719992 LibSegJa_avlR2Z.seg_sound_ax fx R M V avlR2Z_conc_s. Qed.
Definition KS_avlR2P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P1.regs0 LibSegJa_avlR2P1.regs_out0).
Lemma KS_avlR2P1_0_ok : BG.kept_ok 60 LibSegJa_avlR2P1.regs0 LibSegJa_avlR2P1.regs_out0 KS_avlR2P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P1.regs0 LibSegJa_avlR2P1.regs_out1).
Lemma KS_avlR2P1_1_ok : BG.kept_ok 60 LibSegJa_avlR2P1.regs0 LibSegJa_avlR2P1.regs_out1 KS_avlR2P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P1_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#1B#&%+v21#2p#2#40#7#B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2T,19#,4X#:?<78#:?<94Y,1T,=+v21#2T,19#"%pstring.
Lemma avlR2P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P1_0; KS_avlR2P1_1] fx R M V avlR2P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P1_0; KS_avlR2P1_1] LibSegJa_avlR2P1.regs0 LibSegJa_avlR2P1.kn0 LibSegJa_avlR2P1.BR LibSegJa_avlR2P1.PSS LibSegJa_avlR2P1.NX0 LibSegJa_avlR2P1.F0 719992 LibSegJa_avlR2P1.seg_sound_ax fx R M V avlR2P1_conc_s. Qed.
Definition KS_avlR2P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P2.regs0 LibSegJa_avlR2P2.regs_out0).
Lemma KS_avlR2P2_0_ok : BG.kept_ok 60 LibSegJa_avlR2P2.regs0 LibSegJa_avlR2P2.regs_out0 KS_avlR2P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P2.regs0 LibSegJa_avlR2P2.regs_out1).
Lemma KS_avlR2P2_1_ok : BG.kept_ok 60 LibSegJa_avlR2P2.regs0 LibSegJa_avlR2P2.regs_out1 KS_avlR2P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P2_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#2B#&%+v21#2p#2#40#7#1B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2W,19&%+v21#2p#2#40#7,4X#:?<78#:?<94Y,1T,=+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma avlR2P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P2_0; KS_avlR2P2_1] fx R M V avlR2P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P2_0; KS_avlR2P2_1] LibSegJa_avlR2P2.regs0 LibSegJa_avlR2P2.kn0 LibSegJa_avlR2P2.BR LibSegJa_avlR2P2.PSS LibSegJa_avlR2P2.NX0 LibSegJa_avlR2P2.F0 719992 LibSegJa_avlR2P2.seg_sound_ax fx R M V avlR2P2_conc_s. Qed.
Definition KS_avlR2P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P3.regs0 LibSegJa_avlR2P3.regs_out0).
Lemma KS_avlR2P3_0_ok : BG.kept_ok 60 LibSegJa_avlR2P3.regs0 LibSegJa_avlR2P3.regs_out0 KS_avlR2P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P3.regs0 LibSegJa_avlR2P3.regs_out1).
Lemma KS_avlR2P3_1_ok : BG.kept_ok 60 LibSegJa_avlR2P3.regs0 LibSegJa_avlR2P3.regs_out1 KS_avlR2P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P3_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#3B#&%+v21#2p#2#40#7#2B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2W,19&%+v21#2p#2#40#7,4X#:?<78#:?<94Y,1T,=+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma avlR2P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P3_0; KS_avlR2P3_1] fx R M V avlR2P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P3_0; KS_avlR2P3_1] LibSegJa_avlR2P3.regs0 LibSegJa_avlR2P3.kn0 LibSegJa_avlR2P3.BR LibSegJa_avlR2P3.PSS LibSegJa_avlR2P3.NX0 LibSegJa_avlR2P3.F0 719992 LibSegJa_avlR2P3.seg_sound_ax fx R M V avlR2P3_conc_s. Qed.
Definition KS_avlR2P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P4.regs0 LibSegJa_avlR2P4.regs_out0).
Lemma KS_avlR2P4_0_ok : BG.kept_ok 60 LibSegJa_avlR2P4.regs0 LibSegJa_avlR2P4.regs_out0 KS_avlR2P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P4.regs0 LibSegJa_avlR2P4.regs_out1).
Lemma KS_avlR2P4_1_ok : BG.kept_ok 60 LibSegJa_avlR2P4.regs0 LibSegJa_avlR2P4.regs_out1 KS_avlR2P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P4_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#4B#&%+v21#2p#2#40#7#3B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2W,19&%+v21#2p#2#40#7,4X#:?<78#:?<94Y,1T,=+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma avlR2P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P4_0; KS_avlR2P4_1] fx R M V avlR2P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P4_0; KS_avlR2P4_1] LibSegJa_avlR2P4.regs0 LibSegJa_avlR2P4.kn0 LibSegJa_avlR2P4.BR LibSegJa_avlR2P4.PSS LibSegJa_avlR2P4.NX0 LibSegJa_avlR2P4.F0 719992 LibSegJa_avlR2P4.seg_sound_ax fx R M V avlR2P4_conc_s. Qed.
Definition KS_avlR2P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P5.regs0 LibSegJa_avlR2P5.regs_out0).
Lemma KS_avlR2P5_0_ok : BG.kept_ok 60 LibSegJa_avlR2P5.regs0 LibSegJa_avlR2P5.regs_out0 KS_avlR2P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P5.regs0 LibSegJa_avlR2P5.regs_out1).
Lemma KS_avlR2P5_1_ok : BG.kept_ok 60 LibSegJa_avlR2P5.regs0 LibSegJa_avlR2P5.regs_out1 KS_avlR2P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P5_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#5B#&%+v21#2p#2#40#7#4B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2W,19&%+v21#2p#2#40#7,4X#:?<78#:?<94Y,1T,=+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma avlR2P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P5_0; KS_avlR2P5_1] fx R M V avlR2P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P5_0; KS_avlR2P5_1] LibSegJa_avlR2P5.regs0 LibSegJa_avlR2P5.kn0 LibSegJa_avlR2P5.BR LibSegJa_avlR2P5.PSS LibSegJa_avlR2P5.NX0 LibSegJa_avlR2P5.F0 719992 LibSegJa_avlR2P5.seg_sound_ax fx R M V avlR2P5_conc_s. Qed.
Definition KS_avlR2P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P6.regs0 LibSegJa_avlR2P6.regs_out0).
Lemma KS_avlR2P6_0_ok : BG.kept_ok 60 LibSegJa_avlR2P6.regs0 LibSegJa_avlR2P6.regs_out0 KS_avlR2P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P6.regs0 LibSegJa_avlR2P6.regs_out1).
Lemma KS_avlR2P6_1_ok : BG.kept_ok 60 LibSegJa_avlR2P6.regs0 LibSegJa_avlR2P6.regs_out1 KS_avlR2P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P6_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#6B#&%+v21#2p#2#40#7#5B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2W,19&%+v21#2p#2#40#7,4X#:?<78#:?<94Y,1T,=+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma avlR2P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P6_0; KS_avlR2P6_1] fx R M V avlR2P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P6_0; KS_avlR2P6_1] LibSegJa_avlR2P6.regs0 LibSegJa_avlR2P6.kn0 LibSegJa_avlR2P6.BR LibSegJa_avlR2P6.PSS LibSegJa_avlR2P6.NX0 LibSegJa_avlR2P6.F0 719992 LibSegJa_avlR2P6.seg_sound_ax fx R M V avlR2P6_conc_s. Qed.
Definition KS_avlR2P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P7.regs0 LibSegJa_avlR2P7.regs_out0).
Lemma KS_avlR2P7_0_ok : BG.kept_ok 60 LibSegJa_avlR2P7.regs0 LibSegJa_avlR2P7.regs_out0 KS_avlR2P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR2P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR2P7.regs0 LibSegJa_avlR2P7.regs_out1).
Lemma KS_avlR2P7_1_ok : BG.kept_ok 60 LibSegJa_avlR2P7.regs0 LibSegJa_avlR2P7.regs_out1 KS_avlR2P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR2P7_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1:+v21#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#2v27B#v27#??Na+/+v21#2#8#7???8000#7B#&%+v21#2p#2#40#7#6B#v22#800000000000,,2,5X#:?<78#:?=;8Y,T,;#2T,=+v21#2W,19&%+v21#2p#2#40#7,4X#:?<78#:?<94Y,1T,=+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma avlR2P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR2P7_0; KS_avlR2P7_1] fx R M V avlR2P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR2P7_0; KS_avlR2P7_1] LibSegJa_avlR2P7.regs0 LibSegJa_avlR2P7.kn0 LibSegJa_avlR2P7.BR LibSegJa_avlR2P7.PSS LibSegJa_avlR2P7.NX0 LibSegJa_avlR2P7.F0 719992 LibSegJa_avlR2P7.seg_sound_ax fx R M V avlR2P7_conc_s. Qed.
Definition KS_avlR1Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1Z.regs0 LibSegJa_avlR1Z.regs_out0).
Lemma KS_avlR1Z_0_ok : BG.kept_ok 60 LibSegJa_avlR1Z.regs0 LibSegJa_avlR1Z.regs_out0 KS_avlR1Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1Z.regs0 LibSegJa_avlR1Z.regs_out1).
Lemma KS_avlR1Z_1_ok : BG.kept_ok 60 LibSegJa_avlR1Z.regs0 LibSegJa_avlR1Z.regs_out1 KS_avlR1Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1Z_conc_s := ",27A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Ka+/+v21#1#8#7???8000#1B#v22#800000000000,,2,4X#:?<94#:?=;8Y,T,;#2T,=+v21#1,3X#:?<94#:?<;0Y,1T,=+v21#1"%pstring.
Lemma avlR1Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlR1Z_0; KS_avlR1Z_1] fx R M V avlR1Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlR1Z_0; KS_avlR1Z_1] LibSegJa_avlR1Z.regs0 LibSegJa_avlR1Z.kn0 LibSegJa_avlR1Z.BR LibSegJa_avlR1Z.PSS LibSegJa_avlR1Z.NX0 LibSegJa_avlR1Z.F0 720020 LibSegJa_avlR1Z.seg_sound_ax fx R M V avlR1Z_conc_s. Qed.
Definition KS_avlR1P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P1.regs0 LibSegJa_avlR1P1.regs_out0).
Lemma KS_avlR1P1_0_ok : BG.kept_ok 60 LibSegJa_avlR1P1.regs0 LibSegJa_avlR1P1.regs_out0 KS_avlR1P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P1.regs0 LibSegJa_avlR1P1.regs_out1).
Lemma KS_avlR1P1_1_ok : BG.kept_ok 60 LibSegJa_avlR1P1.regs0 LibSegJa_avlR1P1.regs_out1 KS_avlR1P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P1_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#1B#&%+v21#1p#2#40#7#B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1T,19#,4X#:?<94#:?<;0Y,1T,=+v21#1T,19#"%pstring.
Lemma avlR1P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P1_0; KS_avlR1P1_1] fx R M V avlR1P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P1_0; KS_avlR1P1_1] LibSegJa_avlR1P1.regs0 LibSegJa_avlR1P1.kn0 LibSegJa_avlR1P1.BR LibSegJa_avlR1P1.PSS LibSegJa_avlR1P1.NX0 LibSegJa_avlR1P1.F0 720020 LibSegJa_avlR1P1.seg_sound_ax fx R M V avlR1P1_conc_s. Qed.
Definition KS_avlR1P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P2.regs0 LibSegJa_avlR1P2.regs_out0).
Lemma KS_avlR1P2_0_ok : BG.kept_ok 60 LibSegJa_avlR1P2.regs0 LibSegJa_avlR1P2.regs_out0 KS_avlR1P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P2.regs0 LibSegJa_avlR1P2.regs_out1).
Lemma KS_avlR1P2_1_ok : BG.kept_ok 60 LibSegJa_avlR1P2.regs0 LibSegJa_avlR1P2.regs_out1 KS_avlR1P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P2_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#2B#&%+v21#1p#2#40#7#1B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1W,19&%+v21#1p#2#40#7,4X#:?<94#:?<;0Y,1T,=+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma avlR1P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P2_0; KS_avlR1P2_1] fx R M V avlR1P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P2_0; KS_avlR1P2_1] LibSegJa_avlR1P2.regs0 LibSegJa_avlR1P2.kn0 LibSegJa_avlR1P2.BR LibSegJa_avlR1P2.PSS LibSegJa_avlR1P2.NX0 LibSegJa_avlR1P2.F0 720020 LibSegJa_avlR1P2.seg_sound_ax fx R M V avlR1P2_conc_s. Qed.
Definition KS_avlR1P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P3.regs0 LibSegJa_avlR1P3.regs_out0).
Lemma KS_avlR1P3_0_ok : BG.kept_ok 60 LibSegJa_avlR1P3.regs0 LibSegJa_avlR1P3.regs_out0 KS_avlR1P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P3.regs0 LibSegJa_avlR1P3.regs_out1).
Lemma KS_avlR1P3_1_ok : BG.kept_ok 60 LibSegJa_avlR1P3.regs0 LibSegJa_avlR1P3.regs_out1 KS_avlR1P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P3_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#3B#&%+v21#1p#2#40#7#2B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1W,19&%+v21#1p#2#40#7,4X#:?<94#:?<;0Y,1T,=+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma avlR1P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P3_0; KS_avlR1P3_1] fx R M V avlR1P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P3_0; KS_avlR1P3_1] LibSegJa_avlR1P3.regs0 LibSegJa_avlR1P3.kn0 LibSegJa_avlR1P3.BR LibSegJa_avlR1P3.PSS LibSegJa_avlR1P3.NX0 LibSegJa_avlR1P3.F0 720020 LibSegJa_avlR1P3.seg_sound_ax fx R M V avlR1P3_conc_s. Qed.
Definition KS_avlR1P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P4.regs0 LibSegJa_avlR1P4.regs_out0).
Lemma KS_avlR1P4_0_ok : BG.kept_ok 60 LibSegJa_avlR1P4.regs0 LibSegJa_avlR1P4.regs_out0 KS_avlR1P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P4.regs0 LibSegJa_avlR1P4.regs_out1).
Lemma KS_avlR1P4_1_ok : BG.kept_ok 60 LibSegJa_avlR1P4.regs0 LibSegJa_avlR1P4.regs_out1 KS_avlR1P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P4_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#4B#&%+v21#1p#2#40#7#3B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1W,19&%+v21#1p#2#40#7,4X#:?<94#:?<;0Y,1T,=+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma avlR1P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P4_0; KS_avlR1P4_1] fx R M V avlR1P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P4_0; KS_avlR1P4_1] LibSegJa_avlR1P4.regs0 LibSegJa_avlR1P4.kn0 LibSegJa_avlR1P4.BR LibSegJa_avlR1P4.PSS LibSegJa_avlR1P4.NX0 LibSegJa_avlR1P4.F0 720020 LibSegJa_avlR1P4.seg_sound_ax fx R M V avlR1P4_conc_s. Qed.
Definition KS_avlR1P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P5.regs0 LibSegJa_avlR1P5.regs_out0).
Lemma KS_avlR1P5_0_ok : BG.kept_ok 60 LibSegJa_avlR1P5.regs0 LibSegJa_avlR1P5.regs_out0 KS_avlR1P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P5.regs0 LibSegJa_avlR1P5.regs_out1).
Lemma KS_avlR1P5_1_ok : BG.kept_ok 60 LibSegJa_avlR1P5.regs0 LibSegJa_avlR1P5.regs_out1 KS_avlR1P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P5_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#5B#&%+v21#1p#2#40#7#4B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1W,19&%+v21#1p#2#40#7,4X#:?<94#:?<;0Y,1T,=+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma avlR1P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P5_0; KS_avlR1P5_1] fx R M V avlR1P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P5_0; KS_avlR1P5_1] LibSegJa_avlR1P5.regs0 LibSegJa_avlR1P5.kn0 LibSegJa_avlR1P5.BR LibSegJa_avlR1P5.PSS LibSegJa_avlR1P5.NX0 LibSegJa_avlR1P5.F0 720020 LibSegJa_avlR1P5.seg_sound_ax fx R M V avlR1P5_conc_s. Qed.
Definition KS_avlR1P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P6.regs0 LibSegJa_avlR1P6.regs_out0).
Lemma KS_avlR1P6_0_ok : BG.kept_ok 60 LibSegJa_avlR1P6.regs0 LibSegJa_avlR1P6.regs_out0 KS_avlR1P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P6.regs0 LibSegJa_avlR1P6.regs_out1).
Lemma KS_avlR1P6_1_ok : BG.kept_ok 60 LibSegJa_avlR1P6.regs0 LibSegJa_avlR1P6.regs_out1 KS_avlR1P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P6_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#6B#&%+v21#1p#2#40#7#5B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1W,19&%+v21#1p#2#40#7,4X#:?<94#:?<;0Y,1T,=+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma avlR1P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P6_0; KS_avlR1P6_1] fx R M V avlR1P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P6_0; KS_avlR1P6_1] LibSegJa_avlR1P6.regs0 LibSegJa_avlR1P6.kn0 LibSegJa_avlR1P6.BR LibSegJa_avlR1P6.PSS LibSegJa_avlR1P6.NX0 LibSegJa_avlR1P6.F0 720020 LibSegJa_avlR1P6.seg_sound_ax fx R M V avlR1P6_conc_s. Qed.
Definition KS_avlR1P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P7.regs0 LibSegJa_avlR1P7.regs_out0).
Lemma KS_avlR1P7_0_ok : BG.kept_ok 60 LibSegJa_avlR1P7.regs0 LibSegJa_avlR1P7.regs_out0 KS_avlR1P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlR1P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlR1P7.regs0 LibSegJa_avlR1P7.regs_out1).
Lemma KS_avlR1P7_1_ok : BG.kept_ok 60 LibSegJa_avlR1P7.regs0 LibSegJa_avlR1P7.regs_out1 KS_avlR1P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlR1P7_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<v22S,=+v21#2S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??Na+v21#1v27B#v27#??Na+/+v21#1#8#7???8000#7B#&%+v21#1p#2#40#7#6B#v22#800000000000,,2,5X#:?<94#:?=;8Y,T,;#2T,=+v21#1W,19&%+v21#1p#2#40#7,4X#:?<94#:?<;0Y,1T,=+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma avlR1P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlR1P7_0; KS_avlR1P7_1] fx R M V avlR1P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlR1P7_0; KS_avlR1P7_1] LibSegJa_avlR1P7.regs0 LibSegJa_avlR1P7.kn0 LibSegJa_avlR1P7.BR LibSegJa_avlR1P7.PSS LibSegJa_avlR1P7.NX0 LibSegJa_avlR1P7.F0 720020 LibSegJa_avlR1P7.seg_sound_ax fx R M V avlR1P7_conc_s. Qed.
End PMAVALP4.
