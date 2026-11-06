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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_avlF5Z LibSegJa_avlF5P1 LibSegJa_avlF5P2 LibSegJa_avlF5P3 LibSegJa_avlF5P4 LibSegJa_avlF5P5 LibSegJa_avlF5P6 LibSegJa_avlF5P7 LibSegJa_avlF6Z LibSegJa_avlF6P1 LibSegJa_avlF6P2 LibSegJa_avlF6P3 LibSegJa_avlF6P4 LibSegJa_avlF6P5 LibSegJa_avlF6P6 LibSegJa_avlF6P7 LibSegJa_avlF7Z LibSegJa_avlF7P1 LibSegJa_avlF7P2 LibSegJa_avlF7P3 LibSegJa_avlF7P4 LibSegJa_avlF7P5 LibSegJa_avlF7P6 LibSegJa_avlF7P7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAVALP3.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_avlF5Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5Z.regs0 LibSegJa_avlF5Z.regs_out0).
Lemma KS_avlF5Z_0_ok : BG.kept_ok 60 LibSegJa_avlF5Z.regs0 LibSegJa_avlF5Z.regs_out0 KS_avlF5Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5Z.regs0 LibSegJa_avlF5Z.regs_out1).
Lemma KS_avlF5Z_1_ok : BG.kept_ok 60 LibSegJa_avlF5Z.regs0 LibSegJa_avlF5Z.regs_out1 KS_avlF5Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition avlF5Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Ka+/+v21#5#8#7???8000#1,,2,4X#:?;:4#:?<04Y,T,:+v21#5T,;#,4X#:?;:4#:?;<0Y,1T,:+v21#5T,;#"%pstring.
Lemma avlF5Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF5Z_0; KS_avlF5Z_1] fx R M V avlF5Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF5Z_0; KS_avlF5Z_1] LibSegJa_avlF5Z.regs0 LibSegJa_avlF5Z.kn0 LibSegJa_avlF5Z.BR LibSegJa_avlF5Z.PSS LibSegJa_avlF5Z.NX0 LibSegJa_avlF5Z.F0 719780 LibSegJa_avlF5Z.seg_sound_ax fx R M V avlF5Z_conc_s. Qed.
Definition KS_avlF5P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P1.regs0 LibSegJa_avlF5P1.regs_out0).
Lemma KS_avlF5P1_0_ok : BG.kept_ok 60 LibSegJa_avlF5P1.regs0 LibSegJa_avlF5P1.regs_out0 KS_avlF5P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P1.regs0 LibSegJa_avlF5P1.regs_out1).
Lemma KS_avlF5P1_1_ok : BG.kept_ok 60 LibSegJa_avlF5P1.regs0 LibSegJa_avlF5P1.regs_out1 KS_avlF5P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#1B#&%+v21#5p#2#40#7#,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#1T,=#,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#1T,=#"%pstring.
Lemma avlF5P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P1_0; KS_avlF5P1_1] fx R M V avlF5P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P1_0; KS_avlF5P1_1] LibSegJa_avlF5P1.regs0 LibSegJa_avlF5P1.kn0 LibSegJa_avlF5P1.BR LibSegJa_avlF5P1.PSS LibSegJa_avlF5P1.NX0 LibSegJa_avlF5P1.F0 719780 LibSegJa_avlF5P1.seg_sound_ax fx R M V avlF5P1_conc_s. Qed.
Definition KS_avlF5P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P2.regs0 LibSegJa_avlF5P2.regs_out0).
Lemma KS_avlF5P2_0_ok : BG.kept_ok 60 LibSegJa_avlF5P2.regs0 LibSegJa_avlF5P2.regs_out0 KS_avlF5P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P2.regs0 LibSegJa_avlF5P2.regs_out1).
Lemma KS_avlF5P2_1_ok : BG.kept_ok 60 LibSegJa_avlF5P2.regs0 LibSegJa_avlF5P2.regs_out1 KS_avlF5P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#2B#&%+v21#5p#2#40#7#1,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#2W,=&%+v21#5p#2#40#7,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#2W,=&%+v21#5p#2#40#7"%pstring.
Lemma avlF5P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P2_0; KS_avlF5P2_1] fx R M V avlF5P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P2_0; KS_avlF5P2_1] LibSegJa_avlF5P2.regs0 LibSegJa_avlF5P2.kn0 LibSegJa_avlF5P2.BR LibSegJa_avlF5P2.PSS LibSegJa_avlF5P2.NX0 LibSegJa_avlF5P2.F0 719780 LibSegJa_avlF5P2.seg_sound_ax fx R M V avlF5P2_conc_s. Qed.
Definition KS_avlF5P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P3.regs0 LibSegJa_avlF5P3.regs_out0).
Lemma KS_avlF5P3_0_ok : BG.kept_ok 60 LibSegJa_avlF5P3.regs0 LibSegJa_avlF5P3.regs_out0 KS_avlF5P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P3.regs0 LibSegJa_avlF5P3.regs_out1).
Lemma KS_avlF5P3_1_ok : BG.kept_ok 60 LibSegJa_avlF5P3.regs0 LibSegJa_avlF5P3.regs_out1 KS_avlF5P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#3B#&%+v21#5p#2#40#7#2,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#3W,=&%+v21#5p#2#40#7,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#3W,=&%+v21#5p#2#40#7"%pstring.
Lemma avlF5P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P3_0; KS_avlF5P3_1] fx R M V avlF5P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P3_0; KS_avlF5P3_1] LibSegJa_avlF5P3.regs0 LibSegJa_avlF5P3.kn0 LibSegJa_avlF5P3.BR LibSegJa_avlF5P3.PSS LibSegJa_avlF5P3.NX0 LibSegJa_avlF5P3.F0 719780 LibSegJa_avlF5P3.seg_sound_ax fx R M V avlF5P3_conc_s. Qed.
Definition KS_avlF5P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P4.regs0 LibSegJa_avlF5P4.regs_out0).
Lemma KS_avlF5P4_0_ok : BG.kept_ok 60 LibSegJa_avlF5P4.regs0 LibSegJa_avlF5P4.regs_out0 KS_avlF5P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P4.regs0 LibSegJa_avlF5P4.regs_out1).
Lemma KS_avlF5P4_1_ok : BG.kept_ok 60 LibSegJa_avlF5P4.regs0 LibSegJa_avlF5P4.regs_out1 KS_avlF5P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#4B#&%+v21#5p#2#40#7#3,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#4W,=&%+v21#5p#2#40#7,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#4W,=&%+v21#5p#2#40#7"%pstring.
Lemma avlF5P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P4_0; KS_avlF5P4_1] fx R M V avlF5P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P4_0; KS_avlF5P4_1] LibSegJa_avlF5P4.regs0 LibSegJa_avlF5P4.kn0 LibSegJa_avlF5P4.BR LibSegJa_avlF5P4.PSS LibSegJa_avlF5P4.NX0 LibSegJa_avlF5P4.F0 719780 LibSegJa_avlF5P4.seg_sound_ax fx R M V avlF5P4_conc_s. Qed.
Definition KS_avlF5P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P5.regs0 LibSegJa_avlF5P5.regs_out0).
Lemma KS_avlF5P5_0_ok : BG.kept_ok 60 LibSegJa_avlF5P5.regs0 LibSegJa_avlF5P5.regs_out0 KS_avlF5P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P5.regs0 LibSegJa_avlF5P5.regs_out1).
Lemma KS_avlF5P5_1_ok : BG.kept_ok 60 LibSegJa_avlF5P5.regs0 LibSegJa_avlF5P5.regs_out1 KS_avlF5P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#5B#&%+v21#5p#2#40#7#4,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#5W,=&%+v21#5p#2#40#7,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#5W,=&%+v21#5p#2#40#7"%pstring.
Lemma avlF5P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P5_0; KS_avlF5P5_1] fx R M V avlF5P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P5_0; KS_avlF5P5_1] LibSegJa_avlF5P5.regs0 LibSegJa_avlF5P5.kn0 LibSegJa_avlF5P5.BR LibSegJa_avlF5P5.PSS LibSegJa_avlF5P5.NX0 LibSegJa_avlF5P5.F0 719780 LibSegJa_avlF5P5.seg_sound_ax fx R M V avlF5P5_conc_s. Qed.
Definition KS_avlF5P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P6.regs0 LibSegJa_avlF5P6.regs_out0).
Lemma KS_avlF5P6_0_ok : BG.kept_ok 60 LibSegJa_avlF5P6.regs0 LibSegJa_avlF5P6.regs_out0 KS_avlF5P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P6.regs0 LibSegJa_avlF5P6.regs_out1).
Lemma KS_avlF5P6_1_ok : BG.kept_ok 60 LibSegJa_avlF5P6.regs0 LibSegJa_avlF5P6.regs_out1 KS_avlF5P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#6B#&%+v21#5p#2#40#7#5,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#6W,=&%+v21#5p#2#40#7,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#6W,=&%+v21#5p#2#40#7"%pstring.
Lemma avlF5P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P6_0; KS_avlF5P6_1] fx R M V avlF5P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P6_0; KS_avlF5P6_1] LibSegJa_avlF5P6.regs0 LibSegJa_avlF5P6.kn0 LibSegJa_avlF5P6.BR LibSegJa_avlF5P6.PSS LibSegJa_avlF5P6.NX0 LibSegJa_avlF5P6.F0 719780 LibSegJa_avlF5P6.seg_sound_ax fx R M V avlF5P6_conc_s. Qed.
Definition KS_avlF5P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P7.regs0 LibSegJa_avlF5P7.regs_out0).
Lemma KS_avlF5P7_0_ok : BG.kept_ok 60 LibSegJa_avlF5P7.regs0 LibSegJa_avlF5P7.regs_out0 KS_avlF5P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF5P7.regs0 LibSegJa_avlF5P7.regs_out1).
Lemma KS_avlF5P7_1_ok : BG.kept_ok 60 LibSegJa_avlF5P7.regs0 LibSegJa_avlF5P7.regs_out1 KS_avlF5P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF5P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#7B#&%+v21#5p#2#40#7#6,,2,5X#:?;:4#:?<04Y,T,:+v21#5T,;#7W,=&%+v21#5p#2#40#7,5X#:?;:4#:?;<0Y,1T,:+v21#5T,;#7W,=&%+v21#5p#2#40#7"%pstring.
Lemma avlF5P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF5P7_0; KS_avlF5P7_1] fx R M V avlF5P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF5P7_0; KS_avlF5P7_1] LibSegJa_avlF5P7.regs0 LibSegJa_avlF5P7.kn0 LibSegJa_avlF5P7.BR LibSegJa_avlF5P7.PSS LibSegJa_avlF5P7.NX0 LibSegJa_avlF5P7.F0 719780 LibSegJa_avlF5P7.seg_sound_ax fx R M V avlF5P7_conc_s. Qed.
Definition KS_avlF6Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6Z.regs0 LibSegJa_avlF6Z.regs_out0).
Lemma KS_avlF6Z_0_ok : BG.kept_ok 60 LibSegJa_avlF6Z.regs0 LibSegJa_avlF6Z.regs_out0 KS_avlF6Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6Z.regs0 LibSegJa_avlF6Z.regs_out1).
Lemma KS_avlF6Z_1_ok : BG.kept_ok 60 LibSegJa_avlF6Z.regs0 LibSegJa_avlF6Z.regs_out1 KS_avlF6Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Ka+/+v21#6#8#7???8000#1,,2,4X#:?;<0#:?<04Y,T,:+v21#6T,;#,4X#:?;<0#:?;=<Y,1T,:+v21#6T,;#"%pstring.
Lemma avlF6Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF6Z_0; KS_avlF6Z_1] fx R M V avlF6Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF6Z_0; KS_avlF6Z_1] LibSegJa_avlF6Z.regs0 LibSegJa_avlF6Z.kn0 LibSegJa_avlF6Z.BR LibSegJa_avlF6Z.PSS LibSegJa_avlF6Z.NX0 LibSegJa_avlF6Z.F0 719808 LibSegJa_avlF6Z.seg_sound_ax fx R M V avlF6Z_conc_s. Qed.
Definition KS_avlF6P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P1.regs0 LibSegJa_avlF6P1.regs_out0).
Lemma KS_avlF6P1_0_ok : BG.kept_ok 60 LibSegJa_avlF6P1.regs0 LibSegJa_avlF6P1.regs_out0 KS_avlF6P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P1.regs0 LibSegJa_avlF6P1.regs_out1).
Lemma KS_avlF6P1_1_ok : BG.kept_ok 60 LibSegJa_avlF6P1.regs0 LibSegJa_avlF6P1.regs_out1 KS_avlF6P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#1B#&%+v21#6p#2#40#7#,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#1T,=#,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#1T,=#"%pstring.
Lemma avlF6P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P1_0; KS_avlF6P1_1] fx R M V avlF6P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P1_0; KS_avlF6P1_1] LibSegJa_avlF6P1.regs0 LibSegJa_avlF6P1.kn0 LibSegJa_avlF6P1.BR LibSegJa_avlF6P1.PSS LibSegJa_avlF6P1.NX0 LibSegJa_avlF6P1.F0 719808 LibSegJa_avlF6P1.seg_sound_ax fx R M V avlF6P1_conc_s. Qed.
Definition KS_avlF6P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P2.regs0 LibSegJa_avlF6P2.regs_out0).
Lemma KS_avlF6P2_0_ok : BG.kept_ok 60 LibSegJa_avlF6P2.regs0 LibSegJa_avlF6P2.regs_out0 KS_avlF6P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P2.regs0 LibSegJa_avlF6P2.regs_out1).
Lemma KS_avlF6P2_1_ok : BG.kept_ok 60 LibSegJa_avlF6P2.regs0 LibSegJa_avlF6P2.regs_out1 KS_avlF6P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#2B#&%+v21#6p#2#40#7#1,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#2W,=&%+v21#6p#2#40#7,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#2W,=&%+v21#6p#2#40#7"%pstring.
Lemma avlF6P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P2_0; KS_avlF6P2_1] fx R M V avlF6P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P2_0; KS_avlF6P2_1] LibSegJa_avlF6P2.regs0 LibSegJa_avlF6P2.kn0 LibSegJa_avlF6P2.BR LibSegJa_avlF6P2.PSS LibSegJa_avlF6P2.NX0 LibSegJa_avlF6P2.F0 719808 LibSegJa_avlF6P2.seg_sound_ax fx R M V avlF6P2_conc_s. Qed.
Definition KS_avlF6P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P3.regs0 LibSegJa_avlF6P3.regs_out0).
Lemma KS_avlF6P3_0_ok : BG.kept_ok 60 LibSegJa_avlF6P3.regs0 LibSegJa_avlF6P3.regs_out0 KS_avlF6P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P3.regs0 LibSegJa_avlF6P3.regs_out1).
Lemma KS_avlF6P3_1_ok : BG.kept_ok 60 LibSegJa_avlF6P3.regs0 LibSegJa_avlF6P3.regs_out1 KS_avlF6P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#3B#&%+v21#6p#2#40#7#2,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#3W,=&%+v21#6p#2#40#7,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#3W,=&%+v21#6p#2#40#7"%pstring.
Lemma avlF6P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P3_0; KS_avlF6P3_1] fx R M V avlF6P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P3_0; KS_avlF6P3_1] LibSegJa_avlF6P3.regs0 LibSegJa_avlF6P3.kn0 LibSegJa_avlF6P3.BR LibSegJa_avlF6P3.PSS LibSegJa_avlF6P3.NX0 LibSegJa_avlF6P3.F0 719808 LibSegJa_avlF6P3.seg_sound_ax fx R M V avlF6P3_conc_s. Qed.
Definition KS_avlF6P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P4.regs0 LibSegJa_avlF6P4.regs_out0).
Lemma KS_avlF6P4_0_ok : BG.kept_ok 60 LibSegJa_avlF6P4.regs0 LibSegJa_avlF6P4.regs_out0 KS_avlF6P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P4.regs0 LibSegJa_avlF6P4.regs_out1).
Lemma KS_avlF6P4_1_ok : BG.kept_ok 60 LibSegJa_avlF6P4.regs0 LibSegJa_avlF6P4.regs_out1 KS_avlF6P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#4B#&%+v21#6p#2#40#7#3,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#4W,=&%+v21#6p#2#40#7,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#4W,=&%+v21#6p#2#40#7"%pstring.
Lemma avlF6P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P4_0; KS_avlF6P4_1] fx R M V avlF6P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P4_0; KS_avlF6P4_1] LibSegJa_avlF6P4.regs0 LibSegJa_avlF6P4.kn0 LibSegJa_avlF6P4.BR LibSegJa_avlF6P4.PSS LibSegJa_avlF6P4.NX0 LibSegJa_avlF6P4.F0 719808 LibSegJa_avlF6P4.seg_sound_ax fx R M V avlF6P4_conc_s. Qed.
Definition KS_avlF6P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P5.regs0 LibSegJa_avlF6P5.regs_out0).
Lemma KS_avlF6P5_0_ok : BG.kept_ok 60 LibSegJa_avlF6P5.regs0 LibSegJa_avlF6P5.regs_out0 KS_avlF6P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P5.regs0 LibSegJa_avlF6P5.regs_out1).
Lemma KS_avlF6P5_1_ok : BG.kept_ok 60 LibSegJa_avlF6P5.regs0 LibSegJa_avlF6P5.regs_out1 KS_avlF6P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#5B#&%+v21#6p#2#40#7#4,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#5W,=&%+v21#6p#2#40#7,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#5W,=&%+v21#6p#2#40#7"%pstring.
Lemma avlF6P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P5_0; KS_avlF6P5_1] fx R M V avlF6P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P5_0; KS_avlF6P5_1] LibSegJa_avlF6P5.regs0 LibSegJa_avlF6P5.kn0 LibSegJa_avlF6P5.BR LibSegJa_avlF6P5.PSS LibSegJa_avlF6P5.NX0 LibSegJa_avlF6P5.F0 719808 LibSegJa_avlF6P5.seg_sound_ax fx R M V avlF6P5_conc_s. Qed.
Definition KS_avlF6P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P6.regs0 LibSegJa_avlF6P6.regs_out0).
Lemma KS_avlF6P6_0_ok : BG.kept_ok 60 LibSegJa_avlF6P6.regs0 LibSegJa_avlF6P6.regs_out0 KS_avlF6P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P6.regs0 LibSegJa_avlF6P6.regs_out1).
Lemma KS_avlF6P6_1_ok : BG.kept_ok 60 LibSegJa_avlF6P6.regs0 LibSegJa_avlF6P6.regs_out1 KS_avlF6P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#6B#&%+v21#6p#2#40#7#5,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#6W,=&%+v21#6p#2#40#7,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#6W,=&%+v21#6p#2#40#7"%pstring.
Lemma avlF6P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P6_0; KS_avlF6P6_1] fx R M V avlF6P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P6_0; KS_avlF6P6_1] LibSegJa_avlF6P6.regs0 LibSegJa_avlF6P6.kn0 LibSegJa_avlF6P6.BR LibSegJa_avlF6P6.PSS LibSegJa_avlF6P6.NX0 LibSegJa_avlF6P6.F0 719808 LibSegJa_avlF6P6.seg_sound_ax fx R M V avlF6P6_conc_s. Qed.
Definition KS_avlF6P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P7.regs0 LibSegJa_avlF6P7.regs_out0).
Lemma KS_avlF6P7_0_ok : BG.kept_ok 60 LibSegJa_avlF6P7.regs0 LibSegJa_avlF6P7.regs_out0 KS_avlF6P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF6P7.regs0 LibSegJa_avlF6P7.regs_out1).
Lemma KS_avlF6P7_1_ok : BG.kept_ok 60 LibSegJa_avlF6P7.regs0 LibSegJa_avlF6P7.regs_out1 KS_avlF6P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF6P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#7B#&%+v21#6p#2#40#7#6,,2,5X#:?;<0#:?<04Y,T,:+v21#6T,;#7W,=&%+v21#6p#2#40#7,5X#:?;<0#:?;=<Y,1T,:+v21#6T,;#7W,=&%+v21#6p#2#40#7"%pstring.
Lemma avlF6P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF6P7_0; KS_avlF6P7_1] fx R M V avlF6P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF6P7_0; KS_avlF6P7_1] LibSegJa_avlF6P7.regs0 LibSegJa_avlF6P7.kn0 LibSegJa_avlF6P7.BR LibSegJa_avlF6P7.PSS LibSegJa_avlF6P7.NX0 LibSegJa_avlF6P7.F0 719808 LibSegJa_avlF6P7.seg_sound_ax fx R M V avlF6P7_conc_s. Qed.
Definition KS_avlF7Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7Z.regs0 LibSegJa_avlF7Z.regs_out0).
Lemma KS_avlF7Z_0_ok : BG.kept_ok 60 LibSegJa_avlF7Z.regs0 LibSegJa_avlF7Z.regs_out0 KS_avlF7Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7Z.regs0 LibSegJa_avlF7Z.regs_out1).
Lemma KS_avlF7Z_1_ok : BG.kept_ok 60 LibSegJa_avlF7Z.regs0 LibSegJa_avlF7Z.regs_out1 KS_avlF7Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Ka+/+v21#7#8#7???8000#1,,2,4X#:?;=<#:?<04Y,T,:+v21#7T,;#,5X#:?;=<#:?<?<Y,1T,:+v21#7T,;#T,<+v21#8"%pstring.
Lemma avlF7Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF7Z_0; KS_avlF7Z_1] fx R M V avlF7Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF7Z_0; KS_avlF7Z_1] LibSegJa_avlF7Z.regs0 LibSegJa_avlF7Z.kn0 LibSegJa_avlF7Z.BR LibSegJa_avlF7Z.PSS LibSegJa_avlF7Z.NX0 LibSegJa_avlF7Z.F0 719836 LibSegJa_avlF7Z.seg_sound_ax fx R M V avlF7Z_conc_s. Qed.
Definition KS_avlF7P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P1.regs0 LibSegJa_avlF7P1.regs_out0).
Lemma KS_avlF7P1_0_ok : BG.kept_ok 60 LibSegJa_avlF7P1.regs0 LibSegJa_avlF7P1.regs_out0 KS_avlF7P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P1.regs0 LibSegJa_avlF7P1.regs_out1).
Lemma KS_avlF7P1_1_ok : BG.kept_ok 60 LibSegJa_avlF7P1.regs0 LibSegJa_avlF7P1.regs_out1 KS_avlF7P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#1B#&%+v21#7p#2#40#7#,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#1T,=#,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#1T,<+v21#8T,=#"%pstring.
Lemma avlF7P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P1_0; KS_avlF7P1_1] fx R M V avlF7P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P1_0; KS_avlF7P1_1] LibSegJa_avlF7P1.regs0 LibSegJa_avlF7P1.kn0 LibSegJa_avlF7P1.BR LibSegJa_avlF7P1.PSS LibSegJa_avlF7P1.NX0 LibSegJa_avlF7P1.F0 719836 LibSegJa_avlF7P1.seg_sound_ax fx R M V avlF7P1_conc_s. Qed.
Definition KS_avlF7P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P2.regs0 LibSegJa_avlF7P2.regs_out0).
Lemma KS_avlF7P2_0_ok : BG.kept_ok 60 LibSegJa_avlF7P2.regs0 LibSegJa_avlF7P2.regs_out0 KS_avlF7P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P2.regs0 LibSegJa_avlF7P2.regs_out1).
Lemma KS_avlF7P2_1_ok : BG.kept_ok 60 LibSegJa_avlF7P2.regs0 LibSegJa_avlF7P2.regs_out1 KS_avlF7P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#2B#&%+v21#7p#2#40#7#1,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#2W,=&%+v21#7p#2#40#7,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#2T,<+v21#8W,=&%+v21#7p#2#40#7"%pstring.
Lemma avlF7P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P2_0; KS_avlF7P2_1] fx R M V avlF7P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P2_0; KS_avlF7P2_1] LibSegJa_avlF7P2.regs0 LibSegJa_avlF7P2.kn0 LibSegJa_avlF7P2.BR LibSegJa_avlF7P2.PSS LibSegJa_avlF7P2.NX0 LibSegJa_avlF7P2.F0 719836 LibSegJa_avlF7P2.seg_sound_ax fx R M V avlF7P2_conc_s. Qed.
Definition KS_avlF7P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P3.regs0 LibSegJa_avlF7P3.regs_out0).
Lemma KS_avlF7P3_0_ok : BG.kept_ok 60 LibSegJa_avlF7P3.regs0 LibSegJa_avlF7P3.regs_out0 KS_avlF7P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P3.regs0 LibSegJa_avlF7P3.regs_out1).
Lemma KS_avlF7P3_1_ok : BG.kept_ok 60 LibSegJa_avlF7P3.regs0 LibSegJa_avlF7P3.regs_out1 KS_avlF7P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#3B#&%+v21#7p#2#40#7#2,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#3W,=&%+v21#7p#2#40#7,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#3T,<+v21#8W,=&%+v21#7p#2#40#7"%pstring.
Lemma avlF7P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P3_0; KS_avlF7P3_1] fx R M V avlF7P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P3_0; KS_avlF7P3_1] LibSegJa_avlF7P3.regs0 LibSegJa_avlF7P3.kn0 LibSegJa_avlF7P3.BR LibSegJa_avlF7P3.PSS LibSegJa_avlF7P3.NX0 LibSegJa_avlF7P3.F0 719836 LibSegJa_avlF7P3.seg_sound_ax fx R M V avlF7P3_conc_s. Qed.
Definition KS_avlF7P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P4.regs0 LibSegJa_avlF7P4.regs_out0).
Lemma KS_avlF7P4_0_ok : BG.kept_ok 60 LibSegJa_avlF7P4.regs0 LibSegJa_avlF7P4.regs_out0 KS_avlF7P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P4.regs0 LibSegJa_avlF7P4.regs_out1).
Lemma KS_avlF7P4_1_ok : BG.kept_ok 60 LibSegJa_avlF7P4.regs0 LibSegJa_avlF7P4.regs_out1 KS_avlF7P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#4B#&%+v21#7p#2#40#7#3,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#4W,=&%+v21#7p#2#40#7,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#4T,<+v21#8W,=&%+v21#7p#2#40#7"%pstring.
Lemma avlF7P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P4_0; KS_avlF7P4_1] fx R M V avlF7P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P4_0; KS_avlF7P4_1] LibSegJa_avlF7P4.regs0 LibSegJa_avlF7P4.kn0 LibSegJa_avlF7P4.BR LibSegJa_avlF7P4.PSS LibSegJa_avlF7P4.NX0 LibSegJa_avlF7P4.F0 719836 LibSegJa_avlF7P4.seg_sound_ax fx R M V avlF7P4_conc_s. Qed.
Definition KS_avlF7P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P5.regs0 LibSegJa_avlF7P5.regs_out0).
Lemma KS_avlF7P5_0_ok : BG.kept_ok 60 LibSegJa_avlF7P5.regs0 LibSegJa_avlF7P5.regs_out0 KS_avlF7P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P5.regs0 LibSegJa_avlF7P5.regs_out1).
Lemma KS_avlF7P5_1_ok : BG.kept_ok 60 LibSegJa_avlF7P5.regs0 LibSegJa_avlF7P5.regs_out1 KS_avlF7P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#5B#&%+v21#7p#2#40#7#4,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#5W,=&%+v21#7p#2#40#7,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#5T,<+v21#8W,=&%+v21#7p#2#40#7"%pstring.
Lemma avlF7P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P5_0; KS_avlF7P5_1] fx R M V avlF7P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P5_0; KS_avlF7P5_1] LibSegJa_avlF7P5.regs0 LibSegJa_avlF7P5.kn0 LibSegJa_avlF7P5.BR LibSegJa_avlF7P5.PSS LibSegJa_avlF7P5.NX0 LibSegJa_avlF7P5.F0 719836 LibSegJa_avlF7P5.seg_sound_ax fx R M V avlF7P5_conc_s. Qed.
Definition KS_avlF7P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P6.regs0 LibSegJa_avlF7P6.regs_out0).
Lemma KS_avlF7P6_0_ok : BG.kept_ok 60 LibSegJa_avlF7P6.regs0 LibSegJa_avlF7P6.regs_out0 KS_avlF7P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P6.regs0 LibSegJa_avlF7P6.regs_out1).
Lemma KS_avlF7P6_1_ok : BG.kept_ok 60 LibSegJa_avlF7P6.regs0 LibSegJa_avlF7P6.regs_out1 KS_avlF7P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#6B#&%+v21#7p#2#40#7#5,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#6W,=&%+v21#7p#2#40#7,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#6T,<+v21#8W,=&%+v21#7p#2#40#7"%pstring.
Lemma avlF7P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P6_0; KS_avlF7P6_1] fx R M V avlF7P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P6_0; KS_avlF7P6_1] LibSegJa_avlF7P6.regs0 LibSegJa_avlF7P6.kn0 LibSegJa_avlF7P6.BR LibSegJa_avlF7P6.PSS LibSegJa_avlF7P6.NX0 LibSegJa_avlF7P6.F0 719836 LibSegJa_avlF7P6.seg_sound_ax fx R M V avlF7P6_conc_s. Qed.
Definition KS_avlF7P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P7.regs0 LibSegJa_avlF7P7.regs_out0).
Lemma KS_avlF7P7_0_ok : BG.kept_ok 60 LibSegJa_avlF7P7.regs0 LibSegJa_avlF7P7.regs_out0 KS_avlF7P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF7P7.regs0 LibSegJa_avlF7P7.regs_out1).
Lemma KS_avlF7P7_1_ok : BG.kept_ok 60 LibSegJa_avlF7P7.regs0 LibSegJa_avlF7P7.regs_out1 KS_avlF7P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF7P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#7B#&%+v21#7p#2#40#7#6,,2,5X#:?;=<#:?<04Y,T,:+v21#7T,;#7W,=&%+v21#7p#2#40#7,6X#:?;=<#:?<?<Y,1T,:+v21#7T,;#7T,<+v21#8W,=&%+v21#7p#2#40#7"%pstring.
Lemma avlF7P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF7P7_0; KS_avlF7P7_1] fx R M V avlF7P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF7P7_0; KS_avlF7P7_1] LibSegJa_avlF7P7.regs0 LibSegJa_avlF7P7.kn0 LibSegJa_avlF7P7.BR LibSegJa_avlF7P7.PSS LibSegJa_avlF7P7.NX0 LibSegJa_avlF7P7.F0 719836 LibSegJa_avlF7P7.seg_sound_ax fx R M V avlF7P7_conc_s. Qed.
End PMAVALP3.
