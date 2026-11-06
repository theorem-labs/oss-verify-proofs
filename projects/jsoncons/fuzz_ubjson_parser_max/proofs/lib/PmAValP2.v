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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_avlF1Z LibSegJa_avlF1P1 LibSegJa_avlF1P2 LibSegJa_avlF1P3 LibSegJa_avlF1P4 LibSegJa_avlF1P5 LibSegJa_avlF1P6 LibSegJa_avlF1P7 LibSegJa_avlF2Z LibSegJa_avlF2P1 LibSegJa_avlF2P2 LibSegJa_avlF2P3 LibSegJa_avlF2P4 LibSegJa_avlF2P5 LibSegJa_avlF2P6 LibSegJa_avlF2P7 LibSegJa_avlF3Z LibSegJa_avlF3P1 LibSegJa_avlF3P2 LibSegJa_avlF3P3 LibSegJa_avlF3P4 LibSegJa_avlF3P5 LibSegJa_avlF3P6 LibSegJa_avlF3P7 LibSegJa_avlF4Z LibSegJa_avlF4P1 LibSegJa_avlF4P2 LibSegJa_avlF4P3 LibSegJa_avlF4P4 LibSegJa_avlF4P5 LibSegJa_avlF4P6 LibSegJa_avlF4P7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAVALP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_avlF1Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1Z.regs0 LibSegJa_avlF1Z.regs_out0).
Lemma KS_avlF1Z_0_ok : BG.kept_ok 60 LibSegJa_avlF1Z.regs0 LibSegJa_avlF1Z.regs_out0 KS_avlF1Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1Z.regs0 LibSegJa_avlF1Z.regs_out1).
Lemma KS_avlF1Z_1_ok : BG.kept_ok 60 LibSegJa_avlF1Z.regs0 LibSegJa_avlF1Z.regs_out1 KS_avlF1Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition avlF1Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Ka+/+v21#1#8#7???8000#1,,2,4X#:?;34#:?<04Y,T,:+v21#1T,;#,4X#:?;34#:?;50Y,1T,:+v21#1T,;#"%pstring.
Lemma avlF1Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF1Z_0; KS_avlF1Z_1] fx R M V avlF1Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF1Z_0; KS_avlF1Z_1] LibSegJa_avlF1Z.regs0 LibSegJa_avlF1Z.kn0 LibSegJa_avlF1Z.BR LibSegJa_avlF1Z.PSS LibSegJa_avlF1Z.NX0 LibSegJa_avlF1Z.F0 719668 LibSegJa_avlF1Z.seg_sound_ax fx R M V avlF1Z_conc_s. Qed.
Definition KS_avlF1P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P1.regs0 LibSegJa_avlF1P1.regs_out0).
Lemma KS_avlF1P1_0_ok : BG.kept_ok 60 LibSegJa_avlF1P1.regs0 LibSegJa_avlF1P1.regs_out0 KS_avlF1P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P1.regs0 LibSegJa_avlF1P1.regs_out1).
Lemma KS_avlF1P1_1_ok : BG.kept_ok 60 LibSegJa_avlF1P1.regs0 LibSegJa_avlF1P1.regs_out1 KS_avlF1P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#1B#&%+v21#1p#2#40#7#,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#1T,=#,5X#:?;34#:?;50Y,1T,:+v21#1T,;#1T,=#"%pstring.
Lemma avlF1P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P1_0; KS_avlF1P1_1] fx R M V avlF1P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P1_0; KS_avlF1P1_1] LibSegJa_avlF1P1.regs0 LibSegJa_avlF1P1.kn0 LibSegJa_avlF1P1.BR LibSegJa_avlF1P1.PSS LibSegJa_avlF1P1.NX0 LibSegJa_avlF1P1.F0 719668 LibSegJa_avlF1P1.seg_sound_ax fx R M V avlF1P1_conc_s. Qed.
Definition KS_avlF1P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P2.regs0 LibSegJa_avlF1P2.regs_out0).
Lemma KS_avlF1P2_0_ok : BG.kept_ok 60 LibSegJa_avlF1P2.regs0 LibSegJa_avlF1P2.regs_out0 KS_avlF1P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P2.regs0 LibSegJa_avlF1P2.regs_out1).
Lemma KS_avlF1P2_1_ok : BG.kept_ok 60 LibSegJa_avlF1P2.regs0 LibSegJa_avlF1P2.regs_out1 KS_avlF1P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#2B#&%+v21#1p#2#40#7#1,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#2W,=&%+v21#1p#2#40#7,5X#:?;34#:?;50Y,1T,:+v21#1T,;#2W,=&%+v21#1p#2#40#7"%pstring.
Lemma avlF1P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P2_0; KS_avlF1P2_1] fx R M V avlF1P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P2_0; KS_avlF1P2_1] LibSegJa_avlF1P2.regs0 LibSegJa_avlF1P2.kn0 LibSegJa_avlF1P2.BR LibSegJa_avlF1P2.PSS LibSegJa_avlF1P2.NX0 LibSegJa_avlF1P2.F0 719668 LibSegJa_avlF1P2.seg_sound_ax fx R M V avlF1P2_conc_s. Qed.
Definition KS_avlF1P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P3.regs0 LibSegJa_avlF1P3.regs_out0).
Lemma KS_avlF1P3_0_ok : BG.kept_ok 60 LibSegJa_avlF1P3.regs0 LibSegJa_avlF1P3.regs_out0 KS_avlF1P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P3.regs0 LibSegJa_avlF1P3.regs_out1).
Lemma KS_avlF1P3_1_ok : BG.kept_ok 60 LibSegJa_avlF1P3.regs0 LibSegJa_avlF1P3.regs_out1 KS_avlF1P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#3B#&%+v21#1p#2#40#7#2,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#3W,=&%+v21#1p#2#40#7,5X#:?;34#:?;50Y,1T,:+v21#1T,;#3W,=&%+v21#1p#2#40#7"%pstring.
Lemma avlF1P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P3_0; KS_avlF1P3_1] fx R M V avlF1P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P3_0; KS_avlF1P3_1] LibSegJa_avlF1P3.regs0 LibSegJa_avlF1P3.kn0 LibSegJa_avlF1P3.BR LibSegJa_avlF1P3.PSS LibSegJa_avlF1P3.NX0 LibSegJa_avlF1P3.F0 719668 LibSegJa_avlF1P3.seg_sound_ax fx R M V avlF1P3_conc_s. Qed.
Definition KS_avlF1P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P4.regs0 LibSegJa_avlF1P4.regs_out0).
Lemma KS_avlF1P4_0_ok : BG.kept_ok 60 LibSegJa_avlF1P4.regs0 LibSegJa_avlF1P4.regs_out0 KS_avlF1P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P4.regs0 LibSegJa_avlF1P4.regs_out1).
Lemma KS_avlF1P4_1_ok : BG.kept_ok 60 LibSegJa_avlF1P4.regs0 LibSegJa_avlF1P4.regs_out1 KS_avlF1P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#4B#&%+v21#1p#2#40#7#3,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#4W,=&%+v21#1p#2#40#7,5X#:?;34#:?;50Y,1T,:+v21#1T,;#4W,=&%+v21#1p#2#40#7"%pstring.
Lemma avlF1P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P4_0; KS_avlF1P4_1] fx R M V avlF1P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P4_0; KS_avlF1P4_1] LibSegJa_avlF1P4.regs0 LibSegJa_avlF1P4.kn0 LibSegJa_avlF1P4.BR LibSegJa_avlF1P4.PSS LibSegJa_avlF1P4.NX0 LibSegJa_avlF1P4.F0 719668 LibSegJa_avlF1P4.seg_sound_ax fx R M V avlF1P4_conc_s. Qed.
Definition KS_avlF1P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P5.regs0 LibSegJa_avlF1P5.regs_out0).
Lemma KS_avlF1P5_0_ok : BG.kept_ok 60 LibSegJa_avlF1P5.regs0 LibSegJa_avlF1P5.regs_out0 KS_avlF1P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P5.regs0 LibSegJa_avlF1P5.regs_out1).
Lemma KS_avlF1P5_1_ok : BG.kept_ok 60 LibSegJa_avlF1P5.regs0 LibSegJa_avlF1P5.regs_out1 KS_avlF1P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#5B#&%+v21#1p#2#40#7#4,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#5W,=&%+v21#1p#2#40#7,5X#:?;34#:?;50Y,1T,:+v21#1T,;#5W,=&%+v21#1p#2#40#7"%pstring.
Lemma avlF1P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P5_0; KS_avlF1P5_1] fx R M V avlF1P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P5_0; KS_avlF1P5_1] LibSegJa_avlF1P5.regs0 LibSegJa_avlF1P5.kn0 LibSegJa_avlF1P5.BR LibSegJa_avlF1P5.PSS LibSegJa_avlF1P5.NX0 LibSegJa_avlF1P5.F0 719668 LibSegJa_avlF1P5.seg_sound_ax fx R M V avlF1P5_conc_s. Qed.
Definition KS_avlF1P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P6.regs0 LibSegJa_avlF1P6.regs_out0).
Lemma KS_avlF1P6_0_ok : BG.kept_ok 60 LibSegJa_avlF1P6.regs0 LibSegJa_avlF1P6.regs_out0 KS_avlF1P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P6.regs0 LibSegJa_avlF1P6.regs_out1).
Lemma KS_avlF1P6_1_ok : BG.kept_ok 60 LibSegJa_avlF1P6.regs0 LibSegJa_avlF1P6.regs_out1 KS_avlF1P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#6B#&%+v21#1p#2#40#7#5,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#6W,=&%+v21#1p#2#40#7,5X#:?;34#:?;50Y,1T,:+v21#1T,;#6W,=&%+v21#1p#2#40#7"%pstring.
Lemma avlF1P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P6_0; KS_avlF1P6_1] fx R M V avlF1P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P6_0; KS_avlF1P6_1] LibSegJa_avlF1P6.regs0 LibSegJa_avlF1P6.kn0 LibSegJa_avlF1P6.BR LibSegJa_avlF1P6.PSS LibSegJa_avlF1P6.NX0 LibSegJa_avlF1P6.F0 719668 LibSegJa_avlF1P6.seg_sound_ax fx R M V avlF1P6_conc_s. Qed.
Definition KS_avlF1P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P7.regs0 LibSegJa_avlF1P7.regs_out0).
Lemma KS_avlF1P7_0_ok : BG.kept_ok 60 LibSegJa_avlF1P7.regs0 LibSegJa_avlF1P7.regs_out0 KS_avlF1P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF1P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF1P7.regs0 LibSegJa_avlF1P7.regs_out1).
Lemma KS_avlF1P7_1_ok : BG.kept_ok 60 LibSegJa_avlF1P7.regs0 LibSegJa_avlF1P7.regs_out1 KS_avlF1P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF1P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#7B#&%+v21#1p#2#40#7#6,,2,5X#:?;34#:?<04Y,T,:+v21#1T,;#7W,=&%+v21#1p#2#40#7,5X#:?;34#:?;50Y,1T,:+v21#1T,;#7W,=&%+v21#1p#2#40#7"%pstring.
Lemma avlF1P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF1P7_0; KS_avlF1P7_1] fx R M V avlF1P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF1P7_0; KS_avlF1P7_1] LibSegJa_avlF1P7.regs0 LibSegJa_avlF1P7.kn0 LibSegJa_avlF1P7.BR LibSegJa_avlF1P7.PSS LibSegJa_avlF1P7.NX0 LibSegJa_avlF1P7.F0 719668 LibSegJa_avlF1P7.seg_sound_ax fx R M V avlF1P7_conc_s. Qed.
Definition KS_avlF2Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2Z.regs0 LibSegJa_avlF2Z.regs_out0).
Lemma KS_avlF2Z_0_ok : BG.kept_ok 60 LibSegJa_avlF2Z.regs0 LibSegJa_avlF2Z.regs_out0 KS_avlF2Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2Z.regs0 LibSegJa_avlF2Z.regs_out1).
Lemma KS_avlF2Z_1_ok : BG.kept_ok 60 LibSegJa_avlF2Z.regs0 LibSegJa_avlF2Z.regs_out1 KS_avlF2Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Ka+/+v21#2#8#7???8000#1,,2,4X#:?;50#:?<04Y,T,:+v21#2T,;#,4X#:?;50#:?;6<Y,1T,:+v21#2T,;#"%pstring.
Lemma avlF2Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF2Z_0; KS_avlF2Z_1] fx R M V avlF2Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF2Z_0; KS_avlF2Z_1] LibSegJa_avlF2Z.regs0 LibSegJa_avlF2Z.kn0 LibSegJa_avlF2Z.BR LibSegJa_avlF2Z.PSS LibSegJa_avlF2Z.NX0 LibSegJa_avlF2Z.F0 719696 LibSegJa_avlF2Z.seg_sound_ax fx R M V avlF2Z_conc_s. Qed.
Definition KS_avlF2P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P1.regs0 LibSegJa_avlF2P1.regs_out0).
Lemma KS_avlF2P1_0_ok : BG.kept_ok 60 LibSegJa_avlF2P1.regs0 LibSegJa_avlF2P1.regs_out0 KS_avlF2P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P1.regs0 LibSegJa_avlF2P1.regs_out1).
Lemma KS_avlF2P1_1_ok : BG.kept_ok 60 LibSegJa_avlF2P1.regs0 LibSegJa_avlF2P1.regs_out1 KS_avlF2P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#1B#&%+v21#2p#2#40#7#,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#1T,=#,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#1T,=#"%pstring.
Lemma avlF2P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P1_0; KS_avlF2P1_1] fx R M V avlF2P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P1_0; KS_avlF2P1_1] LibSegJa_avlF2P1.regs0 LibSegJa_avlF2P1.kn0 LibSegJa_avlF2P1.BR LibSegJa_avlF2P1.PSS LibSegJa_avlF2P1.NX0 LibSegJa_avlF2P1.F0 719696 LibSegJa_avlF2P1.seg_sound_ax fx R M V avlF2P1_conc_s. Qed.
Definition KS_avlF2P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P2.regs0 LibSegJa_avlF2P2.regs_out0).
Lemma KS_avlF2P2_0_ok : BG.kept_ok 60 LibSegJa_avlF2P2.regs0 LibSegJa_avlF2P2.regs_out0 KS_avlF2P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P2.regs0 LibSegJa_avlF2P2.regs_out1).
Lemma KS_avlF2P2_1_ok : BG.kept_ok 60 LibSegJa_avlF2P2.regs0 LibSegJa_avlF2P2.regs_out1 KS_avlF2P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#2B#&%+v21#2p#2#40#7#1,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#2W,=&%+v21#2p#2#40#7,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#2W,=&%+v21#2p#2#40#7"%pstring.
Lemma avlF2P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P2_0; KS_avlF2P2_1] fx R M V avlF2P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P2_0; KS_avlF2P2_1] LibSegJa_avlF2P2.regs0 LibSegJa_avlF2P2.kn0 LibSegJa_avlF2P2.BR LibSegJa_avlF2P2.PSS LibSegJa_avlF2P2.NX0 LibSegJa_avlF2P2.F0 719696 LibSegJa_avlF2P2.seg_sound_ax fx R M V avlF2P2_conc_s. Qed.
Definition KS_avlF2P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P3.regs0 LibSegJa_avlF2P3.regs_out0).
Lemma KS_avlF2P3_0_ok : BG.kept_ok 60 LibSegJa_avlF2P3.regs0 LibSegJa_avlF2P3.regs_out0 KS_avlF2P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P3.regs0 LibSegJa_avlF2P3.regs_out1).
Lemma KS_avlF2P3_1_ok : BG.kept_ok 60 LibSegJa_avlF2P3.regs0 LibSegJa_avlF2P3.regs_out1 KS_avlF2P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#3B#&%+v21#2p#2#40#7#2,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#3W,=&%+v21#2p#2#40#7,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#3W,=&%+v21#2p#2#40#7"%pstring.
Lemma avlF2P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P3_0; KS_avlF2P3_1] fx R M V avlF2P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P3_0; KS_avlF2P3_1] LibSegJa_avlF2P3.regs0 LibSegJa_avlF2P3.kn0 LibSegJa_avlF2P3.BR LibSegJa_avlF2P3.PSS LibSegJa_avlF2P3.NX0 LibSegJa_avlF2P3.F0 719696 LibSegJa_avlF2P3.seg_sound_ax fx R M V avlF2P3_conc_s. Qed.
Definition KS_avlF2P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P4.regs0 LibSegJa_avlF2P4.regs_out0).
Lemma KS_avlF2P4_0_ok : BG.kept_ok 60 LibSegJa_avlF2P4.regs0 LibSegJa_avlF2P4.regs_out0 KS_avlF2P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P4.regs0 LibSegJa_avlF2P4.regs_out1).
Lemma KS_avlF2P4_1_ok : BG.kept_ok 60 LibSegJa_avlF2P4.regs0 LibSegJa_avlF2P4.regs_out1 KS_avlF2P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#4B#&%+v21#2p#2#40#7#3,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#4W,=&%+v21#2p#2#40#7,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#4W,=&%+v21#2p#2#40#7"%pstring.
Lemma avlF2P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P4_0; KS_avlF2P4_1] fx R M V avlF2P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P4_0; KS_avlF2P4_1] LibSegJa_avlF2P4.regs0 LibSegJa_avlF2P4.kn0 LibSegJa_avlF2P4.BR LibSegJa_avlF2P4.PSS LibSegJa_avlF2P4.NX0 LibSegJa_avlF2P4.F0 719696 LibSegJa_avlF2P4.seg_sound_ax fx R M V avlF2P4_conc_s. Qed.
Definition KS_avlF2P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P5.regs0 LibSegJa_avlF2P5.regs_out0).
Lemma KS_avlF2P5_0_ok : BG.kept_ok 60 LibSegJa_avlF2P5.regs0 LibSegJa_avlF2P5.regs_out0 KS_avlF2P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P5.regs0 LibSegJa_avlF2P5.regs_out1).
Lemma KS_avlF2P5_1_ok : BG.kept_ok 60 LibSegJa_avlF2P5.regs0 LibSegJa_avlF2P5.regs_out1 KS_avlF2P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#5B#&%+v21#2p#2#40#7#4,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#5W,=&%+v21#2p#2#40#7,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#5W,=&%+v21#2p#2#40#7"%pstring.
Lemma avlF2P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P5_0; KS_avlF2P5_1] fx R M V avlF2P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P5_0; KS_avlF2P5_1] LibSegJa_avlF2P5.regs0 LibSegJa_avlF2P5.kn0 LibSegJa_avlF2P5.BR LibSegJa_avlF2P5.PSS LibSegJa_avlF2P5.NX0 LibSegJa_avlF2P5.F0 719696 LibSegJa_avlF2P5.seg_sound_ax fx R M V avlF2P5_conc_s. Qed.
Definition KS_avlF2P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P6.regs0 LibSegJa_avlF2P6.regs_out0).
Lemma KS_avlF2P6_0_ok : BG.kept_ok 60 LibSegJa_avlF2P6.regs0 LibSegJa_avlF2P6.regs_out0 KS_avlF2P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P6.regs0 LibSegJa_avlF2P6.regs_out1).
Lemma KS_avlF2P6_1_ok : BG.kept_ok 60 LibSegJa_avlF2P6.regs0 LibSegJa_avlF2P6.regs_out1 KS_avlF2P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#6B#&%+v21#2p#2#40#7#5,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#6W,=&%+v21#2p#2#40#7,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#6W,=&%+v21#2p#2#40#7"%pstring.
Lemma avlF2P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P6_0; KS_avlF2P6_1] fx R M V avlF2P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P6_0; KS_avlF2P6_1] LibSegJa_avlF2P6.regs0 LibSegJa_avlF2P6.kn0 LibSegJa_avlF2P6.BR LibSegJa_avlF2P6.PSS LibSegJa_avlF2P6.NX0 LibSegJa_avlF2P6.F0 719696 LibSegJa_avlF2P6.seg_sound_ax fx R M V avlF2P6_conc_s. Qed.
Definition KS_avlF2P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P7.regs0 LibSegJa_avlF2P7.regs_out0).
Lemma KS_avlF2P7_0_ok : BG.kept_ok 60 LibSegJa_avlF2P7.regs0 LibSegJa_avlF2P7.regs_out0 KS_avlF2P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF2P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF2P7.regs0 LibSegJa_avlF2P7.regs_out1).
Lemma KS_avlF2P7_1_ok : BG.kept_ok 60 LibSegJa_avlF2P7.regs0 LibSegJa_avlF2P7.regs_out1 KS_avlF2P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF2P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#7B#&%+v21#2p#2#40#7#6,,2,5X#:?;50#:?<04Y,T,:+v21#2T,;#7W,=&%+v21#2p#2#40#7,5X#:?;50#:?;6<Y,1T,:+v21#2T,;#7W,=&%+v21#2p#2#40#7"%pstring.
Lemma avlF2P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF2P7_0; KS_avlF2P7_1] fx R M V avlF2P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF2P7_0; KS_avlF2P7_1] LibSegJa_avlF2P7.regs0 LibSegJa_avlF2P7.kn0 LibSegJa_avlF2P7.BR LibSegJa_avlF2P7.PSS LibSegJa_avlF2P7.NX0 LibSegJa_avlF2P7.F0 719696 LibSegJa_avlF2P7.seg_sound_ax fx R M V avlF2P7_conc_s. Qed.
Definition KS_avlF3Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3Z.regs0 LibSegJa_avlF3Z.regs_out0).
Lemma KS_avlF3Z_0_ok : BG.kept_ok 60 LibSegJa_avlF3Z.regs0 LibSegJa_avlF3Z.regs_out0 KS_avlF3Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3Z.regs0 LibSegJa_avlF3Z.regs_out1).
Lemma KS_avlF3Z_1_ok : BG.kept_ok 60 LibSegJa_avlF3Z.regs0 LibSegJa_avlF3Z.regs_out1 KS_avlF3Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Ka+/+v21#3#8#7???8000#1,,2,4X#:?;6<#:?<04Y,T,:+v21#3T,;#,4X#:?;6<#:?;88Y,1T,:+v21#3T,;#"%pstring.
Lemma avlF3Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF3Z_0; KS_avlF3Z_1] fx R M V avlF3Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF3Z_0; KS_avlF3Z_1] LibSegJa_avlF3Z.regs0 LibSegJa_avlF3Z.kn0 LibSegJa_avlF3Z.BR LibSegJa_avlF3Z.PSS LibSegJa_avlF3Z.NX0 LibSegJa_avlF3Z.F0 719724 LibSegJa_avlF3Z.seg_sound_ax fx R M V avlF3Z_conc_s. Qed.
Definition KS_avlF3P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P1.regs0 LibSegJa_avlF3P1.regs_out0).
Lemma KS_avlF3P1_0_ok : BG.kept_ok 60 LibSegJa_avlF3P1.regs0 LibSegJa_avlF3P1.regs_out0 KS_avlF3P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P1.regs0 LibSegJa_avlF3P1.regs_out1).
Lemma KS_avlF3P1_1_ok : BG.kept_ok 60 LibSegJa_avlF3P1.regs0 LibSegJa_avlF3P1.regs_out1 KS_avlF3P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#1B#&%+v21#3p#2#40#7#,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#1T,=#,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#1T,=#"%pstring.
Lemma avlF3P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P1_0; KS_avlF3P1_1] fx R M V avlF3P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P1_0; KS_avlF3P1_1] LibSegJa_avlF3P1.regs0 LibSegJa_avlF3P1.kn0 LibSegJa_avlF3P1.BR LibSegJa_avlF3P1.PSS LibSegJa_avlF3P1.NX0 LibSegJa_avlF3P1.F0 719724 LibSegJa_avlF3P1.seg_sound_ax fx R M V avlF3P1_conc_s. Qed.
Definition KS_avlF3P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P2.regs0 LibSegJa_avlF3P2.regs_out0).
Lemma KS_avlF3P2_0_ok : BG.kept_ok 60 LibSegJa_avlF3P2.regs0 LibSegJa_avlF3P2.regs_out0 KS_avlF3P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P2.regs0 LibSegJa_avlF3P2.regs_out1).
Lemma KS_avlF3P2_1_ok : BG.kept_ok 60 LibSegJa_avlF3P2.regs0 LibSegJa_avlF3P2.regs_out1 KS_avlF3P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#2B#&%+v21#3p#2#40#7#1,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#2W,=&%+v21#3p#2#40#7,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#2W,=&%+v21#3p#2#40#7"%pstring.
Lemma avlF3P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P2_0; KS_avlF3P2_1] fx R M V avlF3P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P2_0; KS_avlF3P2_1] LibSegJa_avlF3P2.regs0 LibSegJa_avlF3P2.kn0 LibSegJa_avlF3P2.BR LibSegJa_avlF3P2.PSS LibSegJa_avlF3P2.NX0 LibSegJa_avlF3P2.F0 719724 LibSegJa_avlF3P2.seg_sound_ax fx R M V avlF3P2_conc_s. Qed.
Definition KS_avlF3P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P3.regs0 LibSegJa_avlF3P3.regs_out0).
Lemma KS_avlF3P3_0_ok : BG.kept_ok 60 LibSegJa_avlF3P3.regs0 LibSegJa_avlF3P3.regs_out0 KS_avlF3P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P3.regs0 LibSegJa_avlF3P3.regs_out1).
Lemma KS_avlF3P3_1_ok : BG.kept_ok 60 LibSegJa_avlF3P3.regs0 LibSegJa_avlF3P3.regs_out1 KS_avlF3P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#3B#&%+v21#3p#2#40#7#2,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#3W,=&%+v21#3p#2#40#7,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#3W,=&%+v21#3p#2#40#7"%pstring.
Lemma avlF3P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P3_0; KS_avlF3P3_1] fx R M V avlF3P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P3_0; KS_avlF3P3_1] LibSegJa_avlF3P3.regs0 LibSegJa_avlF3P3.kn0 LibSegJa_avlF3P3.BR LibSegJa_avlF3P3.PSS LibSegJa_avlF3P3.NX0 LibSegJa_avlF3P3.F0 719724 LibSegJa_avlF3P3.seg_sound_ax fx R M V avlF3P3_conc_s. Qed.
Definition KS_avlF3P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P4.regs0 LibSegJa_avlF3P4.regs_out0).
Lemma KS_avlF3P4_0_ok : BG.kept_ok 60 LibSegJa_avlF3P4.regs0 LibSegJa_avlF3P4.regs_out0 KS_avlF3P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P4.regs0 LibSegJa_avlF3P4.regs_out1).
Lemma KS_avlF3P4_1_ok : BG.kept_ok 60 LibSegJa_avlF3P4.regs0 LibSegJa_avlF3P4.regs_out1 KS_avlF3P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#4B#&%+v21#3p#2#40#7#3,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#4W,=&%+v21#3p#2#40#7,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#4W,=&%+v21#3p#2#40#7"%pstring.
Lemma avlF3P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P4_0; KS_avlF3P4_1] fx R M V avlF3P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P4_0; KS_avlF3P4_1] LibSegJa_avlF3P4.regs0 LibSegJa_avlF3P4.kn0 LibSegJa_avlF3P4.BR LibSegJa_avlF3P4.PSS LibSegJa_avlF3P4.NX0 LibSegJa_avlF3P4.F0 719724 LibSegJa_avlF3P4.seg_sound_ax fx R M V avlF3P4_conc_s. Qed.
Definition KS_avlF3P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P5.regs0 LibSegJa_avlF3P5.regs_out0).
Lemma KS_avlF3P5_0_ok : BG.kept_ok 60 LibSegJa_avlF3P5.regs0 LibSegJa_avlF3P5.regs_out0 KS_avlF3P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P5.regs0 LibSegJa_avlF3P5.regs_out1).
Lemma KS_avlF3P5_1_ok : BG.kept_ok 60 LibSegJa_avlF3P5.regs0 LibSegJa_avlF3P5.regs_out1 KS_avlF3P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#5B#&%+v21#3p#2#40#7#4,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#5W,=&%+v21#3p#2#40#7,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#5W,=&%+v21#3p#2#40#7"%pstring.
Lemma avlF3P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P5_0; KS_avlF3P5_1] fx R M V avlF3P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P5_0; KS_avlF3P5_1] LibSegJa_avlF3P5.regs0 LibSegJa_avlF3P5.kn0 LibSegJa_avlF3P5.BR LibSegJa_avlF3P5.PSS LibSegJa_avlF3P5.NX0 LibSegJa_avlF3P5.F0 719724 LibSegJa_avlF3P5.seg_sound_ax fx R M V avlF3P5_conc_s. Qed.
Definition KS_avlF3P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P6.regs0 LibSegJa_avlF3P6.regs_out0).
Lemma KS_avlF3P6_0_ok : BG.kept_ok 60 LibSegJa_avlF3P6.regs0 LibSegJa_avlF3P6.regs_out0 KS_avlF3P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P6.regs0 LibSegJa_avlF3P6.regs_out1).
Lemma KS_avlF3P6_1_ok : BG.kept_ok 60 LibSegJa_avlF3P6.regs0 LibSegJa_avlF3P6.regs_out1 KS_avlF3P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#6B#&%+v21#3p#2#40#7#5,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#6W,=&%+v21#3p#2#40#7,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#6W,=&%+v21#3p#2#40#7"%pstring.
Lemma avlF3P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P6_0; KS_avlF3P6_1] fx R M V avlF3P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P6_0; KS_avlF3P6_1] LibSegJa_avlF3P6.regs0 LibSegJa_avlF3P6.kn0 LibSegJa_avlF3P6.BR LibSegJa_avlF3P6.PSS LibSegJa_avlF3P6.NX0 LibSegJa_avlF3P6.F0 719724 LibSegJa_avlF3P6.seg_sound_ax fx R M V avlF3P6_conc_s. Qed.
Definition KS_avlF3P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P7.regs0 LibSegJa_avlF3P7.regs_out0).
Lemma KS_avlF3P7_0_ok : BG.kept_ok 60 LibSegJa_avlF3P7.regs0 LibSegJa_avlF3P7.regs_out0 KS_avlF3P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF3P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF3P7.regs0 LibSegJa_avlF3P7.regs_out1).
Lemma KS_avlF3P7_1_ok : BG.kept_ok 60 LibSegJa_avlF3P7.regs0 LibSegJa_avlF3P7.regs_out1 KS_avlF3P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF3P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#7B#&%+v21#3p#2#40#7#6,,2,5X#:?;6<#:?<04Y,T,:+v21#3T,;#7W,=&%+v21#3p#2#40#7,5X#:?;6<#:?;88Y,1T,:+v21#3T,;#7W,=&%+v21#3p#2#40#7"%pstring.
Lemma avlF3P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF3P7_0; KS_avlF3P7_1] fx R M V avlF3P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF3P7_0; KS_avlF3P7_1] LibSegJa_avlF3P7.regs0 LibSegJa_avlF3P7.kn0 LibSegJa_avlF3P7.BR LibSegJa_avlF3P7.PSS LibSegJa_avlF3P7.NX0 LibSegJa_avlF3P7.F0 719724 LibSegJa_avlF3P7.seg_sound_ax fx R M V avlF3P7_conc_s. Qed.
Definition KS_avlF4Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4Z.regs0 LibSegJa_avlF4Z.regs_out0).
Lemma KS_avlF4Z_0_ok : BG.kept_ok 60 LibSegJa_avlF4Z.regs0 LibSegJa_avlF4Z.regs_out0 KS_avlF4Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4Z.regs0 LibSegJa_avlF4Z.regs_out1).
Lemma KS_avlF4Z_1_ok : BG.kept_ok 60 LibSegJa_avlF4Z.regs0 LibSegJa_avlF4Z.regs_out1 KS_avlF4Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4Z_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Ka+/+v21#4#8#7???8000#1,,2,4X#:?;88#:?<04Y,T,:+v21#4T,;#,4X#:?;88#:?;:4Y,1T,:+v21#4T,;#"%pstring.
Lemma avlF4Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlF4Z_0; KS_avlF4Z_1] fx R M V avlF4Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlF4Z_0; KS_avlF4Z_1] LibSegJa_avlF4Z.regs0 LibSegJa_avlF4Z.kn0 LibSegJa_avlF4Z.BR LibSegJa_avlF4Z.PSS LibSegJa_avlF4Z.NX0 LibSegJa_avlF4Z.F0 719752 LibSegJa_avlF4Z.seg_sound_ax fx R M V avlF4Z_conc_s. Qed.
Definition KS_avlF4P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P1.regs0 LibSegJa_avlF4P1.regs_out0).
Lemma KS_avlF4P1_0_ok : BG.kept_ok 60 LibSegJa_avlF4P1.regs0 LibSegJa_avlF4P1.regs_out0 KS_avlF4P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P1.regs0 LibSegJa_avlF4P1.regs_out1).
Lemma KS_avlF4P1_1_ok : BG.kept_ok 60 LibSegJa_avlF4P1.regs0 LibSegJa_avlF4P1.regs_out1 KS_avlF4P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#1B#&%+v21#4p#2#40#7#,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#1T,=#,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#1T,=#"%pstring.
Lemma avlF4P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P1_0; KS_avlF4P1_1] fx R M V avlF4P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P1_0; KS_avlF4P1_1] LibSegJa_avlF4P1.regs0 LibSegJa_avlF4P1.kn0 LibSegJa_avlF4P1.BR LibSegJa_avlF4P1.PSS LibSegJa_avlF4P1.NX0 LibSegJa_avlF4P1.F0 719752 LibSegJa_avlF4P1.seg_sound_ax fx R M V avlF4P1_conc_s. Qed.
Definition KS_avlF4P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P2.regs0 LibSegJa_avlF4P2.regs_out0).
Lemma KS_avlF4P2_0_ok : BG.kept_ok 60 LibSegJa_avlF4P2.regs0 LibSegJa_avlF4P2.regs_out0 KS_avlF4P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P2.regs0 LibSegJa_avlF4P2.regs_out1).
Lemma KS_avlF4P2_1_ok : BG.kept_ok 60 LibSegJa_avlF4P2.regs0 LibSegJa_avlF4P2.regs_out1 KS_avlF4P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#2B#&%+v21#4p#2#40#7#1,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#2W,=&%+v21#4p#2#40#7,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#2W,=&%+v21#4p#2#40#7"%pstring.
Lemma avlF4P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P2_0; KS_avlF4P2_1] fx R M V avlF4P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P2_0; KS_avlF4P2_1] LibSegJa_avlF4P2.regs0 LibSegJa_avlF4P2.kn0 LibSegJa_avlF4P2.BR LibSegJa_avlF4P2.PSS LibSegJa_avlF4P2.NX0 LibSegJa_avlF4P2.F0 719752 LibSegJa_avlF4P2.seg_sound_ax fx R M V avlF4P2_conc_s. Qed.
Definition KS_avlF4P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P3.regs0 LibSegJa_avlF4P3.regs_out0).
Lemma KS_avlF4P3_0_ok : BG.kept_ok 60 LibSegJa_avlF4P3.regs0 LibSegJa_avlF4P3.regs_out0 KS_avlF4P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P3.regs0 LibSegJa_avlF4P3.regs_out1).
Lemma KS_avlF4P3_1_ok : BG.kept_ok 60 LibSegJa_avlF4P3.regs0 LibSegJa_avlF4P3.regs_out1 KS_avlF4P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#3B#&%+v21#4p#2#40#7#2,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#3W,=&%+v21#4p#2#40#7,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#3W,=&%+v21#4p#2#40#7"%pstring.
Lemma avlF4P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P3_0; KS_avlF4P3_1] fx R M V avlF4P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P3_0; KS_avlF4P3_1] LibSegJa_avlF4P3.regs0 LibSegJa_avlF4P3.kn0 LibSegJa_avlF4P3.BR LibSegJa_avlF4P3.PSS LibSegJa_avlF4P3.NX0 LibSegJa_avlF4P3.F0 719752 LibSegJa_avlF4P3.seg_sound_ax fx R M V avlF4P3_conc_s. Qed.
Definition KS_avlF4P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P4.regs0 LibSegJa_avlF4P4.regs_out0).
Lemma KS_avlF4P4_0_ok : BG.kept_ok 60 LibSegJa_avlF4P4.regs0 LibSegJa_avlF4P4.regs_out0 KS_avlF4P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P4.regs0 LibSegJa_avlF4P4.regs_out1).
Lemma KS_avlF4P4_1_ok : BG.kept_ok 60 LibSegJa_avlF4P4.regs0 LibSegJa_avlF4P4.regs_out1 KS_avlF4P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#4B#&%+v21#4p#2#40#7#3,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#4W,=&%+v21#4p#2#40#7,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#4W,=&%+v21#4p#2#40#7"%pstring.
Lemma avlF4P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P4_0; KS_avlF4P4_1] fx R M V avlF4P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P4_0; KS_avlF4P4_1] LibSegJa_avlF4P4.regs0 LibSegJa_avlF4P4.kn0 LibSegJa_avlF4P4.BR LibSegJa_avlF4P4.PSS LibSegJa_avlF4P4.NX0 LibSegJa_avlF4P4.F0 719752 LibSegJa_avlF4P4.seg_sound_ax fx R M V avlF4P4_conc_s. Qed.
Definition KS_avlF4P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P5.regs0 LibSegJa_avlF4P5.regs_out0).
Lemma KS_avlF4P5_0_ok : BG.kept_ok 60 LibSegJa_avlF4P5.regs0 LibSegJa_avlF4P5.regs_out0 KS_avlF4P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P5.regs0 LibSegJa_avlF4P5.regs_out1).
Lemma KS_avlF4P5_1_ok : BG.kept_ok 60 LibSegJa_avlF4P5.regs0 LibSegJa_avlF4P5.regs_out1 KS_avlF4P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#5B#&%+v21#4p#2#40#7#4,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#5W,=&%+v21#4p#2#40#7,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#5W,=&%+v21#4p#2#40#7"%pstring.
Lemma avlF4P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P5_0; KS_avlF4P5_1] fx R M V avlF4P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P5_0; KS_avlF4P5_1] LibSegJa_avlF4P5.regs0 LibSegJa_avlF4P5.kn0 LibSegJa_avlF4P5.BR LibSegJa_avlF4P5.PSS LibSegJa_avlF4P5.NX0 LibSegJa_avlF4P5.F0 719752 LibSegJa_avlF4P5.seg_sound_ax fx R M V avlF4P5_conc_s. Qed.
Definition KS_avlF4P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P6.regs0 LibSegJa_avlF4P6.regs_out0).
Lemma KS_avlF4P6_0_ok : BG.kept_ok 60 LibSegJa_avlF4P6.regs0 LibSegJa_avlF4P6.regs_out0 KS_avlF4P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P6.regs0 LibSegJa_avlF4P6.regs_out1).
Lemma KS_avlF4P6_1_ok : BG.kept_ok 60 LibSegJa_avlF4P6.regs0 LibSegJa_avlF4P6.regs_out1 KS_avlF4P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#6B#&%+v21#4p#2#40#7#5,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#6W,=&%+v21#4p#2#40#7,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#6W,=&%+v21#4p#2#40#7"%pstring.
Lemma avlF4P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P6_0; KS_avlF4P6_1] fx R M V avlF4P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P6_0; KS_avlF4P6_1] LibSegJa_avlF4P6.regs0 LibSegJa_avlF4P6.kn0 LibSegJa_avlF4P6.BR LibSegJa_avlF4P6.PSS LibSegJa_avlF4P6.NX0 LibSegJa_avlF4P6.F0 719752 LibSegJa_avlF4P6.seg_sound_ax fx R M V avlF4P6_conc_s. Qed.
Definition KS_avlF4P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P7.regs0 LibSegJa_avlF4P7.regs_out0).
Lemma KS_avlF4P7_0_ok : BG.kept_ok 60 LibSegJa_avlF4P7.regs0 LibSegJa_avlF4P7.regs_out0 KS_avlF4P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF4P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlF4P7.regs0 LibSegJa_avlF4P7.regs_out1).
Lemma KS_avlF4P7_1_ok : BG.kept_ok 60 LibSegJa_avlF4P7.regs0 LibSegJa_avlF4P7.regs_out1 KS_avlF4P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlF4P7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#7B#&%+v21#4p#2#40#7#6,,2,5X#:?;88#:?<04Y,T,:+v21#4T,;#7W,=&%+v21#4p#2#40#7,5X#:?;88#:?;:4Y,1T,:+v21#4T,;#7W,=&%+v21#4p#2#40#7"%pstring.
Lemma avlF4P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlF4P7_0; KS_avlF4P7_1] fx R M V avlF4P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlF4P7_0; KS_avlF4P7_1] LibSegJa_avlF4P7.regs0 LibSegJa_avlF4P7.kn0 LibSegJa_avlF4P7.BR LibSegJa_avlF4P7.PSS LibSegJa_avlF4P7.NX0 LibSegJa_avlF4P7.F0 719752 LibSegJa_avlF4P7.seg_sound_ax fx R M V avlF4P7_conc_s. Qed.
End PMAVALP2.
