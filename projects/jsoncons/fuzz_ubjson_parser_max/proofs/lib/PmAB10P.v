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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_ab10E LibSegJa_ab10BZ LibSegJa_ab10P1 LibSegJa_ab10P2 LibSegJa_ab10P3 LibSegJa_ab10P4 LibSegJa_ab10P5 LibSegJa_ab10P6 LibSegJa_ab10P7 LibSegJa_ab10T0 LibSegJa_ab10T3 LibSegJa_ab10T4 LibSegJa_ab10T5 LibSegJa_ab10T6 LibSegJa_ab10T7 LibSegJa_ab10T8 LibSegJa_ab10T9 LibSegJa_ab10T10 LibSegJa_ab10T11 LibSegJa_ab10T12 LibSegJa_ab10F LibSegJa_ab10X.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAB10P.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_ab10E_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10E.regs0 LibSegJa_ab10E.regs_out0).
Lemma KS_ab10E_0_ok : BG.kept_ok 60 LibSegJa_ab10E.regs0 LibSegJa_ab10E.regs_out0 KS_ab10E_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10E_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10E.regs0 LibSegJa_ab10E.regs_out1).
Lemma KS_ab10E_1_ok : BG.kept_ok 60 LibSegJa_ab10E.regs0 LibSegJa_ab10E.regs_out1 KS_ab10E_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ab10E_conc_s := ",>A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801010v2#800000000000Hv2#10I_v2#10#10B#v21#800000000000B#v23#3??????,1_v2#8#8,2,6X#;071<#;0840Y,T,2_v2#10T,:#C%_v23#p#2#40#1Lb_v2#8r1,?X#;071<#;0760Y,1T,2_v2#10T,5#7???8000T,6#1??9T,7#23880T,;v21T,<#T,=+v21v23T,>#5T,?#:T,10#1T,11#=D#1%_v23#p#2#40Lb_v2#8r1"%pstring.
Lemma ab10E_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10E_0; KS_ab10E_1] fx R M V ab10E_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10E_0; KS_ab10E_1] LibSegJa_ab10E.regs0 LibSegJa_ab10E.kn0 LibSegJa_ab10E.BR LibSegJa_ab10E.PSS LibSegJa_ab10E.NX0 LibSegJa_ab10E.F0 722716 LibSegJa_ab10E.seg_sound_ax fx R M V ab10E_conc_s. Qed.
Definition KS_ab10BZ_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out0).
Lemma KS_ab10BZ_0_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out0 KS_ab10BZ_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out1).
Lemma KS_ab10BZ_1_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out1 KS_ab10BZ_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out2).
Lemma KS_ab10BZ_2_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out2 KS_ab10BZ_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out3).
Lemma KS_ab10BZ_3_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out3 KS_ab10BZ_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out4).
Lemma KS_ab10BZ_4_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out4 KS_ab10BZ_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out5).
Lemma KS_ab10BZ_5_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out5 KS_ab10BZ_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out6).
Lemma KS_ab10BZ_6_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out6 KS_ab10BZ_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out7).
Lemma KS_ab10BZ_7_ok : BG.kept_ok 60 LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.regs_out7 KS_ab10BZ_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10BZ_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Ka+/v21#8#7???8000#1,,8,7X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,6X#;0760#;0840Y,1T,:#T,<_v25#30D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,8X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,7X#;0760#;0840Y,3T,:#T,<_v25#30D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10BZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10BZ_0; KS_ab10BZ_1; KS_ab10BZ_2; KS_ab10BZ_3; KS_ab10BZ_4; KS_ab10BZ_5; KS_ab10BZ_6; KS_ab10BZ_7] fx R M V ab10BZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10BZ_0; KS_ab10BZ_1; KS_ab10BZ_2; KS_ab10BZ_3; KS_ab10BZ_4; KS_ab10BZ_5; KS_ab10BZ_6; KS_ab10BZ_7] LibSegJa_ab10BZ.regs0 LibSegJa_ab10BZ.kn0 LibSegJa_ab10BZ.BR LibSegJa_ab10BZ.PSS LibSegJa_ab10BZ.NX0 LibSegJa_ab10BZ.F0 722784 LibSegJa_ab10BZ.seg_sound_ax fx R M V ab10BZ_conc_s. Qed.
Definition KS_ab10P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out0).
Lemma KS_ab10P1_0_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out0 KS_ab10P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out1).
Lemma KS_ab10P1_1_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out1 KS_ab10P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out2).
Lemma KS_ab10P1_2_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out2 KS_ab10P1_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out3).
Lemma KS_ab10P1_3_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out3 KS_ab10P1_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out4).
Lemma KS_ab10P1_4_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out4 KS_ab10P1_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out5).
Lemma KS_ab10P1_5_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out5 KS_ab10P1_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out6).
Lemma KS_ab10P1_6_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out6 KS_ab10P1_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out7).
Lemma KS_ab10P1_7_ok : BG.kept_ok 60 LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.regs_out7 KS_ab10P1_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P1_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#1B#&v21#7#,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30T,1<#D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5T,1<#C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30T,1<#D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P1_0; KS_ab10P1_1; KS_ab10P1_2; KS_ab10P1_3; KS_ab10P1_4; KS_ab10P1_5; KS_ab10P1_6; KS_ab10P1_7] fx R M V ab10P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P1_0; KS_ab10P1_1; KS_ab10P1_2; KS_ab10P1_3; KS_ab10P1_4; KS_ab10P1_5; KS_ab10P1_6; KS_ab10P1_7] LibSegJa_ab10P1.regs0 LibSegJa_ab10P1.kn0 LibSegJa_ab10P1.BR LibSegJa_ab10P1.PSS LibSegJa_ab10P1.NX0 LibSegJa_ab10P1.F0 722784 LibSegJa_ab10P1.seg_sound_ax fx R M V ab10P1_conc_s. Qed.
Definition KS_ab10P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out0).
Lemma KS_ab10P2_0_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out0 KS_ab10P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out1).
Lemma KS_ab10P2_1_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out1 KS_ab10P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out2).
Lemma KS_ab10P2_2_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out2 KS_ab10P2_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out3).
Lemma KS_ab10P2_3_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out3 KS_ab10P2_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out4).
Lemma KS_ab10P2_4_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out4 KS_ab10P2_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out5).
Lemma KS_ab10P2_5_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out5 KS_ab10P2_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out6).
Lemma KS_ab10P2_6_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out6 KS_ab10P2_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out7).
Lemma KS_ab10P2_7_ok : BG.kept_ok 60 LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.regs_out7 KS_ab10P2_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P2_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#2B#&v21#7#1,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P2_0; KS_ab10P2_1; KS_ab10P2_2; KS_ab10P2_3; KS_ab10P2_4; KS_ab10P2_5; KS_ab10P2_6; KS_ab10P2_7] fx R M V ab10P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P2_0; KS_ab10P2_1; KS_ab10P2_2; KS_ab10P2_3; KS_ab10P2_4; KS_ab10P2_5; KS_ab10P2_6; KS_ab10P2_7] LibSegJa_ab10P2.regs0 LibSegJa_ab10P2.kn0 LibSegJa_ab10P2.BR LibSegJa_ab10P2.PSS LibSegJa_ab10P2.NX0 LibSegJa_ab10P2.F0 722784 LibSegJa_ab10P2.seg_sound_ax fx R M V ab10P2_conc_s. Qed.
Definition KS_ab10P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out0).
Lemma KS_ab10P3_0_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out0 KS_ab10P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out1).
Lemma KS_ab10P3_1_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out1 KS_ab10P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out2).
Lemma KS_ab10P3_2_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out2 KS_ab10P3_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out3).
Lemma KS_ab10P3_3_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out3 KS_ab10P3_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out4).
Lemma KS_ab10P3_4_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out4 KS_ab10P3_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out5).
Lemma KS_ab10P3_5_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out5 KS_ab10P3_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out6).
Lemma KS_ab10P3_6_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out6 KS_ab10P3_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out7).
Lemma KS_ab10P3_7_ok : BG.kept_ok 60 LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.regs_out7 KS_ab10P3_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P3_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#3B#&v21#7#2,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P3_0; KS_ab10P3_1; KS_ab10P3_2; KS_ab10P3_3; KS_ab10P3_4; KS_ab10P3_5; KS_ab10P3_6; KS_ab10P3_7] fx R M V ab10P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P3_0; KS_ab10P3_1; KS_ab10P3_2; KS_ab10P3_3; KS_ab10P3_4; KS_ab10P3_5; KS_ab10P3_6; KS_ab10P3_7] LibSegJa_ab10P3.regs0 LibSegJa_ab10P3.kn0 LibSegJa_ab10P3.BR LibSegJa_ab10P3.PSS LibSegJa_ab10P3.NX0 LibSegJa_ab10P3.F0 722784 LibSegJa_ab10P3.seg_sound_ax fx R M V ab10P3_conc_s. Qed.
Definition KS_ab10P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out0).
Lemma KS_ab10P4_0_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out0 KS_ab10P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out1).
Lemma KS_ab10P4_1_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out1 KS_ab10P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out2).
Lemma KS_ab10P4_2_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out2 KS_ab10P4_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out3).
Lemma KS_ab10P4_3_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out3 KS_ab10P4_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out4).
Lemma KS_ab10P4_4_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out4 KS_ab10P4_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out5).
Lemma KS_ab10P4_5_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out5 KS_ab10P4_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out6).
Lemma KS_ab10P4_6_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out6 KS_ab10P4_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out7).
Lemma KS_ab10P4_7_ok : BG.kept_ok 60 LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.regs_out7 KS_ab10P4_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P4_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#4B#&v21#7#3,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P4_0; KS_ab10P4_1; KS_ab10P4_2; KS_ab10P4_3; KS_ab10P4_4; KS_ab10P4_5; KS_ab10P4_6; KS_ab10P4_7] fx R M V ab10P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P4_0; KS_ab10P4_1; KS_ab10P4_2; KS_ab10P4_3; KS_ab10P4_4; KS_ab10P4_5; KS_ab10P4_6; KS_ab10P4_7] LibSegJa_ab10P4.regs0 LibSegJa_ab10P4.kn0 LibSegJa_ab10P4.BR LibSegJa_ab10P4.PSS LibSegJa_ab10P4.NX0 LibSegJa_ab10P4.F0 722784 LibSegJa_ab10P4.seg_sound_ax fx R M V ab10P4_conc_s. Qed.
Definition KS_ab10P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out0).
Lemma KS_ab10P5_0_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out0 KS_ab10P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out1).
Lemma KS_ab10P5_1_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out1 KS_ab10P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out2).
Lemma KS_ab10P5_2_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out2 KS_ab10P5_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out3).
Lemma KS_ab10P5_3_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out3 KS_ab10P5_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out4).
Lemma KS_ab10P5_4_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out4 KS_ab10P5_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out5).
Lemma KS_ab10P5_5_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out5 KS_ab10P5_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out6).
Lemma KS_ab10P5_6_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out6 KS_ab10P5_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out7).
Lemma KS_ab10P5_7_ok : BG.kept_ok 60 LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.regs_out7 KS_ab10P5_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P5_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#5B#&v21#7#4,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P5_0; KS_ab10P5_1; KS_ab10P5_2; KS_ab10P5_3; KS_ab10P5_4; KS_ab10P5_5; KS_ab10P5_6; KS_ab10P5_7] fx R M V ab10P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P5_0; KS_ab10P5_1; KS_ab10P5_2; KS_ab10P5_3; KS_ab10P5_4; KS_ab10P5_5; KS_ab10P5_6; KS_ab10P5_7] LibSegJa_ab10P5.regs0 LibSegJa_ab10P5.kn0 LibSegJa_ab10P5.BR LibSegJa_ab10P5.PSS LibSegJa_ab10P5.NX0 LibSegJa_ab10P5.F0 722784 LibSegJa_ab10P5.seg_sound_ax fx R M V ab10P5_conc_s. Qed.
Definition KS_ab10P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out0).
Lemma KS_ab10P6_0_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out0 KS_ab10P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out1).
Lemma KS_ab10P6_1_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out1 KS_ab10P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out2).
Lemma KS_ab10P6_2_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out2 KS_ab10P6_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out3).
Lemma KS_ab10P6_3_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out3 KS_ab10P6_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out4).
Lemma KS_ab10P6_4_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out4 KS_ab10P6_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out5).
Lemma KS_ab10P6_5_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out5 KS_ab10P6_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out6).
Lemma KS_ab10P6_6_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out6 KS_ab10P6_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out7).
Lemma KS_ab10P6_7_ok : BG.kept_ok 60 LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.regs_out7 KS_ab10P6_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P6_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#6B#&v21#7#5,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P6_0; KS_ab10P6_1; KS_ab10P6_2; KS_ab10P6_3; KS_ab10P6_4; KS_ab10P6_5; KS_ab10P6_6; KS_ab10P6_7] fx R M V ab10P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P6_0; KS_ab10P6_1; KS_ab10P6_2; KS_ab10P6_3; KS_ab10P6_4; KS_ab10P6_5; KS_ab10P6_6; KS_ab10P6_7] LibSegJa_ab10P6.regs0 LibSegJa_ab10P6.kn0 LibSegJa_ab10P6.BR LibSegJa_ab10P6.PSS LibSegJa_ab10P6.NX0 LibSegJa_ab10P6.F0 722784 LibSegJa_ab10P6.seg_sound_ax fx R M V ab10P6_conc_s. Qed.
Definition KS_ab10P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out0).
Lemma KS_ab10P7_0_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out0 KS_ab10P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out1).
Lemma KS_ab10P7_1_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out1 KS_ab10P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out2).
Lemma KS_ab10P7_2_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out2 KS_ab10P7_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out3).
Lemma KS_ab10P7_3_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out3 KS_ab10P7_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out4).
Lemma KS_ab10P7_4_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out4 KS_ab10P7_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out5).
Lemma KS_ab10P7_5_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out5 KS_ab10P7_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out6).
Lemma KS_ab10P7_6_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out6 KS_ab10P7_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out7).
Lemma KS_ab10P7_7_ok : BG.kept_ok 60 LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.regs_out7 KS_ab10P7_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10P7_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????Nav21v25B#v25#??Na+/v21#8#7???8000#7B#&v21#7#6,,8,8X#;0760#;07?<Y,T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#;0760#;0840Y,1T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,9X#;0760#;07?<Y,2T,:+v21#1T,;+v21#1T,<#5W,1<&v21#7C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,8X#;0760#;0840Y,3T,:#T,<_v25#30W,1<&v21#7D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,:X#;0760#;0840Y,4T,:#W,<&%+v25^#?#?????????????=3p#2#40#??W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;07:0Y,5W,<%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#23880p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#;0760#;0840Y,6T,:#W,<&%+v25^#?#?????????????=3p#2#40#??T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,7X#;0760#;07?<Y,7T,:+v21#1T,;+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ab10P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10P7_0; KS_ab10P7_1; KS_ab10P7_2; KS_ab10P7_3; KS_ab10P7_4; KS_ab10P7_5; KS_ab10P7_6; KS_ab10P7_7] fx R M V ab10P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10P7_0; KS_ab10P7_1; KS_ab10P7_2; KS_ab10P7_3; KS_ab10P7_4; KS_ab10P7_5; KS_ab10P7_6; KS_ab10P7_7] LibSegJa_ab10P7.regs0 LibSegJa_ab10P7.kn0 LibSegJa_ab10P7.BR LibSegJa_ab10P7.PSS LibSegJa_ab10P7.NX0 LibSegJa_ab10P7.F0 722784 LibSegJa_ab10P7.seg_sound_ax fx R M V ab10P7_conc_s. Qed.
Definition KS_ab10T0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T0.regs0 LibSegJa_ab10T0.regs_out0).
Lemma KS_ab10T0_ok : BG.kept_ok 60 LibSegJa_ab10T0.regs0 LibSegJa_ab10T0.regs_out0 KS_ab10T0 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T0_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#23880S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<710#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#1T,1<#"%pstring.
Lemma ab10T0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T0] fx R M V ab10T0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T0] LibSegJa_ab10T0.regs0 LibSegJa_ab10T0.kn0 LibSegJa_ab10T0.BR LibSegJa_ab10T0.PSS LibSegJa_ab10T0.NX0 LibSegJa_ab10T0.F0 722848 LibSegJa_ab10T0.seg_sound_ax fx R M V ab10T0_conc_s. Qed.
Definition KS_ab10T3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T3.regs0 LibSegJa_ab10T3.regs_out0).
Lemma KS_ab10T3_ok : BG.kept_ok 60 LibSegJa_ab10T3.regs0 LibSegJa_ab10T3.regs_out0 KS_ab10T3 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T3_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#2388<S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<711#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T3] fx R M V ab10T3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T3] LibSegJa_ab10T3.regs0 LibSegJa_ab10T3.kn0 LibSegJa_ab10T3.BR LibSegJa_ab10T3.PSS LibSegJa_ab10T3.NX0 LibSegJa_ab10T3.F0 722848 LibSegJa_ab10T3.seg_sound_ax fx R M V ab10T3_conc_s. Qed.
Definition KS_ab10T4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T4.regs0 LibSegJa_ab10T4.regs_out0).
Lemma KS_ab10T4_ok : BG.kept_ok 60 LibSegJa_ab10T4.regs0 LibSegJa_ab10T4.regs_out0 KS_ab10T4 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T4_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#23890S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<712#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T4] fx R M V ab10T4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T4] LibSegJa_ab10T4.regs0 LibSegJa_ab10T4.kn0 LibSegJa_ab10T4.BR LibSegJa_ab10T4.PSS LibSegJa_ab10T4.NX0 LibSegJa_ab10T4.F0 722848 LibSegJa_ab10T4.seg_sound_ax fx R M V ab10T4_conc_s. Qed.
Definition KS_ab10T5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T5.regs0 LibSegJa_ab10T5.regs_out0).
Lemma KS_ab10T5_ok : BG.kept_ok 60 LibSegJa_ab10T5.regs0 LibSegJa_ab10T5.regs_out0 KS_ab10T5 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T5_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#23894S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<712#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T5] fx R M V ab10T5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T5] LibSegJa_ab10T5.regs0 LibSegJa_ab10T5.kn0 LibSegJa_ab10T5.BR LibSegJa_ab10T5.PSS LibSegJa_ab10T5.NX0 LibSegJa_ab10T5.F0 722848 LibSegJa_ab10T5.seg_sound_ax fx R M V ab10T5_conc_s. Qed.
Definition KS_ab10T6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T6.regs0 LibSegJa_ab10T6.regs_out0).
Lemma KS_ab10T6_ok : BG.kept_ok 60 LibSegJa_ab10T6.regs0 LibSegJa_ab10T6.regs_out0 KS_ab10T6 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T6_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#23898S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<713#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T6] fx R M V ab10T6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T6] LibSegJa_ab10T6.regs0 LibSegJa_ab10T6.kn0 LibSegJa_ab10T6.BR LibSegJa_ab10T6.PSS LibSegJa_ab10T6.NX0 LibSegJa_ab10T6.F0 722848 LibSegJa_ab10T6.seg_sound_ax fx R M V ab10T6_conc_s. Qed.
Definition KS_ab10T7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T7.regs0 LibSegJa_ab10T7.regs_out0).
Lemma KS_ab10T7_ok : BG.kept_ok 60 LibSegJa_ab10T7.regs0 LibSegJa_ab10T7.regs_out0 KS_ab10T7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T7_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#2389<S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<713#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T7] fx R M V ab10T7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T7] LibSegJa_ab10T7.regs0 LibSegJa_ab10T7.kn0 LibSegJa_ab10T7.BR LibSegJa_ab10T7.PSS LibSegJa_ab10T7.NX0 LibSegJa_ab10T7.F0 722848 LibSegJa_ab10T7.seg_sound_ax fx R M V ab10T7_conc_s. Qed.
Definition KS_ab10T8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T8.regs0 LibSegJa_ab10T8.regs_out0).
Lemma KS_ab10T8_ok : BG.kept_ok 60 LibSegJa_ab10T8.regs0 LibSegJa_ab10T8.regs_out0 KS_ab10T8 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T8_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#238:0S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<714#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T8] fx R M V ab10T8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T8] LibSegJa_ab10T8.regs0 LibSegJa_ab10T8.kn0 LibSegJa_ab10T8.BR LibSegJa_ab10T8.PSS LibSegJa_ab10T8.NX0 LibSegJa_ab10T8.F0 722848 LibSegJa_ab10T8.seg_sound_ax fx R M V ab10T8_conc_s. Qed.
Definition KS_ab10T9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T9.regs0 LibSegJa_ab10T9.regs_out0).
Lemma KS_ab10T9_ok : BG.kept_ok 60 LibSegJa_ab10T9.regs0 LibSegJa_ab10T9.regs_out0 KS_ab10T9 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T9_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#238:4S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<714#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T9] fx R M V ab10T9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T9] LibSegJa_ab10T9.regs0 LibSegJa_ab10T9.kn0 LibSegJa_ab10T9.BR LibSegJa_ab10T9.PSS LibSegJa_ab10T9.NX0 LibSegJa_ab10T9.F0 722848 LibSegJa_ab10T9.seg_sound_ax fx R M V ab10T9_conc_s. Qed.
Definition KS_ab10T10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T10.regs0 LibSegJa_ab10T10.regs_out0).
Lemma KS_ab10T10_ok : BG.kept_ok 60 LibSegJa_ab10T10.regs0 LibSegJa_ab10T10.regs_out0 KS_ab10T10 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T10_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#238:8S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<715#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T10] fx R M V ab10T10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T10] LibSegJa_ab10T10.regs0 LibSegJa_ab10T10.kn0 LibSegJa_ab10T10.BR LibSegJa_ab10T10.PSS LibSegJa_ab10T10.NX0 LibSegJa_ab10T10.F0 722848 LibSegJa_ab10T10.seg_sound_ax fx R M V ab10T10_conc_s. Qed.
Definition KS_ab10T11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T11.regs0 LibSegJa_ab10T11.regs_out0).
Lemma KS_ab10T11_ok : BG.kept_ok 60 LibSegJa_ab10T11.regs0 LibSegJa_ab10T11.regs_out0 KS_ab10T11 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T11_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#238:<S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Ka#7???<715#1,,1,6X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#"%pstring.
Lemma ab10T11_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ab10T11] fx R M V ab10T11_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ab10T11] LibSegJa_ab10T11.regs0 LibSegJa_ab10T11.kn0 LibSegJa_ab10T11.BR LibSegJa_ab10T11.PSS LibSegJa_ab10T11.NX0 LibSegJa_ab10T11.F0 722848 LibSegJa_ab10T11.seg_sound_ax fx R M V ab10T11_conc_s. Qed.
Definition KS_ab10T12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10T12.regs0 LibSegJa_ab10T12.regs_out0).
Lemma KS_ab10T12_ok : BG.kept_ok 60 LibSegJa_ab10T12.regs0 LibSegJa_ab10T12.regs_out0 KS_ab10T12 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10T12_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<#238;0S,=v22S,>#5S,?#:S,10#1S,11#=O#10000#134000B#v21#800000000000B#1v22#800000000000Na#7???<716#4,,1,7X#;07:0#;07?<Y,T,:+v21#1T,;+v21#1T,<#5T,1<#4T,1=#3"%pstring.
Lemma ab10T12_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10T12] fx R M V ab10T12_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10T12] LibSegJa_ab10T12.regs0 LibSegJa_ab10T12.kn0 LibSegJa_ab10T12.BR LibSegJa_ab10T12.PSS LibSegJa_ab10T12.NX0 LibSegJa_ab10T12.F0 722848 LibSegJa_ab10T12.seg_sound_ax fx R M V ab10T12_conc_s. Qed.
Definition KS_ab10F_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10F.regs0 LibSegJa_ab10F.regs_out0).
Lemma KS_ab10F_0_ok : BG.kept_ok 60 LibSegJa_ab10F.regs0 LibSegJa_ab10F.regs_out0 KS_ab10F_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10F_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10F.regs0 LibSegJa_ab10F.regs_out1).
Lemma KS_ab10F_1_ok : BG.kept_ok 60 LibSegJa_ab10F.regs0 LibSegJa_ab10F.regs_out1 KS_ab10F_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10F_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2_v2#10S,5#7???8000S,6#1??9S,7#23880S,:v21S,;v21S,<v24S,=v22S,>#5S,?#:S,10#1S,11#=B#v21#800000000000B#1v22#800000000000B#v24^#?#???????????????,,2,3X#;07?<#;0760Y,Cv21v22,5X#;07?<#;0840Y,1W,:c%+v24^#?#??????????????;p#2#40#1T,<_v24#5Dv22v21"%pstring.
Lemma ab10F_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10F_0; KS_ab10F_1] fx R M V ab10F_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10F_0; KS_ab10F_1] LibSegJa_ab10F.regs0 LibSegJa_ab10F.kn0 LibSegJa_ab10F.BR LibSegJa_ab10F.PSS LibSegJa_ab10F.NX0 LibSegJa_ab10F.F0 722940 LibSegJa_ab10F.seg_sound_ax fx R M V ab10F_conc_s. Qed.
Definition KS_ab10X : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ab10X.regs0 LibSegJa_ab10X.regs_out0).
Lemma KS_ab10X_ok : BG.kept_ok 60 LibSegJa_ab10X.regs0 LibSegJa_ab10X.regs_out0 KS_ab10X = true. Proof. vm_compute. reflexivity. Qed.
Definition ab10X_conc_s := ",6A#v2p#2#40A#v28p#2#40S,2_v2#10B#7???7?801010v2#800000000000Hv2#10La_v2#8v28,,1,4X#;0840#;0848Y,T,1v28T,2v2"%pstring.
Lemma ab10X_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ab10X] fx R M V ab10X_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ab10X] LibSegJa_ab10X.regs0 LibSegJa_ab10X.kn0 LibSegJa_ab10X.BR LibSegJa_ab10X.PSS LibSegJa_ab10X.NX0 LibSegJa_ab10X.F0 723008 LibSegJa_ab10X.seg_sound_ax fx R M V ab10X_conc_s. Qed.
End PMAB10P.
