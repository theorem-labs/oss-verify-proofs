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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_b10E LibSegJs_b10B LibSegJs_b10J LibSegJs_b10F.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMB10P.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_b10E_0 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10E.regs0 LibSegJs_b10E.regs_out0).
Lemma KS_b10E_0_ok : BG.kept_ok 52 LibSegJs_b10E.regs0 LibSegJs_b10E.regs_out0 KS_b10E_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10E_1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10E.regs0 LibSegJs_b10E.regs_out1).
Lemma KS_b10E_1_ok : BG.kept_ok 52 LibSegJs_b10E.regs0 LibSegJs_b10E.regs_out1 KS_b10E_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition b10E_conc_s := ",8A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#v21#800000000000B#v22#3??????,,2,4X#37000#3708<Y,T,:#C%_v22#p#2#40#1,;X#37000#3702<Y,1T,5#T,;+v21v22T,<#5T,=#:T,>#1T,?#=T,10#1??9T,11#139;<D#1%_v22#p#2#40"%pstring.
Lemma b10E_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_b10E_0; KS_b10E_1] fx R M V b10E_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_b10E_0; KS_b10E_1] LibSegJs_b10E.regs0 LibSegJs_b10E.kn0 LibSegJs_b10E.BR LibSegJs_b10E.PSS LibSegJs_b10E.NX0 LibSegJs_b10E.F0 225280 LibSegJs_b10E.seg_sound_ax fx R M V b10E_conc_s. Qed.
Definition KS_b10B_0 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out0).
Lemma KS_b10B_0_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out0 KS_b10B_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out1).
Lemma KS_b10B_1_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out1 KS_b10B_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_2 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out2).
Lemma KS_b10B_2_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out2 KS_b10B_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_3 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out3).
Lemma KS_b10B_3_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out3 KS_b10B_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_4 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out4).
Lemma KS_b10B_4_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out4 KS_b10B_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_5 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out5).
Lemma KS_b10B_5_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out5 KS_b10B_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_6 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out6).
Lemma KS_b10B_6_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out6 KS_b10B_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10B_7 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out7).
Lemma KS_b10B_7_ok : BG.kept_ok 52 LibSegJs_b10B.regs0 LibSegJs_b10B.regs_out7 KS_b10B_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition b10B_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,5v24S,:v21S,;v22S,<#5S,=#:S,>#1S,?#=S,10#1??9S,11#139;<B#v21#800000000000B#1v22#800000000000B#1_v22v21#4000000Nav21v25B#v25#??O#10000#;60=0,,8,6X#3702<#37078Y,T,5#5T,:+v21#1C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,7X#3702<#37078Y,1T,5#5T,:+v21#1C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,6X#3702<#37078Y,2T,:+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#3702<#3705<Y,3W,5%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#139;<p#2#40W,6&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,6X#3702<#3708<Y,4T,5_v25#30T,:#D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,7X#3702<#3708<Y,5T,5_v25#30T,:#D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,9X#3702<#3708<Y,6W,5&%+v25^#?#?????????????=3p#2#40#??T,6_v25#2=T,:#D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,:X#3702<#3708<Y,7W,5&%+v25^#?#?????????????=3p#2#40#??W,6&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1T,:#C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma b10B_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_b10B_0; KS_b10B_1; KS_b10B_2; KS_b10B_3; KS_b10B_4; KS_b10B_5; KS_b10B_6; KS_b10B_7] fx R M V b10B_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_b10B_0; KS_b10B_1; KS_b10B_2; KS_b10B_3; KS_b10B_4; KS_b10B_5; KS_b10B_6; KS_b10B_7] LibSegJs_b10B.regs0 LibSegJs_b10B.kn0 LibSegJs_b10B.BR LibSegJs_b10B.PSS LibSegJs_b10B.NX0 LibSegJs_b10B.F0 225324 LibSegJs_b10B.seg_sound_ax fx R M V b10B_conc_s. Qed.
Definition KS_b10J : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10J.regs0 LibSegJs_b10J.regs_out0).
Lemma KS_b10J_ok : BG.kept_ok 52 LibSegJs_b10J.regs0 LibSegJs_b10J.regs_out0 KS_b10J = true. Proof. vm_compute. reflexivity. Qed.
Definition b10J_conc_s := ",>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2S,5v24S,:v21S,;v22S,<#5S,=#:S,>#1S,?#=S,10#1??9S,11#139;<,,1,3X#37060#37078Y,T,:+v21#1"%pstring.
Lemma b10J_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_b10J] fx R M V b10J_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_b10J] LibSegJs_b10J.regs0 LibSegJs_b10J.kn0 LibSegJs_b10J.BR LibSegJs_b10J.PSS LibSegJs_b10J.NX0 LibSegJs_b10J.F0 225376 LibSegJs_b10J.seg_sound_ax fx R M V b10J_conc_s. Qed.
Definition KS_b10F_0 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10F.regs0 LibSegJs_b10F.regs_out0).
Lemma KS_b10F_0_ok : BG.kept_ok 52 LibSegJs_b10F.regs0 LibSegJs_b10F.regs_out0 KS_b10F_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_b10F_1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_b10F.regs0 LibSegJs_b10F.regs_out1).
Lemma KS_b10F_1_ok : BG.kept_ok 52 LibSegJs_b10F.regs0 LibSegJs_b10F.regs_out1 KS_b10F_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition b10F_conc_s := ",>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2S,5v24S,:v21S,;v22S,<#5S,=#:S,>#1S,?#=S,10#1??9S,11#139;<,,2,3X#37078#3702<Y,Cv21v22,5X#37078#37084Y,1T,5_v24#5W,:c%+v24^#?#??????????????;p#2#40#1Dv22v21"%pstring.
Lemma b10F_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_b10F_0; KS_b10F_1] fx R M V b10F_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_b10F_0; KS_b10F_1] LibSegJs_b10F.regs0 LibSegJs_b10F.kn0 LibSegJs_b10F.BR LibSegJs_b10F.PSS LibSegJs_b10F.NX0 LibSegJs_b10F.F0 225400 LibSegJs_b10F.seg_sound_ax fx R M V b10F_conc_s. Qed.
End PMB10P.
