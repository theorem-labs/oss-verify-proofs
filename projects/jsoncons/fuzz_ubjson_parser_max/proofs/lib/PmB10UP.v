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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_ub10E LibSegJu_ub10B LibSegJu_ub10J LibSegJu_ub10F.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMB10UP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_ub10E_0 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10E.regs0 LibSegJu_ub10E.regs_out0).
Lemma KS_ub10E_0_ok : BG.kept_ok 52 LibSegJu_ub10E.regs0 LibSegJu_ub10E.regs_out0 KS_ub10E_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10E_1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10E.regs0 LibSegJu_ub10E.regs_out1).
Lemma KS_ub10E_1_ok : BG.kept_ok 52 LibSegJu_ub10E.regs0 LibSegJu_ub10E.regs_out1 KS_ub10E_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ub10E_conc_s := ",8A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#1v21#800000000000B#v22#3??????,,2,7X#37=;8#37>70Y,T,:#T,<+v21v22T,=#1T,>#C%_v22#p#2#40#1,=X#37=;8#37>00Y,1T,5#139?0T,6v21T,7#T,;#5T,<+v21v22T,=#:T,>#2T,?#1T,10#=T,11#1??9D#1%_v22#p#2#40"%pstring.
Lemma ub10E_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ub10E_0; KS_ub10E_1] fx R M V ub10E_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ub10E_0; KS_ub10E_1] LibSegJu_ub10E.regs0 LibSegJu_ub10E.kn0 LibSegJu_ub10E.BR LibSegJu_ub10E.PSS LibSegJu_ub10E.NX0 LibSegJu_ub10E.F0 228792 LibSegJu_ub10E.seg_sound_ax fx R M V ub10E_conc_s. Qed.
Definition KS_ub10B_0 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out0).
Lemma KS_ub10B_0_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out0 KS_ub10B_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out1).
Lemma KS_ub10B_1_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out1 KS_ub10B_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_2 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out2).
Lemma KS_ub10B_2_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out2 KS_ub10B_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_3 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out3).
Lemma KS_ub10B_3_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out3 KS_ub10B_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_4 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out4).
Lemma KS_ub10B_4_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out4 KS_ub10B_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_5 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out5).
Lemma KS_ub10B_5_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out5 KS_ub10B_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_6 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out6).
Lemma KS_ub10B_6_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out6 KS_ub10B_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10B_7 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out7).
Lemma KS_ub10B_7_ok : BG.kept_ok 52 LibSegJu_ub10B.regs0 LibSegJu_ub10B.regs_out7 KS_ub10B_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ub10B_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,5#139?0S,6v21S,7v24S,:v21S,;#5S,<v22S,=#:S,>#2S,?#1S,10#=S,11#1??9B#1v21#800000000000B#1v22#800000000000B#1_v22v21#4000000Nav21v25B#v25#??O#10000#;7120,,8,7X#37>00#37>5<Y,T,6+v21#1T,7#5T,:+v21#1C%+v25^#?#?????????????=0p#2#40#:C%_v24#5p#2#40#1,8X#37>00#37>5<Y,1T,6+v21#1T,7#5T,:+v21#1C%+v25^#?#?????????????=0p#2#40#:C%_v24#1p#2#40#1D#1%_v24#5p#2#40,7X#37>00#37>5<Y,2T,6+v21#1T,:+v21#1D#1%_v24#p#2#40D#1%_v24#1p#2#40D#1%_v24#5p#2#40,9X#37>00#37>34Y,3W,7%+%*#4&%+v25^#?#?????????????=3p#2#40#??p#2#40#139?0p#2#40W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1D#1%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,6X#37>00#37>70Y,4T,7_v25#30T,:#D#:%+v25^#?#?????????????=0p#2#40C%_v24#5p#2#40#1,7X#37>00#37>70Y,5T,7_v25#30T,:#D#:%+v25^#?#?????????????=0p#2#40C%_v24#1p#2#40#1D#1%_v24#5p#2#40,9X#37>00#37>70Y,6W,7&%+v25^#?#?????????????=3p#2#40#??T,:#T,1<_v25#2=D#=&%+v25^#?#?????????????=3p#2#40#??C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40,:X#37>00#37>70Y,7W,7&%+v25^#?#?????????????=3p#2#40#??T,:#W,1<&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1C%_&/#1??9p#2%%+v25^#?#?????????????=3p#2#40#40#1#p#2#40#1C&%+v25^#?#?????????????=3p#2#40#??#=C%_v24#p#2#40#1D#1%_v24#1p#2#40D#1%_v24#5p#2#40"%pstring.
Lemma ub10B_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ub10B_0; KS_ub10B_1; KS_ub10B_2; KS_ub10B_3; KS_ub10B_4; KS_ub10B_5; KS_ub10B_6; KS_ub10B_7] fx R M V ub10B_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ub10B_0; KS_ub10B_1; KS_ub10B_2; KS_ub10B_3; KS_ub10B_4; KS_ub10B_5; KS_ub10B_6; KS_ub10B_7] LibSegJu_ub10B.regs0 LibSegJu_ub10B.kn0 LibSegJu_ub10B.BR LibSegJu_ub10B.PSS LibSegJu_ub10B.NX0 LibSegJu_ub10B.F0 228864 LibSegJu_ub10B.seg_sound_ax fx R M V ub10B_conc_s. Qed.
Definition KS_ub10J : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10J.regs0 LibSegJu_ub10J.regs_out0).
Lemma KS_ub10J_ok : BG.kept_ok 52 LibSegJu_ub10J.regs0 LibSegJu_ub10J.regs_out0 KS_ub10J = true. Proof. vm_compute. reflexivity. Qed.
Definition ub10J_conc_s := ",11A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2S,5#139?0S,6v21S,7v24S,:v21S,;#5S,<v22S,=#:S,>#2S,?#1S,10#=S,11#1??9B#1v21#800000000000,,1,4X#37>38#37>5<Y,T,6+v21#1T,:+v21#1"%pstring.
Lemma ub10J_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ub10J] fx R M V ub10J_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ub10J] LibSegJu_ub10J.regs0 LibSegJu_ub10J.kn0 LibSegJu_ub10J.BR LibSegJu_ub10J.PSS LibSegJu_ub10J.NX0 LibSegJu_ub10J.F0 228920 LibSegJu_ub10J.seg_sound_ax fx R M V ub10J_conc_s. Qed.
Definition KS_ub10F_0 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10F.regs0 LibSegJu_ub10F.regs_out0).
Lemma KS_ub10F_0_ok : BG.kept_ok 52 LibSegJu_ub10F.regs0 LibSegJu_ub10F.regs_out0 KS_ub10F_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ub10F_1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_ub10F.regs0 LibSegJu_ub10F.regs_out1).
Lemma KS_ub10F_1_ok : BG.kept_ok 52 LibSegJu_ub10F.regs0 LibSegJu_ub10F.regs_out1 KS_ub10F_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ub10F_conc_s := ",10A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2S,5#139?0S,6v21S,7v24S,:v21S,;#5S,<v22S,=#:S,>#2S,?#1S,10#=S,11#1??9,,2,3X#37>5<#37>00Y,Cv21v22,5X#37>5<#37>68Y,1T,7_v24#5W,:c%+v24^#?#??????????????;p#2#40#1Dv22v21"%pstring.
Lemma ub10F_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ub10F_0; KS_ub10F_1] fx R M V ub10F_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ub10F_0; KS_ub10F_1] LibSegJu_ub10F.regs0 LibSegJu_ub10F.kn0 LibSegJu_ub10F.BR LibSegJu_ub10F.PSS LibSegJu_ub10F.NX0 LibSegJu_ub10F.F0 228956 LibSegJu_ub10F.seg_sound_ax fx R M V ub10F_conc_s. Qed.
End PMB10UP.
