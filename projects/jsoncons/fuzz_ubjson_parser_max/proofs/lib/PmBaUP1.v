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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_ubaA0 LibSegJu_ubaA1 LibSegJu_ubaKe LibSegJu_ubaKh LibSegJu_ubaKd LibSegJu_ubaKl LibSegJu_ubaKu LibSegJu_ubaZ LibSegJu_ubaC1 LibSegJu_ubaCe LibSegJu_ubaCx LibSegJu_ubaT1 LibSegJu_ubaT2z LibSegJu_ubaT2p LibSegJu_ubaT3e LibSegJu_ubaT3h LibSegJu_ubaT3l LibSegJu_ubaT3u LibSegJu_ubaT4 LibSegJu_ubaTe LibSegJu_ubaTx.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAUP1.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_ubaA0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaA0.regs0 LibSegJu_ubaA0.regs_out0).
Lemma KS_ubaA0_ok : BG.kept_ok 64 LibSegJu_ubaA0.regs0 LibSegJu_ubaA0.regs_out0 KS_ubaA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ubaA0_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<v21Ma+v24#140#400B#v21#3??,2_v2#38#38+v24#<#4,1,14X#37>78#37050Y,T,1#37>=0T,2_v2#70T,8v24T,9v26T,:+v24#18T,;#400T,<v21T,12v25T,13+v24#18T,15#?>00Mb+v24#<+v21#1Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ubaA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaA0] fx R M V ubaA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaA0] LibSegJu_ubaA0.regs0 LibSegJu_ubaA0.kn0 LibSegJu_ubaA0.BR LibSegJu_ubaA0.PSS LibSegJu_ubaA0.NX0 LibSegJu_ubaA0.F0 228984 LibSegJu_ubaA0.seg_sound_ax fx R M V ubaA0_conc_s. Qed.
Definition KS_ubaA1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaA1.regs0 LibSegJu_ubaA1.regs_out0).
Lemma KS_ubaA1_ok : BG.kept_ok 64 LibSegJu_ubaA1.regs0 LibSegJu_ubaA1.regs_out0 KS_ubaA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaA1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<#400Ma+v24#140#400,2_v2#38#38+v24#<#4,1,12X#37>78#370:<Y,T,1#38140T,2_v2#70T,8v24T,9v26T,:v26T,;#;T,<#400T,12v25Mb+v24#<#401Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ubaA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaA1] fx R M V ubaA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaA1] LibSegJu_ubaA1.regs0 LibSegJu_ubaA1.kn0 LibSegJu_ubaA1.BR LibSegJu_ubaA1.PSS LibSegJu_ubaA1.NX0 LibSegJu_ubaA1.F0 228984 LibSegJu_ubaA1.seg_sound_ax fx R M V ubaA1_conc_s. Qed.
Definition KS_ubaKe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaKe.regs0 LibSegJu_ubaKe.regs_out0).
Lemma KS_ubaKe_ok : BG.kept_ok 64 LibSegJu_ubaKe.regs0 LibSegJu_ubaKe.regs_out0 KS_ubaKe = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaKe_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37>=0#370:<Y,T,1#38140T,:v26T,;#1"%pstring.
Lemma ubaKe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaKe] fx R M V ubaKe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaKe] LibSegJu_ubaKe.regs0 LibSegJu_ubaKe.kn0 LibSegJu_ubaKe.BR LibSegJu_ubaKe.PSS LibSegJu_ubaKe.NX0 LibSegJu_ubaKe.F0 229072 LibSegJu_ubaKe.seg_sound_ax fx R M V ubaKe_conc_s. Qed.
Definition KS_ubaKh : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaKh.regs0 LibSegJu_ubaKh.regs_out0).
Lemma KS_ubaKh_ok : BG.kept_ok 64 LibSegJu_ubaKh.regs0 LibSegJu_ubaKh.regs_out0 KS_ubaKh = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaKh_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37>=0#37144Y,T,1#37?;0T,:+v24#18T,;#1"%pstring.
Lemma ubaKh_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaKh] fx R M V ubaKh_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaKh] LibSegJu_ubaKh.regs0 LibSegJu_ubaKh.kn0 LibSegJu_ubaKh.BR LibSegJu_ubaKh.PSS LibSegJu_ubaKh.NX0 LibSegJu_ubaKh.F0 229072 LibSegJu_ubaKh.seg_sound_ax fx R M V ubaKh_conc_s. Qed.
Definition KS_ubaKd : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaKd.regs0 LibSegJu_ubaKd.regs_out0).
Lemma KS_ubaKd_ok : BG.kept_ok 64 LibSegJu_ubaKd.regs0 LibSegJu_ubaKd.regs_out0 KS_ubaKd = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaKd_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#24S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#37>=0#37144Y,T,1#37?04T,:+v24#18T,;#1T,14#1"%pstring.
Lemma ubaKd_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaKd] fx R M V ubaKd_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaKd] LibSegJu_ubaKd.regs0 LibSegJu_ubaKd.kn0 LibSegJu_ubaKd.BR LibSegJu_ubaKd.PSS LibSegJu_ubaKd.NX0 LibSegJu_ubaKd.F0 229072 LibSegJu_ubaKd.seg_sound_ax fx R M V ubaKd_conc_s. Qed.
Definition KS_ubaKl : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaKl.regs0 LibSegJu_ubaKl.regs_out0).
Lemma KS_ubaKl_ok : BG.kept_ok 64 LibSegJu_ubaKl.regs0 LibSegJu_ubaKl.regs_out0 KS_ubaKl = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaKl_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,3X#37>=0#37?=<Y,T,;#24"%pstring.
Lemma ubaKl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaKl] fx R M V ubaKl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaKl] LibSegJu_ubaKl.regs0 LibSegJu_ubaKl.kn0 LibSegJu_ubaKl.BR LibSegJu_ubaKl.PSS LibSegJu_ubaKl.NX0 LibSegJu_ubaKl.F0 229072 LibSegJu_ubaKl.seg_sound_ax fx R M V ubaKl_conc_s. Qed.
Definition KS_ubaKu : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaKu.regs0 LibSegJu_ubaKu.regs_out0).
Lemma KS_ubaKu_ok : BG.kept_ok 64 LibSegJu_ubaKu.regs0 LibSegJu_ubaKu.regs_out0 KS_ubaKu = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaKu_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#25v27#??,,1,3X#37>=0#37?=<Y,T,;#24"%pstring.
Lemma ubaKu_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaKu] fx R M V ubaKu_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaKu] LibSegJu_ubaKu.regs0 LibSegJu_ubaKu.kn0 LibSegJu_ubaKu.BR LibSegJu_ubaKu.PSS LibSegJu_ubaKu.NX0 LibSegJu_ubaKu.F0 229072 LibSegJu_ubaKu.seg_sound_ax fx R M V ubaKu_conc_s. Qed.
Definition KS_ubaZ : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaZ.regs0 LibSegJu_ubaZ.regs_out0).
Lemma KS_ubaZ_ok : BG.kept_ok 64 LibSegJu_ubaZ.regs0 LibSegJu_ubaZ.regs_out0 KS_ubaZ = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaZ_conc_s := ",28A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>,1+v24#8#1,1,;X#38140#382>8Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=T,15v2>Nb+v24#8#"%pstring.
Lemma ubaZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaZ] fx R M V ubaZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaZ] LibSegJu_ubaZ.regs0 LibSegJu_ubaZ.kn0 LibSegJu_ubaZ.BR LibSegJu_ubaZ.PSS LibSegJu_ubaZ.NX0 LibSegJu_ubaZ.F0 229696 LibSegJu_ubaZ.seg_sound_ax fx R M V ubaZ_conc_s. Qed.
Definition KS_ubaC1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaC1.regs0 LibSegJu_ubaC1.regs_out0).
Lemma KS_ubaC1_ok : BG.kept_ok 64 LibSegJu_ubaC1.regs0 LibSegJu_ubaC1.regs_out0 KS_ubaC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaC1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37?;0#37::4Y,T,1#37?;<T,:v24T,;v26"%pstring.
Lemma ubaC1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaC1] fx R M V ubaC1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaC1] LibSegJu_ubaC1.regs0 LibSegJu_ubaC1.kn0 LibSegJu_ubaC1.BR LibSegJu_ubaC1.PSS LibSegJu_ubaC1.NX0 LibSegJu_ubaC1.F0 229296 LibSegJu_ubaC1.seg_sound_ax fx R M V ubaC1_conc_s. Qed.
Definition KS_ubaCe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCe.regs0 LibSegJu_ubaCe.regs_out0).
Lemma KS_ubaCe_ok : BG.kept_ok 64 LibSegJu_ubaCe.regs0 LibSegJu_ubaCe.regs_out0 KS_ubaCe = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCe_conc_s := ",2?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>Mav26v31B#1v31#40,,1,;X#37?;<#382>8Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>"%pstring.
Lemma ubaCe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCe] fx R M V ubaCe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCe] LibSegJu_ubaCe.regs0 LibSegJu_ubaCe.kn0 LibSegJu_ubaCe.BR LibSegJu_ubaCe.PSS LibSegJu_ubaCe.NX0 LibSegJu_ubaCe.F0 229308 LibSegJu_ubaCe.seg_sound_ax fx R M V ubaCe_conc_s. Qed.
Definition KS_ubaCx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCx.regs0 LibSegJu_ubaCx.regs_out0).
Lemma KS_ubaCx_ok : BG.kept_ok 64 LibSegJu_ubaCx.regs0 LibSegJu_ubaCx.regs_out0 KS_ubaCx = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCx_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#37?;<#370:<Y,T,1#38140T,:v26T,;#=T,13v30"%pstring.
Lemma ubaCx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCx] fx R M V ubaCx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCx] LibSegJu_ubaCx.regs0 LibSegJu_ubaCx.kn0 LibSegJu_ubaCx.BR LibSegJu_ubaCx.PSS LibSegJu_ubaCx.NX0 LibSegJu_ubaCx.F0 229308 LibSegJu_ubaCx.seg_sound_ax fx R M V ubaCx_conc_s. Qed.
Definition KS_ubaT1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT1.regs0 LibSegJu_ubaT1.regs_out0).
Lemma KS_ubaT1_ok : BG.kept_ok 64 LibSegJu_ubaT1.regs0 LibSegJu_ubaT1.regs_out0 KS_ubaT1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT1_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#37?04#374;8Y,T,1#37?14T,:+v24#18T,;_v2#61T,<#1"%pstring.
Lemma ubaT1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT1] fx R M V ubaT1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT1] LibSegJu_ubaT1.regs0 LibSegJu_ubaT1.kn0 LibSegJu_ubaT1.BR LibSegJu_ubaT1.PSS LibSegJu_ubaT1.NX0 LibSegJu_ubaT1.F0 229124 LibSegJu_ubaT1.seg_sound_ax fx R M V ubaT1_conc_s. Qed.
Definition KS_ubaT2z : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT2z.regs0 LibSegJu_ubaT2z.regs_out0).
Lemma KS_ubaT2z_ok : BG.kept_ok 64 LibSegJu_ubaT2z.regs0 LibSegJu_ubaT2z.regs_out0 KS_ubaT2z = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT2z_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37?14#370:<Y,T,1#38140T,:v26T,;#1"%pstring.
Lemma ubaT2z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT2z] fx R M V ubaT2z_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT2z] LibSegJu_ubaT2z.regs0 LibSegJu_ubaT2z.kn0 LibSegJu_ubaT2z.BR LibSegJu_ubaT2z.PSS LibSegJu_ubaT2z.NX0 LibSegJu_ubaT2z.F0 229140 LibSegJu_ubaT2z.seg_sound_ax fx R M V ubaT2z_conc_s. Qed.
Definition KS_ubaT2p : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT2p.regs0 LibSegJu_ubaT2p.regs_out0).
Lemma KS_ubaT2p_ok : BG.kept_ok 64 LibSegJu_ubaT2p.regs0 LibSegJu_ubaT2p.regs_out0 KS_ubaT2p = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT2p_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#1S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,4X#37?14#37050Y,T,1#37?20T,:+v24#18"%pstring.
Lemma ubaT2p_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT2p] fx R M V ubaT2p_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT2p] LibSegJu_ubaT2p.regs0 LibSegJu_ubaT2p.kn0 LibSegJu_ubaT2p.BR LibSegJu_ubaT2p.PSS LibSegJu_ubaT2p.NX0 LibSegJu_ubaT2p.F0 229140 LibSegJu_ubaT2p.seg_sound_ax fx R M V ubaT2p_conc_s. Qed.
Definition KS_ubaT3e : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT3e.regs0 LibSegJu_ubaT3e.regs_out0).
Lemma KS_ubaT3e_ok : BG.kept_ok 64 LibSegJu_ubaT3e.regs0 LibSegJu_ubaT3e.regs_out0 KS_ubaT3e = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT3e_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37?20#370:<Y,T,1#38140T,:v26T,;#1"%pstring.
Lemma ubaT3e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT3e] fx R M V ubaT3e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT3e] LibSegJu_ubaT3e.regs0 LibSegJu_ubaT3e.kn0 LibSegJu_ubaT3e.BR LibSegJu_ubaT3e.PSS LibSegJu_ubaT3e.NX0 LibSegJu_ubaT3e.F0 229152 LibSegJu_ubaT3e.seg_sound_ax fx R M V ubaT3e_conc_s. Qed.
Definition KS_ubaT3h : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT3h.regs0 LibSegJu_ubaT3h.regs_out0).
Lemma KS_ubaT3h_ok : BG.kept_ok 64 LibSegJu_ubaT3h.regs0 LibSegJu_ubaT3h.regs_out0 KS_ubaT3h = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT3h_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37?20#37144Y,T,1#37?48T,:+v24#18T,;#1"%pstring.
Lemma ubaT3h_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT3h] fx R M V ubaT3h_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT3h] LibSegJu_ubaT3h.regs0 LibSegJu_ubaT3h.kn0 LibSegJu_ubaT3h.BR LibSegJu_ubaT3h.PSS LibSegJu_ubaT3h.NX0 LibSegJu_ubaT3h.F0 229152 LibSegJu_ubaT3h.seg_sound_ax fx R M V ubaT3h_conc_s. Qed.
Definition KS_ubaT3l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT3l.regs0 LibSegJu_ubaT3l.regs_out0).
Lemma KS_ubaT3l_ok : BG.kept_ok 64 LibSegJu_ubaT3l.regs0 LibSegJu_ubaT3l.regs_out0 KS_ubaT3l = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT3l_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,6X#37?20#370:<Y,T,1#38140T,:v26T,;#3T,14#3"%pstring.
Lemma ubaT3l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT3l] fx R M V ubaT3l_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT3l] LibSegJu_ubaT3l.regs0 LibSegJu_ubaT3l.kn0 LibSegJu_ubaT3l.BR LibSegJu_ubaT3l.PSS LibSegJu_ubaT3l.NX0 LibSegJu_ubaT3l.F0 229152 LibSegJu_ubaT3l.seg_sound_ax fx R M V ubaT3l_conc_s. Qed.
Definition KS_ubaT3u : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT3u.regs0 LibSegJu_ubaT3u.regs_out0).
Lemma KS_ubaT3u_ok : BG.kept_ok 64 LibSegJu_ubaT3u.regs0 LibSegJu_ubaT3u.regs_out0 KS_ubaT3u = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT3u_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#24v27#??,,1,6X#37?20#370:<Y,T,1#38140T,:v26T,;#3T,14#3"%pstring.
Lemma ubaT3u_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT3u] fx R M V ubaT3u_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT3u] LibSegJu_ubaT3u.regs0 LibSegJu_ubaT3u.kn0 LibSegJu_ubaT3u.BR LibSegJu_ubaT3u.PSS LibSegJu_ubaT3u.NX0 LibSegJu_ubaT3u.F0 229152 LibSegJu_ubaT3u.seg_sound_ax fx R M V ubaT3u_conc_s. Qed.
Definition KS_ubaT4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaT4.regs0 LibSegJu_ubaT4.regs_out0).
Lemma KS_ubaT4_ok : BG.kept_ok 64 LibSegJu_ubaT4.regs0 LibSegJu_ubaT4.regs_out0 KS_ubaT4 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaT4_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37?48#37::4Y,T,1#37?54T,:v24T,;v26"%pstring.
Lemma ubaT4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaT4] fx R M V ubaT4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaT4] LibSegJu_ubaT4.regs0 LibSegJu_ubaT4.kn0 LibSegJu_ubaT4.BR LibSegJu_ubaT4.PSS LibSegJu_ubaT4.NX0 LibSegJu_ubaT4.F0 229192 LibSegJu_ubaT4.seg_sound_ax fx R M V ubaT4_conc_s. Qed.
Definition KS_ubaTe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaTe.regs0 LibSegJu_ubaTe.regs_out0).
Lemma KS_ubaTe_ok : BG.kept_ok 64 LibSegJu_ubaTe.regs0 LibSegJu_ubaTe.regs_out0 KS_ubaTe = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaTe_conc_s := ",30A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>Mav26v31B#1v31#40,,1,;X#37?54#382>8Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>"%pstring.
Lemma ubaTe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaTe] fx R M V ubaTe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaTe] LibSegJu_ubaTe.regs0 LibSegJu_ubaTe.kn0 LibSegJu_ubaTe.BR LibSegJu_ubaTe.PSS LibSegJu_ubaTe.NX0 LibSegJu_ubaTe.F0 229204 LibSegJu_ubaTe.seg_sound_ax fx R M V ubaTe_conc_s. Qed.
Definition KS_ubaTx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaTx.regs0 LibSegJu_ubaTx.regs_out0).
Lemma KS_ubaTx_ok : BG.kept_ok 64 LibSegJu_ubaTx.regs0 LibSegJu_ubaTx.regs_out0 KS_ubaTx = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaTx_conc_s := ",22A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#37?54#370:<Y,T,1#38140T,:v26T,;#=T,13v30"%pstring.
Lemma ubaTx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaTx] fx R M V ubaTx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaTx] LibSegJu_ubaTx.regs0 LibSegJu_ubaTx.kn0 LibSegJu_ubaTx.BR LibSegJu_ubaTx.PSS LibSegJu_ubaTx.NX0 LibSegJu_ubaTx.F0 229204 LibSegJu_ubaTx.seg_sound_ax fx R M V ubaTx_conc_s. Qed.
End PMBAUP1.
