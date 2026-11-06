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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uboA0 LibSegJu_uboA1 LibSegJu_uboKe LibSegJu_uboKd LibSegJu_uboKl LibSegJu_uboKu LibSegJu_uboK2e LibSegJu_uboK2h LibSegJu_uboK2l LibSegJu_uboK2u LibSegJu_uboZ LibSegJu_uboC1 LibSegJu_uboCe LibSegJu_uboCx LibSegJu_uboT1 LibSegJu_uboT2z LibSegJu_uboT2p LibSegJu_uboT3e LibSegJu_uboT3h LibSegJu_uboT3l LibSegJu_uboT3u LibSegJu_uboT4 LibSegJu_uboTe LibSegJu_uboTx.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOUP1.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uboA0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboA0.regs0 LibSegJu_uboA0.regs_out0).
Lemma KS_uboA0_ok : BG.kept_ok 64 LibSegJu_uboA0.regs0 LibSegJu_uboA0.regs_out0 KS_uboA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uboA0_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<v21Ma+v24#140#400B#v21#3??,2_v2#38#38+v24#<#4,1,14X#38324#37050Y,T,1#3837<T,2_v2#70T,8v24T,9v26T,:+v24#18T,;#400T,<v21T,12v25T,13+v24#18T,15#?>00Mb+v24#<+v21#1Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uboA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboA0] fx R M V uboA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboA0] LibSegJu_uboA0.regs0 LibSegJu_uboA0.kn0 LibSegJu_uboA0.BR LibSegJu_uboA0.PSS LibSegJu_uboA0.NX0 LibSegJu_uboA0.F0 230180 LibSegJu_uboA0.seg_sound_ax fx R M V uboA0_conc_s. Qed.
Definition KS_uboA1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboA1.regs0 LibSegJu_uboA1.regs_out0).
Lemma KS_uboA1_ok : BG.kept_ok 64 LibSegJu_uboA1.regs0 LibSegJu_uboA1.regs_out0 KS_uboA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboA1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<#400Ma+v24#140#400,2_v2#38#38+v24#<#4,1,12X#38324#370:<Y,T,1#384?4T,2_v2#70T,8v24T,9v26T,:v26T,;#;T,<#400T,12v25Mb+v24#<#401Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uboA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboA1] fx R M V uboA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboA1] LibSegJu_uboA1.regs0 LibSegJu_uboA1.kn0 LibSegJu_uboA1.BR LibSegJu_uboA1.PSS LibSegJu_uboA1.NX0 LibSegJu_uboA1.F0 230180 LibSegJu_uboA1.seg_sound_ax fx R M V uboA1_conc_s. Qed.
Definition KS_uboKe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboKe.regs0 LibSegJu_uboKe.regs_out0).
Lemma KS_uboKe_ok : BG.kept_ok 64 LibSegJu_uboKe.regs0 LibSegJu_uboKe.regs_out0 KS_uboKe = true. Proof. vm_compute. reflexivity. Qed.
Definition uboKe_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#3837<#370:<Y,T,1#384?4T,:v26T,;#1"%pstring.
Lemma uboKe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboKe] fx R M V uboKe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboKe] LibSegJu_uboKe.regs0 LibSegJu_uboKe.kn0 LibSegJu_uboKe.BR LibSegJu_uboKe.PSS LibSegJu_uboKe.NX0 LibSegJu_uboKe.F0 230268 LibSegJu_uboKe.seg_sound_ax fx R M V uboKe_conc_s. Qed.
Definition KS_uboKd : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboKd.regs0 LibSegJu_uboKd.regs_out0).
Lemma KS_uboKd_ok : BG.kept_ok 64 LibSegJu_uboKd.regs0 LibSegJu_uboKd.regs_out0 KS_uboKd = true. Proof. vm_compute. reflexivity. Qed.
Definition uboKd_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#24S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#3837<#37144Y,T,1#383:8T,:+v24#18T,;#1T,14#1"%pstring.
Lemma uboKd_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboKd] fx R M V uboKd_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboKd] LibSegJu_uboKd.regs0 LibSegJu_uboKd.kn0 LibSegJu_uboKd.BR LibSegJu_uboKd.PSS LibSegJu_uboKd.NX0 LibSegJu_uboKd.F0 230268 LibSegJu_uboKd.seg_sound_ax fx R M V uboKd_conc_s. Qed.
Definition KS_uboKl : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboKl.regs0 LibSegJu_uboKl.regs_out0).
Lemma KS_uboKl_ok : BG.kept_ok 64 LibSegJu_uboKl.regs0 LibSegJu_uboKl.regs_out0 KS_uboKl = true. Proof. vm_compute. reflexivity. Qed.
Definition uboKl_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#23,,1,5X#3837<#37050Y,T,1#38450T,:+v24#18T,;#24"%pstring.
Lemma uboKl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboKl] fx R M V uboKl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboKl] LibSegJu_uboKl.regs0 LibSegJu_uboKl.kn0 LibSegJu_uboKl.BR LibSegJu_uboKl.PSS LibSegJu_uboKl.NX0 LibSegJu_uboKl.F0 230268 LibSegJu_uboKl.seg_sound_ax fx R M V uboKl_conc_s. Qed.
Definition KS_uboKu : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboKu.regs0 LibSegJu_uboKu.regs_out0).
Lemma KS_uboKu_ok : BG.kept_ok 64 LibSegJu_uboKu.regs0 LibSegJu_uboKu.regs_out0 KS_uboKu = true. Proof. vm_compute. reflexivity. Qed.
Definition uboKu_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#25v27#??,,1,5X#3837<#37050Y,T,1#38450T,:+v24#18T,;#24"%pstring.
Lemma uboKu_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboKu] fx R M V uboKu_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboKu] LibSegJu_uboKu.regs0 LibSegJu_uboKu.kn0 LibSegJu_uboKu.BR LibSegJu_uboKu.PSS LibSegJu_uboKu.NX0 LibSegJu_uboKu.F0 230268 LibSegJu_uboKu.seg_sound_ax fx R M V uboKu_conc_s. Qed.
Definition KS_uboK2e : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboK2e.regs0 LibSegJu_uboK2e.regs_out0).
Lemma KS_uboK2e_ok : BG.kept_ok 64 LibSegJu_uboK2e.regs0 LibSegJu_uboK2e.regs_out0 KS_uboK2e = true. Proof. vm_compute. reflexivity. Qed.
Definition uboK2e_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#38450#370:<Y,T,1#384?4T,:v26T,;#1"%pstring.
Lemma uboK2e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboK2e] fx R M V uboK2e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboK2e] LibSegJu_uboK2e.regs0 LibSegJu_uboK2e.kn0 LibSegJu_uboK2e.BR LibSegJu_uboK2e.PSS LibSegJu_uboK2e.NX0 LibSegJu_uboK2e.F0 230480 LibSegJu_uboK2e.seg_sound_ax fx R M V uboK2e_conc_s. Qed.
Definition KS_uboK2h : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboK2h.regs0 LibSegJu_uboK2h.regs_out0).
Lemma KS_uboK2h_ok : BG.kept_ok 64 LibSegJu_uboK2h.regs0 LibSegJu_uboK2h.regs_out0 KS_uboK2h = true. Proof. vm_compute. reflexivity. Qed.
Definition uboK2h_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#38450#37144Y,T,1#38478T,:+v24#18T,;#1"%pstring.
Lemma uboK2h_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboK2h] fx R M V uboK2h_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboK2h] LibSegJu_uboK2h.regs0 LibSegJu_uboK2h.kn0 LibSegJu_uboK2h.BR LibSegJu_uboK2h.PSS LibSegJu_uboK2h.NX0 LibSegJu_uboK2h.F0 230480 LibSegJu_uboK2h.seg_sound_ax fx R M V uboK2h_conc_s. Qed.
Definition KS_uboK2l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboK2l.regs0 LibSegJu_uboK2l.regs_out0).
Lemma KS_uboK2l_ok : BG.kept_ok 64 LibSegJu_uboK2l.regs0 LibSegJu_uboK2l.regs_out0 KS_uboK2l = true. Proof. vm_compute. reflexivity. Qed.
Definition uboK2l_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,3X#38450#384:4Y,T,;#23"%pstring.
Lemma uboK2l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboK2l] fx R M V uboK2l_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboK2l] LibSegJu_uboK2l.regs0 LibSegJu_uboK2l.kn0 LibSegJu_uboK2l.BR LibSegJu_uboK2l.PSS LibSegJu_uboK2l.NX0 LibSegJu_uboK2l.F0 230480 LibSegJu_uboK2l.seg_sound_ax fx R M V uboK2l_conc_s. Qed.
Definition KS_uboK2u : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboK2u.regs0 LibSegJu_uboK2u.regs_out0).
Lemma KS_uboK2u_ok : BG.kept_ok 64 LibSegJu_uboK2u.regs0 LibSegJu_uboK2u.regs_out0 KS_uboK2u = true. Proof. vm_compute. reflexivity. Qed.
Definition uboK2u_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#24v27#??,,1,3X#38450#384:4Y,T,;#23"%pstring.
Lemma uboK2u_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboK2u] fx R M V uboK2u_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboK2u] LibSegJu_uboK2u.regs0 LibSegJu_uboK2u.kn0 LibSegJu_uboK2u.BR LibSegJu_uboK2u.PSS LibSegJu_uboK2u.NX0 LibSegJu_uboK2u.F0 230480 LibSegJu_uboK2u.seg_sound_ax fx R M V uboK2u_conc_s. Qed.
Definition KS_uboZ : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboZ.regs0 LibSegJu_uboZ.regs_out0).
Lemma KS_uboZ_ok : BG.kept_ok 64 LibSegJu_uboZ.regs0 LibSegJu_uboZ.regs_out0 KS_uboZ = true. Proof. vm_compute. reflexivity. Qed.
Definition uboZ_conc_s := ",28A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>,1+v24#8#1,1,;X#384?4#387;0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=T,15v2>Nb+v24#8#"%pstring.
Lemma uboZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboZ] fx R M V uboZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboZ] LibSegJu_uboZ.regs0 LibSegJu_uboZ.kn0 LibSegJu_uboZ.BR LibSegJu_uboZ.PSS LibSegJu_uboZ.NX0 LibSegJu_uboZ.F0 230644 LibSegJu_uboZ.seg_sound_ax fx R M V uboZ_conc_s. Qed.
Definition KS_uboC1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboC1.regs0 LibSegJu_uboC1.regs_out0).
Lemma KS_uboC1_ok : BG.kept_ok 64 LibSegJu_uboC1.regs0 LibSegJu_uboC1.regs_out0 KS_uboC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboC1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#38478#37::4Y,T,1#38484T,:v24T,;v26"%pstring.
Lemma uboC1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboC1] fx R M V uboC1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboC1] LibSegJu_uboC1.regs0 LibSegJu_uboC1.kn0 LibSegJu_uboC1.BR LibSegJu_uboC1.PSS LibSegJu_uboC1.NX0 LibSegJu_uboC1.F0 230520 LibSegJu_uboC1.seg_sound_ax fx R M V uboC1_conc_s. Qed.
Definition KS_uboCe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCe.regs0 LibSegJu_uboCe.regs_out0).
Lemma KS_uboCe_ok : BG.kept_ok 64 LibSegJu_uboCe.regs0 LibSegJu_uboCe.regs_out0 KS_uboCe = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCe_conc_s := ",2?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>Mav26v31B#1v31#40,,1,;X#38484#387;0Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>"%pstring.
Lemma uboCe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCe] fx R M V uboCe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCe] LibSegJu_uboCe.regs0 LibSegJu_uboCe.kn0 LibSegJu_uboCe.BR LibSegJu_uboCe.PSS LibSegJu_uboCe.NX0 LibSegJu_uboCe.F0 230532 LibSegJu_uboCe.seg_sound_ax fx R M V uboCe_conc_s. Qed.
Definition KS_uboCx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCx.regs0 LibSegJu_uboCx.regs_out0).
Lemma KS_uboCx_ok : BG.kept_ok 64 LibSegJu_uboCx.regs0 LibSegJu_uboCx.regs_out0 KS_uboCx = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCx_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#38484#370:<Y,T,1#384?4T,:v26T,;#=T,13v30"%pstring.
Lemma uboCx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCx] fx R M V uboCx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCx] LibSegJu_uboCx.regs0 LibSegJu_uboCx.kn0 LibSegJu_uboCx.BR LibSegJu_uboCx.PSS LibSegJu_uboCx.NX0 LibSegJu_uboCx.F0 230532 LibSegJu_uboCx.seg_sound_ax fx R M V uboCx_conc_s. Qed.
Definition KS_uboT1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT1.regs0 LibSegJu_uboT1.regs_out0).
Lemma KS_uboT1_ok : BG.kept_ok 64 LibSegJu_uboT1.regs0 LibSegJu_uboT1.regs_out0 KS_uboT1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT1_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#383:8#374;8Y,T,1#383;8T,:+v24#18T,;_v2#61T,<#1"%pstring.
Lemma uboT1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT1] fx R M V uboT1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT1] LibSegJu_uboT1.regs0 LibSegJu_uboT1.kn0 LibSegJu_uboT1.BR LibSegJu_uboT1.PSS LibSegJu_uboT1.NX0 LibSegJu_uboT1.F0 230312 LibSegJu_uboT1.seg_sound_ax fx R M V uboT1_conc_s. Qed.
Definition KS_uboT2z : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT2z.regs0 LibSegJu_uboT2z.regs_out0).
Lemma KS_uboT2z_ok : BG.kept_ok 64 LibSegJu_uboT2z.regs0 LibSegJu_uboT2z.regs_out0 KS_uboT2z = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT2z_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#383;8#370:<Y,T,1#384?4T,:v26T,;#1"%pstring.
Lemma uboT2z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT2z] fx R M V uboT2z_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT2z] LibSegJu_uboT2z.regs0 LibSegJu_uboT2z.kn0 LibSegJu_uboT2z.BR LibSegJu_uboT2z.PSS LibSegJu_uboT2z.NX0 LibSegJu_uboT2z.F0 230328 LibSegJu_uboT2z.seg_sound_ax fx R M V uboT2z_conc_s. Qed.
Definition KS_uboT2p : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT2p.regs0 LibSegJu_uboT2p.regs_out0).
Lemma KS_uboT2p_ok : BG.kept_ok 64 LibSegJu_uboT2p.regs0 LibSegJu_uboT2p.regs_out0 KS_uboT2p = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT2p_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#1S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,4X#383;8#37050Y,T,1#383<4T,:+v24#18"%pstring.
Lemma uboT2p_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT2p] fx R M V uboT2p_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT2p] LibSegJu_uboT2p.regs0 LibSegJu_uboT2p.kn0 LibSegJu_uboT2p.BR LibSegJu_uboT2p.PSS LibSegJu_uboT2p.NX0 LibSegJu_uboT2p.F0 230328 LibSegJu_uboT2p.seg_sound_ax fx R M V uboT2p_conc_s. Qed.
Definition KS_uboT3e : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT3e.regs0 LibSegJu_uboT3e.regs_out0).
Lemma KS_uboT3e_ok : BG.kept_ok 64 LibSegJu_uboT3e.regs0 LibSegJu_uboT3e.regs_out0 KS_uboT3e = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT3e_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#383<4#370:<Y,T,1#384?4T,:v26T,;#1"%pstring.
Lemma uboT3e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT3e] fx R M V uboT3e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT3e] LibSegJu_uboT3e.regs0 LibSegJu_uboT3e.kn0 LibSegJu_uboT3e.BR LibSegJu_uboT3e.PSS LibSegJu_uboT3e.NX0 LibSegJu_uboT3e.F0 230340 LibSegJu_uboT3e.seg_sound_ax fx R M V uboT3e_conc_s. Qed.
Definition KS_uboT3h : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT3h.regs0 LibSegJu_uboT3h.regs_out0).
Lemma KS_uboT3h_ok : BG.kept_ok 64 LibSegJu_uboT3h.regs0 LibSegJu_uboT3h.regs_out0 KS_uboT3h = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT3h_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#383<4#37144Y,T,1#383><T,:+v24#18T,;#1"%pstring.
Lemma uboT3h_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT3h] fx R M V uboT3h_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT3h] LibSegJu_uboT3h.regs0 LibSegJu_uboT3h.kn0 LibSegJu_uboT3h.BR LibSegJu_uboT3h.PSS LibSegJu_uboT3h.NX0 LibSegJu_uboT3h.F0 230340 LibSegJu_uboT3h.seg_sound_ax fx R M V uboT3h_conc_s. Qed.
Definition KS_uboT3l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT3l.regs0 LibSegJu_uboT3l.regs_out0).
Lemma KS_uboT3l_ok : BG.kept_ok 64 LibSegJu_uboT3l.regs0 LibSegJu_uboT3l.regs_out0 KS_uboT3l = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT3l_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,6X#383<4#370:<Y,T,1#384?4T,:v26T,;#3T,14#3"%pstring.
Lemma uboT3l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT3l] fx R M V uboT3l_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT3l] LibSegJu_uboT3l.regs0 LibSegJu_uboT3l.kn0 LibSegJu_uboT3l.BR LibSegJu_uboT3l.PSS LibSegJu_uboT3l.NX0 LibSegJu_uboT3l.F0 230340 LibSegJu_uboT3l.seg_sound_ax fx R M V uboT3l_conc_s. Qed.
Definition KS_uboT3u : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT3u.regs0 LibSegJu_uboT3u.regs_out0).
Lemma KS_uboT3u_ok : BG.kept_ok 64 LibSegJu_uboT3u.regs0 LibSegJu_uboT3u.regs_out0 KS_uboT3u = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT3u_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#24v27#??,,1,6X#383<4#370:<Y,T,1#384?4T,:v26T,;#3T,14#3"%pstring.
Lemma uboT3u_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT3u] fx R M V uboT3u_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT3u] LibSegJu_uboT3u.regs0 LibSegJu_uboT3u.kn0 LibSegJu_uboT3u.BR LibSegJu_uboT3u.PSS LibSegJu_uboT3u.NX0 LibSegJu_uboT3u.F0 230340 LibSegJu_uboT3u.seg_sound_ax fx R M V uboT3u_conc_s. Qed.
Definition KS_uboT4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboT4.regs0 LibSegJu_uboT4.regs_out0).
Lemma KS_uboT4_ok : BG.kept_ok 64 LibSegJu_uboT4.regs0 LibSegJu_uboT4.regs_out0 KS_uboT4 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboT4_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#383><#37::4Y,T,1#383?8T,:v24T,;v26"%pstring.
Lemma uboT4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboT4] fx R M V uboT4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboT4] LibSegJu_uboT4.regs0 LibSegJu_uboT4.kn0 LibSegJu_uboT4.BR LibSegJu_uboT4.PSS LibSegJu_uboT4.NX0 LibSegJu_uboT4.F0 230380 LibSegJu_uboT4.seg_sound_ax fx R M V uboT4_conc_s. Qed.
Definition KS_uboTe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTe.regs0 LibSegJu_uboTe.regs_out0).
Lemma KS_uboTe_ok : BG.kept_ok 64 LibSegJu_uboTe.regs0 LibSegJu_uboTe.regs_out0 KS_uboTe = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTe_conc_s := ",30A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>Mav26v31B#1v31#40,,1,;X#383?8#387;0Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>"%pstring.
Lemma uboTe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTe] fx R M V uboTe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTe] LibSegJu_uboTe.regs0 LibSegJu_uboTe.kn0 LibSegJu_uboTe.BR LibSegJu_uboTe.PSS LibSegJu_uboTe.NX0 LibSegJu_uboTe.F0 230392 LibSegJu_uboTe.seg_sound_ax fx R M V uboTe_conc_s. Qed.
Definition KS_uboTx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboTx.regs0 LibSegJu_uboTx.regs_out0).
Lemma KS_uboTx_ok : BG.kept_ok 64 LibSegJu_uboTx.regs0 LibSegJu_uboTx.regs_out0 KS_uboTx = true. Proof. vm_compute. reflexivity. Qed.
Definition uboTx_conc_s := ",22A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#383?8#370:<Y,T,1#384?4T,:v26T,;#=T,13v30"%pstring.
Lemma uboTx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboTx] fx R M V uboTx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboTx] LibSegJu_uboTx.regs0 LibSegJu_uboTx.kn0 LibSegJu_uboTx.BR LibSegJu_uboTx.PSS LibSegJu_uboTx.NX0 LibSegJu_uboTx.F0 230392 LibSegJu_uboTx.seg_sound_ax fx R M V uboTx_conc_s. Qed.
End PMBOUP1.
