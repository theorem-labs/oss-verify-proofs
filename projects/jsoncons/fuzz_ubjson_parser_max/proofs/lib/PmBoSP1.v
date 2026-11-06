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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_boA0 LibSegJs_boA1 LibSegJs_boKe LibSegJs_boKd LibSegJs_boKl LibSegJs_boKu LibSegJs_boK2e LibSegJs_boK2h LibSegJs_boK2l LibSegJs_boK2u LibSegJs_boZ LibSegJs_boC1 LibSegJs_boCe LibSegJs_boCx LibSegJs_boT1 LibSegJs_boT2z LibSegJs_boT2p LibSegJs_boT3e LibSegJs_boT3h LibSegJs_boT3l LibSegJs_boT3u LibSegJs_boT4 LibSegJs_boTe LibSegJs_boTx.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOP1.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_boA0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boA0.regs0 LibSegJs_boA0.regs_out0).
Lemma KS_boA0_ok : BG.kept_ok 64 LibSegJs_boA0.regs0 LibSegJs_boA0.regs_out0 KS_boA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition boA0_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<v21Ma+v24#140#400B#v21#3??,2_v2#40#40+v24#<#4,1,14X#374:0#3643<Y,T,1#374?0T,2_v2#70T,8v24T,9v26T,:+v24#18T,;#400T,<+v21#1T,12v25T,13+v24#18Mb+v24#<+v21#1Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma boA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boA0] fx R M V boA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boA0] LibSegJs_boA0.regs0 LibSegJs_boA0.kn0 LibSegJs_boA0.BR LibSegJs_boA0.PSS LibSegJs_boA0.NX0 LibSegJs_boA0.F0 226464 LibSegJs_boA0.seg_sound_ax fx R M V boA0_conc_s. Qed.
Definition KS_boA1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boA1.regs0 LibSegJs_boA1.regs_out0).
Lemma KS_boA1_ok : BG.kept_ok 64 LibSegJs_boA1.regs0 LibSegJs_boA1.regs_out0 KS_boA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition boA1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<#400Ma+v24#140#400,2_v2#40#40+v24#<#4,1,13X#374:0#36490Y,T,1#37620T,2_v2#70T,8v24T,9v26T,:v26T,;#;T,<#401T,12v25Mb+v24#<#401Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma boA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boA1] fx R M V boA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boA1] LibSegJs_boA1.regs0 LibSegJs_boA1.kn0 LibSegJs_boA1.BR LibSegJs_boA1.PSS LibSegJs_boA1.NX0 LibSegJs_boA1.F0 226464 LibSegJs_boA1.seg_sound_ax fx R M V boA1_conc_s. Qed.
Definition KS_boKe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boKe.regs0 LibSegJs_boKe.regs_out0).
Lemma KS_boKe_ok : BG.kept_ok 64 LibSegJs_boKe.regs0 LibSegJs_boKe.regs_out0 KS_boKe = true. Proof. vm_compute. reflexivity. Qed.
Definition boKe_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#374?0#36490Y,T,1#37620T,:v26T,;#1"%pstring.
Lemma boKe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boKe] fx R M V boKe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boKe] LibSegJs_boKe.regs0 LibSegJs_boKe.kn0 LibSegJs_boKe.BR LibSegJs_boKe.PSS LibSegJs_boKe.NX0 LibSegJs_boKe.F0 226544 LibSegJs_boKe.seg_sound_ax fx R M V boKe_conc_s. Qed.
Definition KS_boKd : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boKd.regs0 LibSegJs_boKd.regs_out0).
Lemma KS_boKd_ok : BG.kept_ok 64 LibSegJs_boKd.regs0 LibSegJs_boKd.regs_out0 KS_boKd = true. Proof. vm_compute. reflexivity. Qed.
Definition boKd_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#24S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#374?0#36528Y,T,1#37514T,:+v24#18T,;#1T,14#1"%pstring.
Lemma boKd_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boKd] fx R M V boKd_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boKd] LibSegJs_boKd.regs0 LibSegJs_boKd.kn0 LibSegJs_boKd.BR LibSegJs_boKd.PSS LibSegJs_boKd.NX0 LibSegJs_boKd.F0 226544 LibSegJs_boKd.seg_sound_ax fx R M V boKd_conc_s. Qed.
Definition KS_boKl : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boKl.regs0 LibSegJs_boKl.regs_out0).
Lemma KS_boKl_ok : BG.kept_ok 64 LibSegJs_boKl.regs0 LibSegJs_boKl.regs_out0 KS_boKl = true. Proof. vm_compute. reflexivity. Qed.
Definition boKl_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#23,,1,5X#374?0#3643<Y,T,1#3759<T,:+v24#18T,;#24"%pstring.
Lemma boKl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boKl] fx R M V boKl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boKl] LibSegJs_boKl.regs0 LibSegJs_boKl.kn0 LibSegJs_boKl.BR LibSegJs_boKl.PSS LibSegJs_boKl.NX0 LibSegJs_boKl.F0 226544 LibSegJs_boKl.seg_sound_ax fx R M V boKl_conc_s. Qed.
Definition KS_boKu : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boKu.regs0 LibSegJs_boKu.regs_out0).
Lemma KS_boKu_ok : BG.kept_ok 64 LibSegJs_boKu.regs0 LibSegJs_boKu.regs_out0 KS_boKu = true. Proof. vm_compute. reflexivity. Qed.
Definition boKu_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#25v27#??,,1,5X#374?0#3643<Y,T,1#3759<T,:+v24#18T,;#24"%pstring.
Lemma boKu_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boKu] fx R M V boKu_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boKu] LibSegJs_boKu.regs0 LibSegJs_boKu.kn0 LibSegJs_boKu.BR LibSegJs_boKu.PSS LibSegJs_boKu.NX0 LibSegJs_boKu.F0 226544 LibSegJs_boKu.seg_sound_ax fx R M V boKu_conc_s. Qed.
Definition KS_boK2e : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boK2e.regs0 LibSegJs_boK2e.regs_out0).
Lemma KS_boK2e_ok : BG.kept_ok 64 LibSegJs_boK2e.regs0 LibSegJs_boK2e.regs_out0 KS_boK2e = true. Proof. vm_compute. reflexivity. Qed.
Definition boK2e_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#3759<#36490Y,T,1#37620T,:v26T,;#1"%pstring.
Lemma boK2e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boK2e] fx R M V boK2e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boK2e] LibSegJs_boK2e.regs0 LibSegJs_boK2e.kn0 LibSegJs_boK2e.BR LibSegJs_boK2e.PSS LibSegJs_boK2e.NX0 LibSegJs_boK2e.F0 226716 LibSegJs_boK2e.seg_sound_ax fx R M V boK2e_conc_s. Qed.
Definition KS_boK2h : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boK2h.regs0 LibSegJs_boK2h.regs_out0).
Lemma KS_boK2h_ok : BG.kept_ok 64 LibSegJs_boK2h.regs0 LibSegJs_boK2h.regs_out0 KS_boK2h = true. Proof. vm_compute. reflexivity. Qed.
Definition boK2h_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#3759<#36528Y,T,1#375;<T,:+v24#18T,;#1"%pstring.
Lemma boK2h_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boK2h] fx R M V boK2h_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boK2h] LibSegJs_boK2h.regs0 LibSegJs_boK2h.kn0 LibSegJs_boK2h.BR LibSegJs_boK2h.PSS LibSegJs_boK2h.NX0 LibSegJs_boK2h.F0 226716 LibSegJs_boK2h.seg_sound_ax fx R M V boK2h_conc_s. Qed.
Definition KS_boK2l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boK2l.regs0 LibSegJs_boK2l.regs_out0).
Lemma KS_boK2l_ok : BG.kept_ok 64 LibSegJs_boK2l.regs0 LibSegJs_boK2l.regs_out0 KS_boK2l = true. Proof. vm_compute. reflexivity. Qed.
Definition boK2l_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,3X#3759<#375>8Y,T,;#23"%pstring.
Lemma boK2l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boK2l] fx R M V boK2l_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boK2l] LibSegJs_boK2l.regs0 LibSegJs_boK2l.kn0 LibSegJs_boK2l.BR LibSegJs_boK2l.PSS LibSegJs_boK2l.NX0 LibSegJs_boK2l.F0 226716 LibSegJs_boK2l.seg_sound_ax fx R M V boK2l_conc_s. Qed.
Definition KS_boK2u : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boK2u.regs0 LibSegJs_boK2u.regs_out0).
Lemma KS_boK2u_ok : BG.kept_ok 64 LibSegJs_boK2u.regs0 LibSegJs_boK2u.regs_out0 KS_boK2u = true. Proof. vm_compute. reflexivity. Qed.
Definition boK2u_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#24v27#??,,1,3X#3759<#375>8Y,T,;#23"%pstring.
Lemma boK2u_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boK2u] fx R M V boK2u_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boK2u] LibSegJs_boK2u.regs0 LibSegJs_boK2u.kn0 LibSegJs_boK2u.BR LibSegJs_boK2u.PSS LibSegJs_boK2u.NX0 LibSegJs_boK2u.F0 226716 LibSegJs_boK2u.seg_sound_ax fx R M V boK2u_conc_s. Qed.
Definition KS_boZ : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boZ.regs0 LibSegJs_boZ.regs_out0).
Lemma KS_boZ_ok : BG.kept_ok 64 LibSegJs_boZ.regs0 LibSegJs_boZ.regs_out0 KS_boZ = true. Proof. vm_compute. reflexivity. Qed.
Definition boZ_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?,1+v24#8#1,1,<X#37620#378:<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?Nb+v24#8#"%pstring.
Lemma boZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boZ] fx R M V boZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boZ] LibSegJs_boZ.regs0 LibSegJs_boZ.kn0 LibSegJs_boZ.BR LibSegJs_boZ.PSS LibSegJs_boZ.NX0 LibSegJs_boZ.F0 226848 LibSegJs_boZ.seg_sound_ax fx R M V boZ_conc_s. Qed.
Definition KS_boC1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boC1.regs0 LibSegJs_boC1.regs_out0).
Lemma KS_boC1_ok : BG.kept_ok 64 LibSegJs_boC1.regs0 LibSegJs_boC1.regs_out0 KS_boC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition boC1_conc_s := ",1;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#375;<#36<?8Y,T,1#375<8T,:v24T,;v26"%pstring.
Lemma boC1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boC1] fx R M V boC1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boC1] LibSegJs_boC1.regs0 LibSegJs_boC1.kn0 LibSegJs_boC1.BR LibSegJs_boC1.PSS LibSegJs_boC1.NX0 LibSegJs_boC1.F0 226748 LibSegJs_boC1.seg_sound_ax fx R M V boC1_conc_s. Qed.
Definition KS_boCe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boCe.regs0 LibSegJs_boCe.regs_out0).
Lemma KS_boCe_ok : BG.kept_ok 64 LibSegJs_boCe.regs0 LibSegJs_boCe.regs_out0 KS_boCe = true. Proof. vm_compute. reflexivity. Qed.
Definition boCe_conc_s := ",30A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?Mav26v31B#1v31#40,,1,<X#375<8#378:<Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?"%pstring.
Lemma boCe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boCe] fx R M V boCe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boCe] LibSegJs_boCe.regs0 LibSegJs_boCe.kn0 LibSegJs_boCe.BR LibSegJs_boCe.PSS LibSegJs_boCe.NX0 LibSegJs_boCe.F0 226760 LibSegJs_boCe.seg_sound_ax fx R M V boCe_conc_s. Qed.
Definition KS_boCx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boCx.regs0 LibSegJs_boCx.regs_out0).
Lemma KS_boCx_ok : BG.kept_ok 64 LibSegJs_boCx.regs0 LibSegJs_boCx.regs_out0 KS_boCx = true. Proof. vm_compute. reflexivity. Qed.
Definition boCx_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#375<8#36490Y,T,1#37620T,:v26T,;#=T,13v30"%pstring.
Lemma boCx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boCx] fx R M V boCx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boCx] LibSegJs_boCx.regs0 LibSegJs_boCx.kn0 LibSegJs_boCx.BR LibSegJs_boCx.PSS LibSegJs_boCx.NX0 LibSegJs_boCx.F0 226760 LibSegJs_boCx.seg_sound_ax fx R M V boCx_conc_s. Qed.
Definition KS_boT1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT1.regs0 LibSegJs_boT1.regs_out0).
Lemma KS_boT1_ok : BG.kept_ok 64 LibSegJs_boT1.regs0 LibSegJs_boT1.regs_out0 KS_boT1 = true. Proof. vm_compute. reflexivity. Qed.
Definition boT1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#37514#36830Y,T,1#37524T,:+v24#18T,;_v2#69T,<#1"%pstring.
Lemma boT1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT1] fx R M V boT1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT1] LibSegJs_boT1.regs0 LibSegJs_boT1.kn0 LibSegJs_boT1.BR LibSegJs_boT1.PSS LibSegJs_boT1.NX0 LibSegJs_boT1.F0 226580 LibSegJs_boT1.seg_sound_ax fx R M V boT1_conc_s. Qed.
Definition KS_boT2z : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT2z.regs0 LibSegJs_boT2z.regs_out0).
Lemma KS_boT2z_ok : BG.kept_ok 64 LibSegJs_boT2z.regs0 LibSegJs_boT2z.regs_out0 KS_boT2z = true. Proof. vm_compute. reflexivity. Qed.
Definition boT2z_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37524#36490Y,T,1#37620T,:v26T,;#1"%pstring.
Lemma boT2z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT2z] fx R M V boT2z_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT2z] LibSegJs_boT2z.regs0 LibSegJs_boT2z.kn0 LibSegJs_boT2z.BR LibSegJs_boT2z.PSS LibSegJs_boT2z.NX0 LibSegJs_boT2z.F0 226596 LibSegJs_boT2z.seg_sound_ax fx R M V boT2z_conc_s. Qed.
Definition KS_boT2p : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT2p.regs0 LibSegJs_boT2p.regs_out0).
Lemma KS_boT2p_ok : BG.kept_ok 64 LibSegJs_boT2p.regs0 LibSegJs_boT2p.regs_out0 KS_boT2p = true. Proof. vm_compute. reflexivity. Qed.
Definition boT2p_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#1S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,4X#37524#3643<Y,T,1#37530T,:+v24#18"%pstring.
Lemma boT2p_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT2p] fx R M V boT2p_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT2p] LibSegJs_boT2p.regs0 LibSegJs_boT2p.kn0 LibSegJs_boT2p.BR LibSegJs_boT2p.PSS LibSegJs_boT2p.NX0 LibSegJs_boT2p.F0 226596 LibSegJs_boT2p.seg_sound_ax fx R M V boT2p_conc_s. Qed.
Definition KS_boT3e : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT3e.regs0 LibSegJs_boT3e.regs_out0).
Lemma KS_boT3e_ok : BG.kept_ok 64 LibSegJs_boT3e.regs0 LibSegJs_boT3e.regs_out0 KS_boT3e = true. Proof. vm_compute. reflexivity. Qed.
Definition boT3e_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37530#36490Y,T,1#37620T,:v26T,;#1"%pstring.
Lemma boT3e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT3e] fx R M V boT3e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT3e] LibSegJs_boT3e.regs0 LibSegJs_boT3e.kn0 LibSegJs_boT3e.BR LibSegJs_boT3e.PSS LibSegJs_boT3e.NX0 LibSegJs_boT3e.F0 226608 LibSegJs_boT3e.seg_sound_ax fx R M V boT3e_conc_s. Qed.
Definition KS_boT3h : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT3h.regs0 LibSegJs_boT3h.regs_out0).
Lemma KS_boT3h_ok : BG.kept_ok 64 LibSegJs_boT3h.regs0 LibSegJs_boT3h.regs_out0 KS_boT3h = true. Proof. vm_compute. reflexivity. Qed.
Definition boT3h_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37530#36528Y,T,1#37550T,:+v24#18T,;#1"%pstring.
Lemma boT3h_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT3h] fx R M V boT3h_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT3h] LibSegJs_boT3h.regs0 LibSegJs_boT3h.kn0 LibSegJs_boT3h.BR LibSegJs_boT3h.PSS LibSegJs_boT3h.NX0 LibSegJs_boT3h.F0 226608 LibSegJs_boT3h.seg_sound_ax fx R M V boT3h_conc_s. Qed.
Definition KS_boT3l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT3l.regs0 LibSegJs_boT3l.regs_out0).
Lemma KS_boT3l_ok : BG.kept_ok 64 LibSegJs_boT3l.regs0 LibSegJs_boT3l.regs_out0 KS_boT3l = true. Proof. vm_compute. reflexivity. Qed.
Definition boT3l_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,6X#37530#36490Y,T,1#37620T,:v26T,;#3T,14#3"%pstring.
Lemma boT3l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT3l] fx R M V boT3l_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT3l] LibSegJs_boT3l.regs0 LibSegJs_boT3l.kn0 LibSegJs_boT3l.BR LibSegJs_boT3l.PSS LibSegJs_boT3l.NX0 LibSegJs_boT3l.F0 226608 LibSegJs_boT3l.seg_sound_ax fx R M V boT3l_conc_s. Qed.
Definition KS_boT3u : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT3u.regs0 LibSegJs_boT3u.regs_out0).
Lemma KS_boT3u_ok : BG.kept_ok 64 LibSegJs_boT3u.regs0 LibSegJs_boT3u.regs_out0 KS_boT3u = true. Proof. vm_compute. reflexivity. Qed.
Definition boT3u_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#24v27#??,,1,6X#37530#36490Y,T,1#37620T,:v26T,;#3T,14#3"%pstring.
Lemma boT3u_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT3u] fx R M V boT3u_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT3u] LibSegJs_boT3u.regs0 LibSegJs_boT3u.kn0 LibSegJs_boT3u.BR LibSegJs_boT3u.PSS LibSegJs_boT3u.NX0 LibSegJs_boT3u.F0 226608 LibSegJs_boT3u.seg_sound_ax fx R M V boT3u_conc_s. Qed.
Definition KS_boT4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boT4.regs0 LibSegJs_boT4.regs_out0).
Lemma KS_boT4_ok : BG.kept_ok 64 LibSegJs_boT4.regs0 LibSegJs_boT4.regs_out0 KS_boT4 = true. Proof. vm_compute. reflexivity. Qed.
Definition boT4_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37550#36<?8Y,T,1#3755<T,:v24T,;v26"%pstring.
Lemma boT4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boT4] fx R M V boT4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boT4] LibSegJs_boT4.regs0 LibSegJs_boT4.kn0 LibSegJs_boT4.BR LibSegJs_boT4.PSS LibSegJs_boT4.NX0 LibSegJs_boT4.F0 226640 LibSegJs_boT4.seg_sound_ax fx R M V boT4_conc_s. Qed.
Definition KS_boTe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boTe.regs0 LibSegJs_boTe.regs_out0).
Lemma KS_boTe_ok : BG.kept_ok 64 LibSegJs_boTe.regs0 LibSegJs_boTe.regs_out0 KS_boTe = true. Proof. vm_compute. reflexivity. Qed.
Definition boTe_conc_s := ",31A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?Mav26v31B#1v31#40,,1,<X#3755<#378:<Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?"%pstring.
Lemma boTe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boTe] fx R M V boTe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boTe] LibSegJs_boTe.regs0 LibSegJs_boTe.kn0 LibSegJs_boTe.BR LibSegJs_boTe.PSS LibSegJs_boTe.NX0 LibSegJs_boTe.F0 226652 LibSegJs_boTe.seg_sound_ax fx R M V boTe_conc_s. Qed.
Definition KS_boTx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_boTx.regs0 LibSegJs_boTx.regs_out0).
Lemma KS_boTx_ok : BG.kept_ok 64 LibSegJs_boTx.regs0 LibSegJs_boTx.regs_out0 KS_boTx = true. Proof. vm_compute. reflexivity. Qed.
Definition boTx_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#3755<#36490Y,T,1#37620T,:v26T,;#=T,13v30"%pstring.
Lemma boTx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_boTx] fx R M V boTx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_boTx] LibSegJs_boTx.regs0 LibSegJs_boTx.kn0 LibSegJs_boTx.BR LibSegJs_boTx.PSS LibSegJs_boTx.NX0 LibSegJs_boTx.F0 226652 LibSegJs_boTx.seg_sound_ax fx R M V boTx_conc_s. Qed.
End PMBOP1.
