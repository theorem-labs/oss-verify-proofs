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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_baA0 LibSegJs_baA1 LibSegJs_baKe LibSegJs_baKh LibSegJs_baKd LibSegJs_baKl LibSegJs_baKu LibSegJs_baZ LibSegJs_baC1 LibSegJs_baCe LibSegJs_baCx LibSegJs_baT1 LibSegJs_baT2z LibSegJs_baT2p LibSegJs_baT3e LibSegJs_baT3h LibSegJs_baT3l LibSegJs_baT3u LibSegJs_baT4 LibSegJs_baTe LibSegJs_baTx.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAP1.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_baA0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baA0.regs0 LibSegJs_baA0.regs_out0).
Lemma KS_baA0_ok : BG.kept_ok 64 LibSegJs_baA0.regs0 LibSegJs_baA0.regs_out0 KS_baA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition baA0_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<v21Ma+v24#140#400B#v21#3??,2_v2#40#40+v24#<#4,1,14X#37090#3643<Y,T,1#370>0T,2_v2#70T,8v24T,9v26T,:+v24#18T,;#400T,<+v21#1T,12v25T,13+v24#18Mb+v24#<+v21#1Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma baA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baA0] fx R M V baA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baA0] LibSegJs_baA0.regs0 LibSegJs_baA0.kn0 LibSegJs_baA0.BR LibSegJs_baA0.PSS LibSegJs_baA0.NX0 LibSegJs_baA0.F0 225424 LibSegJs_baA0.seg_sound_ax fx R M V baA0_conc_s. Qed.
Definition KS_baA1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baA1.regs0 LibSegJs_baA1.regs_out0).
Lemma KS_baA1_ok : BG.kept_ok 64 LibSegJs_baA1.regs0 LibSegJs_baA1.regs_out0 KS_baA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baA1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Ma+v24#<#400Ma+v24#140#400,2_v2#40#40+v24#<#4,1,13X#37090#36490Y,T,1#372?<T,2_v2#70T,8v24T,9v26T,:v26T,;#;T,<#401T,12v25Mb+v24#<#401Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma baA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baA1] fx R M V baA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baA1] LibSegJs_baA1.regs0 LibSegJs_baA1.kn0 LibSegJs_baA1.BR LibSegJs_baA1.PSS LibSegJs_baA1.NX0 LibSegJs_baA1.F0 225424 LibSegJs_baA1.seg_sound_ax fx R M V baA1_conc_s. Qed.
Definition KS_baKe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baKe.regs0 LibSegJs_baKe.regs_out0).
Lemma KS_baKe_ok : BG.kept_ok 64 LibSegJs_baKe.regs0 LibSegJs_baKe.regs_out0 KS_baKe = true. Proof. vm_compute. reflexivity. Qed.
Definition baKe_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#370>0#36490Y,T,1#372?<T,:v26T,;#1"%pstring.
Lemma baKe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baKe] fx R M V baKe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baKe] LibSegJs_baKe.regs0 LibSegJs_baKe.kn0 LibSegJs_baKe.BR LibSegJs_baKe.PSS LibSegJs_baKe.NX0 LibSegJs_baKe.F0 225504 LibSegJs_baKe.seg_sound_ax fx R M V baKe_conc_s. Qed.
Definition KS_baKh : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baKh.regs0 LibSegJs_baKh.regs_out0).
Lemma KS_baKh_ok : BG.kept_ok 64 LibSegJs_baKh.regs0 LibSegJs_baKh.regs_out0 KS_baKh = true. Proof. vm_compute. reflexivity. Qed.
Definition baKh_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#370>0#36528Y,T,1#37198T,:+v24#18T,;#1"%pstring.
Lemma baKh_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baKh] fx R M V baKh_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baKh] LibSegJs_baKh.regs0 LibSegJs_baKh.kn0 LibSegJs_baKh.BR LibSegJs_baKh.PSS LibSegJs_baKh.NX0 LibSegJs_baKh.F0 225504 LibSegJs_baKh.seg_sound_ax fx R M V baKh_conc_s. Qed.
Definition KS_baKd : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baKd.regs0 LibSegJs_baKd.regs_out0).
Lemma KS_baKd_ok : BG.kept_ok 64 LibSegJs_baKd.regs0 LibSegJs_baKd.regs_out0 KS_baKd = true. Proof. vm_compute. reflexivity. Qed.
Definition baKd_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#24S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#370>0#36528Y,T,1#3710<T,:+v24#18T,;#1T,14#1"%pstring.
Lemma baKd_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baKd] fx R M V baKd_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baKd] LibSegJs_baKd.regs0 LibSegJs_baKd.kn0 LibSegJs_baKd.BR LibSegJs_baKd.PSS LibSegJs_baKd.NX0 LibSegJs_baKd.F0 225504 LibSegJs_baKd.seg_sound_ax fx R M V baKd_conc_s. Qed.
Definition KS_baKl : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baKl.regs0 LibSegJs_baKl.regs_out0).
Lemma KS_baKl_ok : BG.kept_ok 64 LibSegJs_baKl.regs0 LibSegJs_baKl.regs_out0 KS_baKl = true. Proof. vm_compute. reflexivity. Qed.
Definition baKl_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,3X#370>0#371<4Y,T,;#24"%pstring.
Lemma baKl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baKl] fx R M V baKl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baKl] LibSegJs_baKl.regs0 LibSegJs_baKl.kn0 LibSegJs_baKl.BR LibSegJs_baKl.PSS LibSegJs_baKl.NX0 LibSegJs_baKl.F0 225504 LibSegJs_baKl.seg_sound_ax fx R M V baKl_conc_s. Qed.
Definition KS_baKu : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baKu.regs0 LibSegJs_baKu.regs_out0).
Lemma KS_baKu_ok : BG.kept_ok 64 LibSegJs_baKu.regs0 LibSegJs_baKu.regs_out0 KS_baKu = true. Proof. vm_compute. reflexivity. Qed.
Definition baKu_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#25v27#??,,1,3X#370>0#371<4Y,T,;#24"%pstring.
Lemma baKu_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baKu] fx R M V baKu_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baKu] LibSegJs_baKu.regs0 LibSegJs_baKu.kn0 LibSegJs_baKu.BR LibSegJs_baKu.PSS LibSegJs_baKu.NX0 LibSegJs_baKu.F0 225504 LibSegJs_baKu.seg_sound_ax fx R M V baKu_conc_s. Qed.
Definition KS_baZ : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baZ.regs0 LibSegJs_baZ.regs_out0).
Lemma KS_baZ_ok : BG.kept_ok 64 LibSegJs_baZ.regs0 LibSegJs_baZ.regs_out0 KS_baZ = true. Proof. vm_compute. reflexivity. Qed.
Definition baZ_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#70S,8v24S,9v26S,12v25B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?,1+v24#8#1,1,<X#372?<#37488Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?Nb+v24#8#"%pstring.
Lemma baZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baZ] fx R M V baZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baZ] LibSegJs_baZ.regs0 LibSegJs_baZ.kn0 LibSegJs_baZ.BR LibSegJs_baZ.PSS LibSegJs_baZ.NX0 LibSegJs_baZ.F0 226044 LibSegJs_baZ.seg_sound_ax fx R M V baZ_conc_s. Qed.
Definition KS_baC1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baC1.regs0 LibSegJs_baC1.regs_out0).
Lemma KS_baC1_ok : BG.kept_ok 64 LibSegJs_baC1.regs0 LibSegJs_baC1.regs_out0 KS_baC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baC1_conc_s := ",1;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37198#36<?8Y,T,1#371:4T,:v24T,;v26"%pstring.
Lemma baC1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baC1] fx R M V baC1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baC1] LibSegJs_baC1.regs0 LibSegJs_baC1.kn0 LibSegJs_baC1.BR LibSegJs_baC1.PSS LibSegJs_baC1.NX0 LibSegJs_baC1.F0 225688 LibSegJs_baC1.seg_sound_ax fx R M V baC1_conc_s. Qed.
Definition KS_baCe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCe.regs0 LibSegJs_baCe.regs_out0).
Lemma KS_baCe_ok : BG.kept_ok 64 LibSegJs_baCe.regs0 LibSegJs_baCe.regs_out0 KS_baCe = true. Proof. vm_compute. reflexivity. Qed.
Definition baCe_conc_s := ",30A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?Mav26v31B#1v31#40,,1,<X#371:4#37488Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?"%pstring.
Lemma baCe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCe] fx R M V baCe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCe] LibSegJs_baCe.regs0 LibSegJs_baCe.kn0 LibSegJs_baCe.BR LibSegJs_baCe.PSS LibSegJs_baCe.NX0 LibSegJs_baCe.F0 225700 LibSegJs_baCe.seg_sound_ax fx R M V baCe_conc_s. Qed.
Definition KS_baCx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCx.regs0 LibSegJs_baCx.regs_out0).
Lemma KS_baCx_ok : BG.kept_ok 64 LibSegJs_baCx.regs0 LibSegJs_baCx.regs_out0 KS_baCx = true. Proof. vm_compute. reflexivity. Qed.
Definition baCx_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#371:4#36490Y,T,1#372?<T,:v26T,;#=T,13v30"%pstring.
Lemma baCx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCx] fx R M V baCx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCx] LibSegJs_baCx.regs0 LibSegJs_baCx.kn0 LibSegJs_baCx.BR LibSegJs_baCx.PSS LibSegJs_baCx.NX0 LibSegJs_baCx.F0 225700 LibSegJs_baCx.seg_sound_ax fx R M V baCx_conc_s. Qed.
Definition KS_baT1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT1.regs0 LibSegJs_baT1.regs_out0).
Lemma KS_baT1_ok : BG.kept_ok 64 LibSegJs_baT1.regs0 LibSegJs_baT1.regs_out0 KS_baT1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baT1_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,6X#3710<#36830Y,T,1#3711<T,:+v24#18T,;_v2#69T,<#1"%pstring.
Lemma baT1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT1] fx R M V baT1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT1] LibSegJs_baT1.regs0 LibSegJs_baT1.kn0 LibSegJs_baT1.BR LibSegJs_baT1.PSS LibSegJs_baT1.NX0 LibSegJs_baT1.F0 225548 LibSegJs_baT1.seg_sound_ax fx R M V baT1_conc_s. Qed.
Definition KS_baT2z : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT2z.regs0 LibSegJs_baT2z.regs_out0).
Lemma KS_baT2z_ok : BG.kept_ok 64 LibSegJs_baT2z.regs0 LibSegJs_baT2z.regs_out0 KS_baT2z = true. Proof. vm_compute. reflexivity. Qed.
Definition baT2z_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#3711<#36490Y,T,1#372?<T,:v26T,;#1"%pstring.
Lemma baT2z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT2z] fx R M V baT2z_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT2z] LibSegJs_baT2z.regs0 LibSegJs_baT2z.kn0 LibSegJs_baT2z.BR LibSegJs_baT2z.PSS LibSegJs_baT2z.NX0 LibSegJs_baT2z.F0 225564 LibSegJs_baT2z.seg_sound_ax fx R M V baT2z_conc_s. Qed.
Definition KS_baT2p : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT2p.regs0 LibSegJs_baT2p.regs_out0).
Lemma KS_baT2p_ok : BG.kept_ok 64 LibSegJs_baT2p.regs0 LibSegJs_baT2p.regs_out0 KS_baT2p = true. Proof. vm_compute. reflexivity. Qed.
Definition baT2p_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#1S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,4X#3711<#3643<Y,T,1#37128T,:+v24#18"%pstring.
Lemma baT2p_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT2p] fx R M V baT2p_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT2p] LibSegJs_baT2p.regs0 LibSegJs_baT2p.kn0 LibSegJs_baT2p.BR LibSegJs_baT2p.PSS LibSegJs_baT2p.NX0 LibSegJs_baT2p.F0 225564 LibSegJs_baT2p.seg_sound_ax fx R M V baT2p_conc_s. Qed.
Definition KS_baT3e : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT3e.regs0 LibSegJs_baT3e.regs_out0).
Lemma KS_baT3e_ok : BG.kept_ok 64 LibSegJs_baT3e.regs0 LibSegJs_baT3e.regs_out0 KS_baT3e = true. Proof. vm_compute. reflexivity. Qed.
Definition baT3e_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#100S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37128#36490Y,T,1#372?<T,:v26T,;#1"%pstring.
Lemma baT3e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT3e] fx R M V baT3e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT3e] LibSegJs_baT3e.regs0 LibSegJs_baT3e.kn0 LibSegJs_baT3e.BR LibSegJs_baT3e.PSS LibSegJs_baT3e.NX0 LibSegJs_baT3e.F0 225576 LibSegJs_baT3e.seg_sound_ax fx R M V baT3e_conc_s. Qed.
Definition KS_baT3h : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT3h.regs0 LibSegJs_baT3h.regs_out0).
Lemma KS_baT3h_ok : BG.kept_ok 64 LibSegJs_baT3h.regs0 LibSegJs_baT3h.regs_out0 KS_baT3h = true. Proof. vm_compute. reflexivity. Qed.
Definition baT3h_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,:#23S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37128#36528Y,T,1#37148T,:+v24#18T,;#1"%pstring.
Lemma baT3h_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT3h] fx R M V baT3h_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT3h] LibSegJs_baT3h.regs0 LibSegJs_baT3h.kn0 LibSegJs_baT3h.BR LibSegJs_baT3h.PSS LibSegJs_baT3h.NX0 LibSegJs_baT3h.F0 225576 LibSegJs_baT3h.seg_sound_ax fx R M V baT3h_conc_s. Qed.
Definition KS_baT3l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT3l.regs0 LibSegJs_baT3l.regs_out0).
Lemma KS_baT3l_ok : BG.kept_ok 64 LibSegJs_baT3l.regs0 LibSegJs_baT3l.regs_out0 KS_baT3l = true. Proof. vm_compute. reflexivity. Qed.
Definition baT3l_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#v27#22,,1,6X#37128#36490Y,T,1#372?<T,:v26T,;#3T,14#3"%pstring.
Lemma baT3l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT3l] fx R M V baT3l_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT3l] LibSegJs_baT3l.regs0 LibSegJs_baT3l.kn0 LibSegJs_baT3l.BR LibSegJs_baT3l.PSS LibSegJs_baT3l.NX0 LibSegJs_baT3l.F0 225576 LibSegJs_baT3l.seg_sound_ax fx R M V baT3l_conc_s. Qed.
Definition KS_baT3u : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT3u.regs0 LibSegJs_baT3u.regs_out0).
Lemma KS_baT3u_ok : BG.kept_ok 64 LibSegJs_baT3u.regs0 LibSegJs_baT3u.regs_out0 KS_baT3u = true. Proof. vm_compute. reflexivity. Qed.
Definition baT3u_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#70S,8v24S,9v26S,:v27S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18B#24v27#??,,1,6X#37128#36490Y,T,1#372?<T,:v26T,;#3T,14#3"%pstring.
Lemma baT3u_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT3u] fx R M V baT3u_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT3u] LibSegJs_baT3u.regs0 LibSegJs_baT3u.kn0 LibSegJs_baT3u.BR LibSegJs_baT3u.PSS LibSegJs_baT3u.NX0 LibSegJs_baT3u.F0 225576 LibSegJs_baT3u.seg_sound_ax fx R M V baT3u_conc_s. Qed.
Definition KS_baT4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baT4.regs0 LibSegJs_baT4.regs_out0).
Lemma KS_baT4_ok : BG.kept_ok 64 LibSegJs_baT4.regs0 LibSegJs_baT4.regs_out0 KS_baT4 = true. Proof. vm_compute. reflexivity. Qed.
Definition baT4_conc_s := ",1<A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,8v24S,9v26S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18,,1,5X#37148#36<?8Y,T,1#37154T,:v24T,;v26"%pstring.
Lemma baT4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baT4] fx R M V baT4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baT4] LibSegJs_baT4.regs0 LibSegJs_baT4.kn0 LibSegJs_baT4.BR LibSegJs_baT4.PSS LibSegJs_baT4.NX0 LibSegJs_baT4.F0 225608 LibSegJs_baT4.seg_sound_ax fx R M V baT4_conc_s. Qed.
Definition KS_baTe : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTe.regs0 LibSegJs_baTe.regs_out0).
Lemma KS_baTe_ok : BG.kept_ok 64 LibSegJs_baTe.regs0 LibSegJs_baTe.regs_out0 KS_baTe = true. Proof. vm_compute. reflexivity. Qed.
Definition baTe_conc_s := ",31A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?Mav26v31B#1v31#40,,1,<X#37154#37488Y,T,1v28T,2v2T,8v29T,9v2:T,;v31T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?"%pstring.
Lemma baTe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTe] fx R M V baTe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTe] LibSegJs_baTe.regs0 LibSegJs_baTe.kn0 LibSegJs_baTe.BR LibSegJs_baTe.PSS LibSegJs_baTe.NX0 LibSegJs_baTe.F0 225620 LibSegJs_baTe.seg_sound_ax fx R M V baTe_conc_s. Qed.
Definition KS_baTx : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baTx.regs0 LibSegJs_baTx.regs_out0).
Lemma KS_baTx_ok : BG.kept_ok 64 LibSegJs_baTx.regs0 LibSegJs_baTx.regs_out0 KS_baTx = true. Proof. vm_compute. reflexivity. Qed.
Definition baTx_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,14#1B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18Mav26#La+v24#148#1000000B#1000001v30^#?#???????????????,,1,6X#37154#36490Y,T,1#372?<T,:v26T,;#=T,13v30"%pstring.
Lemma baTx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baTx] fx R M V baTx_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baTx] LibSegJs_baTx.regs0 LibSegJs_baTx.kn0 LibSegJs_baTx.BR LibSegJs_baTx.PSS LibSegJs_baTx.NX0 LibSegJs_baTx.F0 225620 LibSegJs_baTx.seg_sound_ax fx R M V baTx_conc_s. Qed.
End PMBAP1.
