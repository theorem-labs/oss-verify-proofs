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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_eaA LibSegJs_eoA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSENDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_eaA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_eaA.regs0 LibSegJs_eaA.regs_out0).
Lemma KS_eaA_ok : BG.kept_ok 48 LibSegJs_eaA.regs0 LibSegJs_eaA.regs_out0 KS_eaA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition eaA_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>80Hv24#8P_v2#10#10v24#180B#7???7?800010v25#7??????????8Hv25#8P_v2#10#10v25#8O#10000#;60=0Lav25#:?1>8Ma+v24#<v21Na+v24#10#Ma+v24#14#La+v24#168v22La+v24#170+v22v23B#1v21#400B#1000v22#7???????0000B#40v23#8020Hv23#20I+v24#8#8I+v24#170#8Pv24#180v25#8,4_v2#10#10+v24#8#1+v24#<#4+v24#170#8,1,;X#35><8#35?38Y,T,:_+v22v23#20T,;#1T,</v23#20T,=#Lb+v24#170_+v22v23#20Nb+v24#8#1Mb+v24#<_v21#1Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma eaA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_eaA] fx R M V eaA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_eaA] LibSegJs_eaA.regs0 LibSegJs_eaA.kn0 LibSegJs_eaA.BR LibSegJs_eaA.PSS LibSegJs_eaA.NX0 LibSegJs_eaA.F0 220872 LibSegJs_eaA.seg_sound_ax fx R M V eaA_conc_s. Qed.
Definition KS_eoA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_eoA.regs0 LibSegJs_eoA.regs_out0).
Lemma KS_eoA_ok : BG.kept_ok 48 LibSegJs_eoA.regs0 LibSegJs_eoA.regs_out0 KS_eoA = true. Proof. vm_compute. reflexivity. Qed.
Definition eoA_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>80Hv24#8P_v2#10#10v24#180B#7???7?800010v25#7??????????8Hv25#8P_v2#10#10v25#8O#10000#;60=0Lav25#:?1>8Ma+v24#<v21Na+v24#10#Ma+v24#14#La+v24#168v22La+v24#170+v22v23B#1v21#400B#1000v22#7???????0000B#40v23#8020Hv23#20I+v24#8#8I+v24#170#8Pv24#180v25#8,4_v2#10#10+v24#8#1+v24#<#4+v24#170#8,1,;X#366<8#36738Y,T,:_+v22v23#20T,;#1T,</v23#20T,=#Lb+v24#170_+v22v23#20Nb+v24#8#1Mb+v24#<_v21#1Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma eoA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_eoA] fx R M V eoA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_eoA] LibSegJs_eoA.regs0 LibSegJs_eoA.kn0 LibSegJs_eoA.BR LibSegJs_eoA.PSS LibSegJs_eoA.NX0 LibSegJs_eoA.F0 222920 LibSegJs_eoA.seg_sound_ax fx R M V eoA_conc_s. Qed.
End PMSENDP.
