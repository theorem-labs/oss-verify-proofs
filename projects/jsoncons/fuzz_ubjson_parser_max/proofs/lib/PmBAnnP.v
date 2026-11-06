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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Jb0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_adlA LibSegJb_adlB LibSegJb_ashA LibSegJb_ashB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBANP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_adlA : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_adlA.regs0 LibSegJb_adlA.regs_out0).
Lemma KS_adlA_ok : BG.kept_ok 60 LibSegJb_adlA.regs0 LibSegJb_adlA.regs_out0 KS_adlA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition adlA_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v29p#2#40S,2v2S,:v21B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#v25#10000Hv25#20B#1020v29#7???????????B#_v29+v24v25#10000B#20_v29v24#10000,1_v2#20#20,1,=X#::?98#7;3?4Y,T,1#:;01<T,2_v2#10T,:v24T,;v29T,<+v24v25T,=v29T,>#1T,?#T,10/+v21#10#8Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma adlA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_adlA] fx R M V adlA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_adlA] LibSegJb_adlA.regs0 LibSegJb_adlA.kn0 LibSegJb_adlA.BR LibSegJb_adlA.PSS LibSegJb_adlA.NX0 LibSegJb_adlA.F0 700312 LibSegJb_adlA.seg_sound_ax fx R M V adlA_conc_s. Qed.
Definition KS_adlB : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_adlB.regs0 LibSegJb_adlB.regs_out0).
Lemma KS_adlB_ok : BG.kept_ok 60 LibSegJb_adlB.regs0 LibSegJb_adlB.regs_out0 KS_adlB = true. Proof. vm_compute. reflexivity. Qed.
Definition adlB_conc_s := ",9A#v2p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#10B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000La_v2#8v2;La_v2#10v2<,,1,5X#:;01<#:;028Y,T,1v2;T,2v2T,8v2<"%pstring.
Lemma adlB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_adlB] fx R M V adlB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_adlB] LibSegJb_adlB.regs0 LibSegJb_adlB.kn0 LibSegJb_adlB.BR LibSegJb_adlB.PSS LibSegJb_adlB.NX0 LibSegJb_adlB.F0 700444 LibSegJb_adlB.seg_sound_ax fx R M V adlB_conc_s. Qed.
Definition KS_ashA : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_ashA.regs0 LibSegJb_ashA.regs_out0).
Lemma KS_ashA_ok : BG.kept_ok 60 LibSegJb_ashA.regs0 LibSegJb_ashA.regs_out0 KS_ashA = true. Proof. vm_compute. reflexivity. Qed.
Definition ashA_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v29p#2#40S,2v2S,:v21S,;v22B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#v25#10000Hv25#20B#1020v29#7???????????B#_v29+v24v25#10000B#20_v29v24#10000B#v22#800,1_v2#20#20,1,=X#:;054#7;3?4Y,T,1#:;0=<T,2_v2#10T,:v24T,;v29T,<+*#20v22v24T,=+v24v25T,>#1T,?#T,10/+v21#8#8Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ashA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ashA] fx R M V ashA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ashA] LibSegJb_ashA.regs0 LibSegJb_ashA.kn0 LibSegJb_ashA.BR LibSegJb_ashA.PSS LibSegJb_ashA.NX0 LibSegJb_ashA.F0 700500 LibSegJb_ashA.seg_sound_ax fx R M V ashA_conc_s. Qed.
Definition KS_ashB : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_ashB.regs0 LibSegJb_ashB.regs_out0).
Lemma KS_ashB_ok : BG.kept_ok 60 LibSegJb_ashB.regs0 LibSegJb_ashB.regs_out0 KS_ashB = true. Proof. vm_compute. reflexivity. Qed.
Definition ashB_conc_s := ",9A#v2p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#10B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000La_v2#8v2;La_v2#10v2<,,1,5X#:;0=<#:;0>8Y,T,1v2;T,2v2T,8v2<"%pstring.
Lemma ashB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ashB] fx R M V ashB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ashB] LibSegJb_ashB.regs0 LibSegJb_ashB.kn0 LibSegJb_ashB.BR LibSegJb_ashB.PSS LibSegJb_ashB.NX0 LibSegJb_ashB.F0 700636 LibSegJb_ashB.seg_sound_ax fx R M V ashB_conc_s. Qed.
End PMBANP.
