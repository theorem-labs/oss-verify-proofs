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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_arvHBx.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBRVP9.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_arvHBx_0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJb_arvHBx.regs0 LibSegJb_arvHBx.regs_out0).
Lemma KS_arvHBx_0_ok : BG.kept_ok 72 LibSegJb_arvHBx.regs0 LibSegJb_arvHBx.regs_out0 KS_arvHBx_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvHBx_1 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJb_arvHBx.regs0 LibSegJb_arvHBx.regs_out1).
Lemma KS_arvHBx_1_ok : BG.kept_ok 72 LibSegJb_arvHBx.regs0 LibSegJb_arvHBx.regs_out1 KS_arvHBx_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arvHBx_conc_s := ",51A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v35S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,18v31S,19v33S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1La#1363;0#126;>8B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#693000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#693000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#693000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#126000P+/v2?#8#7???8000#40#1363;0#8B#693000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12>760Ka#8001=<><#10Na+v24#10#Pv24#180v25#8Pv26#10v25#8P+/v2?#8#7???8000#40#8001=<><#10Pv2?#200v25#8Pv30#1v25#8P+/v2?#8#7???8000#40+/v25#8#7???8000#1Mav26#,,2,4X#:>9?8#:>:00Y,T,17+v24#10D#1%_v35#p#2#40,4X#:>9?8#:?460Y,1T,17+v24#10C%_v35#p#2#40#1"%pstring.
Lemma arvHBx_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvHBx_0; KS_arvHBx_1] fx R M V arvHBx_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvHBx_0; KS_arvHBx_1] LibSegJb_arvHBx.regs0 LibSegJb_arvHBx.kn0 LibSegJb_arvHBx.BR LibSegJb_arvHBx.PSS LibSegJb_arvHBx.NX0 LibSegJb_arvHBx.F0 715256 LibSegJb_arvHBx.seg_sound_ax fx R M V arvHBx_conc_s. Qed.
End PMBRVP9.
