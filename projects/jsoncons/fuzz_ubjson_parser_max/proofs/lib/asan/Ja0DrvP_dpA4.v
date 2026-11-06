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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_dpA4.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpA4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpA4 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJa_dpA4.regs0 LibSegJa_dpA4.regs_out0).
Lemma KS_dpA4_ok : BG.kept_ok 56 LibSegJa_dpA4.regs0 LibSegJa_dpA4.regs_out0 KS_dpA4 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpA4_conc_s := ",22A#v2p#2#40A#v28p#2#40S,1#:7640S,2v2S,:#14><<S,;+v2#18B#7???7?811000v2#800000000000Hv2#10I_v2#<:0#<:0Ja_v2#<:0#<:0O#10000#134000Ka+/v2#8#7???7?8:#18La#7???:9=8#La#800<9>;0#I#136?30#4I#136?58#8I#68?5:4#1I#68?5:5#1Na#13;9=8#1Na#1<<87<#1La#13:<?8#7???8000La#1344<0#1224:8La#1344<8#11<1<4La#68>=<0v28Ma#136?;<#????????Ma#136?30#5La#136?90#400La#136?50#68?9:0La#136?58#68?5:4Ma#136?<0#????????Na#13;9=9#1La#134640#1249:<Ma+v2#18#La#134648#124=;0,5_v2#<:0#<:0#136?30#4#136?58#8#68?5:4#1#68?5:5#1,1,?X#62:54#:7640Y,T,5#3T,:#2T,;v28T,<v28T,=#68?5:6T,>#T,?#2T,10#1T,11#:Mb#136?30#5Lb#136?58#68?5:6Nb#68?5:5#:Nb#68?5:4#30"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpA4_conc : ltac:(r1mk L5KA.zeros_at [KS_dpA4] fx R M V dpA4_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_dpA4] LibSegJa_dpA4.regs0 LibSegJa_dpA4.kn0 LibSegJa_dpA4.BR LibSegJa_dpA4.PSS LibSegJa_dpA4.NX0 LibSegJa_dpA4.F0 404052 LibSegJa_dpA4.seg_sound_ax fx R M V dpA4_conc_s. Qed.
End SE.
End AS0DRVP_dpA4.
