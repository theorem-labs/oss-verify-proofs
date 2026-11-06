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
BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_liB LibSegJs_liD.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMLP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_liB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_liB.regs0 LibSegJs_liB.regs_out0).
Lemma KS_liB_ok : BG.kept_ok 48 LibSegJs_liB.regs0 LibSegJs_liB.regs_out0 KS_liB = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition liB_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2v2S,:v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v21#7??????????8Hv21#8P_v2#20#20v21#8Iv21#8Na#<6690#1La#<6688#<6::0,2_v2#20#20+v21##8,1,5X#7?8;<#7?918Y,T,:#<6::0T,;#<6::0Lbv21#<6::0"%pstring.
Lemma liB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_liB] fx R M V liB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_liB] LibSegJs_liB.regs0 LibSegJs_liB.kn0 LibSegJs_liB.BR LibSegJs_liB.PSS LibSegJs_liB.NX0 LibSegJs_liB.F0 522428 LibSegJs_liB.seg_sound_ax fx R M V liB_conc_s. Qed.
Definition KS_liD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_liD.regs0 LibSegJs_liD.regs_out0).
Lemma KS_liD_ok : BG.kept_ok 48 LibSegJs_liD.regs0 LibSegJs_liD.regs_out0 KS_liD = true. Proof. vm_compute. reflexivity. Qed.
Definition liD_conc_s := ",6A#v2p#2#40A#v21p#2#40S,2v2S,:v21B#7???7?800000v21#7??????????8Lav21#<6::0,,1,4X#7?994#7?9;4Y,T,:#<6::0T,;#<6::0"%pstring.
Lemma liD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_liD] fx R M V liD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_liD] LibSegJs_liD.regs0 LibSegJs_liD.kn0 LibSegJs_liD.BR LibSegJs_liD.PSS LibSegJs_liD.NX0 LibSegJs_liD.F0 522644 LibSegJs_liD.seg_sound_ax fx R M V liD_conc_s. Qed.
End PMLP.
