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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_syA LibSegJs_syB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSYP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_syA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_syA.regs0 LibSegJs_syA.regs_out0).
Lemma KS_syA_ok : BG.kept_ok 48 LibSegJs_syA.regs0 LibSegJs_syA.regs_out0 KS_syA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition syA_conc_s := ",3A#v2p#2#40S,2v2Na#<6490#1,,1,3X#59?60#59?78Y,T,:#;5?58"%pstring.
Lemma syA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_syA] fx R M V syA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_syA] LibSegJs_syA.regs0 LibSegJs_syA.kn0 LibSegJs_syA.BR LibSegJs_syA.PSS LibSegJs_syA.NX0 LibSegJs_syA.F0 368480 LibSegJs_syA.seg_sound_ax fx R M V syA_conc_s. Qed.
Definition KS_syB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_syB.regs0 LibSegJs_syB.regs_out0).
Lemma KS_syB_ok : BG.kept_ok 48 LibSegJs_syB.regs0 LibSegJs_syB.regs_out0 KS_syB = true. Proof. vm_compute. reflexivity. Qed.
Definition syB_conc_s := ",7A#v2p#2#40S,2v2B#7???7?800010v2#800000000000Hv2#10I_v2#10#10O#<6490#<6492I#<6490#2,2_v2#10#10+##<6490#2,1,7X#59?60#59?78Y,T,:#;5?58T,;#1T,<#2Nb#<6491#1Nb#<6490#1"%pstring.
Lemma syB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_syB] fx R M V syB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_syB] LibSegJs_syB.regs0 LibSegJs_syB.kn0 LibSegJs_syB.BR LibSegJs_syB.PSS LibSegJs_syB.NX0 LibSegJs_syB.F0 368480 LibSegJs_syB.seg_sound_ax fx R M V syB_conc_s. Qed.
End PMSYP.
