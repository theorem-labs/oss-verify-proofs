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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_asyA LibSegJb_asyB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSYP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_asyA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_asyA.regs0 LibSegJb_asyA.regs_out0).
Lemma KS_asyA_ok : BG.kept_ok 48 LibSegJb_asyA.regs0 LibSegJb_asyA.regs_out0 KS_asyA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition asyA_conc_s := ",3A#v2p#2#40S,2v2Na#66?2?0#1,,1,3X#=63?0#=6408Y,T,:#138;10"%pstring.
Lemma asyA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_asyA] fx R M V asyA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_asyA] LibSegJb_asyA.regs0 LibSegJb_asyA.kn0 LibSegJb_asyA.BR LibSegJb_asyA.PSS LibSegJb_asyA.NX0 LibSegJb_asyA.F0 877552 LibSegJb_asyA.seg_sound_ax fx R M V asyA_conc_s. Qed.
Definition KS_asyB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_asyB.regs0 LibSegJb_asyB.regs_out0).
Lemma KS_asyB_ok : BG.kept_ok 48 LibSegJb_asyB.regs0 LibSegJb_asyB.regs_out0 KS_asyB = true. Proof. vm_compute. reflexivity. Qed.
Definition asyB_conc_s := ",7A#v2p#2#40S,2v2B#7???7?801010v2#800000000000Hv2#10I_v2#10#10O#66?2?0#66?2?2I#66?2?0#2,2_v2#10#10+##66?2?0#2,1,7X#=63?0#=6408Y,T,:#138;10T,;#1T,<#2Nb#66?2?1#1Nb#66?2?0#1"%pstring.
Lemma asyB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_asyB] fx R M V asyB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_asyB] LibSegJb_asyB.regs0 LibSegJb_asyB.kn0 LibSegJb_asyB.BR LibSegJb_asyB.PSS LibSegJb_asyB.NX0 LibSegJb_asyB.F0 877552 LibSegJb_asyB.seg_sound_ax fx R M V asyB_conc_s. Qed.
End PMBSYP.
