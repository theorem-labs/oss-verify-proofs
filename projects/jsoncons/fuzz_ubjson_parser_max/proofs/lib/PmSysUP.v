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
BigLinkBase BigLinkGlueUb0 L5Defs L5KnU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_usyA LibSegJu_usyB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcOU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSYUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcOU.
Definition KS_usyA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usyA.regs0 LibSegJu_usyA.regs_out0).
Lemma KS_usyA_ok : BG.kept_ok 48 LibSegJu_usyA.regs0 LibSegJu_usyA.regs_out0 KS_usyA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition usyA_conc_s := ",3A#v2p#2#40S,2v2Na#<74>0#1,,1,3X#5:?;4#5:?<<Y,T,:#;6?:8"%pstring.
Lemma usyA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usyA] fx R M V usyA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usyA] LibSegJu_usyA.regs0 LibSegJu_usyA.kn0 LibSegJu_usyA.BR LibSegJu_usyA.PSS LibSegJu_usyA.NX0 LibSegJu_usyA.F0 372660 LibSegJu_usyA.seg_sound_ax fx R M V usyA_conc_s. Qed.
Definition KS_usyB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usyB.regs0 LibSegJu_usyB.regs_out0).
Lemma KS_usyB_ok : BG.kept_ok 48 LibSegJu_usyB.regs0 LibSegJu_usyB.regs_out0 KS_usyB = true. Proof. vm_compute. reflexivity. Qed.
Definition usyB_conc_s := ",7A#v2p#2#40S,2v2B#7???7?800010v2#800000000000Hv2#10I_v2#10#10O#<74>0#<74>2I#<74>0#2,2_v2#10#10+##<74>0#2,1,7X#5:?;4#5:?<<Y,T,:#;6?:8T,;#1T,<#2Nb#<74>1#1Nb#<74>0#1"%pstring.
Lemma usyB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usyB] fx R M V usyB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usyB] LibSegJu_usyB.regs0 LibSegJu_usyB.kn0 LibSegJu_usyB.BR LibSegJu_usyB.PSS LibSegJu_usyB.NX0 LibSegJu_usyB.F0 372660 LibSegJu_usyB.seg_sound_ax fx R M V usyB_conc_s. Qed.
End PMSYUP.
