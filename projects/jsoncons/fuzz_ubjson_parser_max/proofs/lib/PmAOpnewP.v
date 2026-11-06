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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_anewA LibSegJa_anewB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMANEWP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_anewA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_anewA.regs0 LibSegJa_anewA.regs_out0).
Lemma KS_anewA_ok : BG.kept_ok 48 LibSegJa_anewA.regs0 LibSegJa_anewA.regs_out0 KS_anewA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition anewA_conc_s := ",6A#v2p#2#40S,2v2B#7???7?801010v2#800000000000Hv2#10I_v2#10#10B#1r:#8000000,1_v2#10#10,1,7X#12;3>4#78><0Y,T,1#12;400T,2_v2#10U,8,:Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma anewA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_anewA] fx R M V anewA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_anewA] LibSegJa_anewA.regs0 LibSegJa_anewA.kn0 LibSegJa_anewA.BR LibSegJa_anewA.PSS LibSegJa_anewA.NX0 LibSegJa_anewA.F0 1225700 LibSegJa_anewA.seg_sound_ax fx R M V anewA_conc_s. Qed.
Definition KS_anewB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_anewB.regs0 LibSegJa_anewB.regs_out0).
Lemma KS_anewB_ok : BG.kept_ok 48 LibSegJa_anewB.regs0 LibSegJa_anewB.regs_out0 KS_anewB = true. Proof. vm_compute. reflexivity. Qed.
Definition anewB_conc_s := ",:A#v2p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10B#7???7?801010v2#800000000000Hv2#10I_v2#10#10B#1r:^#?#???????????????La_v2#8v28La_v2#10v29,,1,5X#12;400#12;428Y,T,1v28T,2v2T,8v29"%pstring.
Lemma anewB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_anewB] fx R M V anewB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_anewB] LibSegJa_anewB.regs0 LibSegJa_anewB.kn0 LibSegJa_anewB.BR LibSegJa_anewB.PSS LibSegJa_anewB.NX0 LibSegJa_anewB.F0 1225728 LibSegJa_anewB.seg_sound_ax fx R M V anewB_conc_s. Qed.
End PMANEWP.
