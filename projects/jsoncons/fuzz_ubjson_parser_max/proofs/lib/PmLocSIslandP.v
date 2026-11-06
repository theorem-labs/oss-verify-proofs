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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_liA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMLIP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_liA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_liA.regs0 LibSegJs_liA.regs_out0).
Lemma KS_liA_ok : BG.kept_ok 48 LibSegJs_liA.regs0 LibSegJs_liA.regs_out0 KS_liA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition liA_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21B#7???7?800400v2#800000000000Hv2#10I_v2#400#400B#7???7?800400v21#7??????????8Hv21#8P_v2#400#400v21#8Iv21#8O#10000#;60=0O#<6492#<6;=0I#<6492#73>O#<72?8#<7350I#<72?8#58O#>7>?3#>7>?4O#>7?<8#>7?<<La#>7>=0v22,4_v2#400#400+v21##8+##<6492#73>+##<72?8#58,1,7X#7?8;<#7?918Y,T,:#<6::0T,;#<6::0Lbv21#<6::0Nb#<6690#1Lb#<6688#<6::0"%pstring.
Lemma liA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_liA] fx R M V liA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_liA] LibSegJs_liA.regs0 LibSegJs_liA.kn0 LibSegJs_liA.BR LibSegJs_liA.PSS LibSegJs_liA.NX0 LibSegJs_liA.F0 522428 LibSegJs_liA.seg_sound_ax fx R M V liA_conc_s. Qed.
End PMLIP.
