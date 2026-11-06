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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uliA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcOU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMLIUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcOU.
Definition KS_uliA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uliA.regs0 LibSegJu_uliA.regs_out0).
Lemma KS_uliA_ok : BG.kept_ok 48 LibSegJu_uliA.regs0 LibSegJu_uliA.regs_out0 KS_uliA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uliA_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21B#7???7?800400v2#800000000000Hv2#10I_v2#400#400B#7???7?800400v21#7??????????8Hv21#8P_v2#400#400v21#8Iv21#8O#10000#;7120O#<74>2#<7<20I#<74>2#73>O#<8348#<83:0I#<8348#58O#>8?43#>8?44O#>9018#>901<La#>8?20v22,4_v2#400#400+v21##8+##<74>2#73>+##<8348#58,1,7X#80910#8096<Y,T,:#<7:?0T,;#<7:?0Lbv21#<7:?0Nb#<76>0#1Lb#<76=8#<7:?0"%pstring.
Lemma uliA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uliA] fx R M V uliA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uliA] LibSegJu_uliA.regs0 LibSegJu_uliA.kn0 LibSegJu_uliA.BR LibSegJu_uliA.PSS LibSegJu_uliA.NX0 LibSegJu_uliA.F0 526608 LibSegJu_uliA.seg_sound_ax fx R M V uliA_conc_s. Qed.
End PMLIUP.
