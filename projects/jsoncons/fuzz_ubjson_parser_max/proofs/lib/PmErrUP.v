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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uerA LibSegJu_uerB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcOU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMERUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcOU.
Definition KS_uerA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uerA.regs0 LibSegJu_uerA.regs_out0).
Lemma KS_uerA_ok : BG.kept_ok 48 LibSegJu_uerA.regs0 LibSegJu_uerA.regs_out0 KS_uerA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uerA_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v21#7??????????0Hv21#8P_v2#80#80v21#10Iv21#10B#1v22#40Na#<72;0#1,2_v2#20#20+v21##10,1,4X#370:<#37100Y,Lb+v21#8#;6?70Lbv21v22"%pstring.
Lemma uerA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uerA] fx R M V uerA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uerA] LibSegJu_uerA.regs0 LibSegJu_uerA.kn0 LibSegJu_uerA.BR LibSegJu_uerA.PSS LibSegJu_uerA.NX0 LibSegJu_uerA.F0 225452 LibSegJu_uerA.seg_sound_ax fx R M V uerA_conc_s. Qed.
Definition KS_uerB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uerB.regs0 LibSegJu_uerB.regs_out0).
Lemma KS_uerB_ok : BG.kept_ok 48 LibSegJu_uerB.regs0 LibSegJu_uerB.regs_out0 KS_uerB = true. Proof. vm_compute. reflexivity. Qed.
Definition uerB_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v21#7??????????0Hv21#8P_v2#80#80v21#10Iv21#10B#1v22#40O#10000#;7120O#<72;0#<72;2I#<72;0#2O#>8<?8#>8=00Ma#>8=00#1O#>8=04#>8=08La#>8=08#>8=10O#>8=10#>8=18O#>8=20#>8>18O#>8>20#>8?18I#>8<?8#220O#>8?43#>8?44,6_v2#80#80+v21##10+##<72;0#2+##>8=00#4+##>8=20#8+##>8>20#8,1,<X#370:<#37100Y,T,;#1T,<#8T,=#Lb+v21#8#;6?70Lbv21v22Nb#<72;1#1Nb#<72;0#1Mb#>8=00#2Lb#>8>20#;6?70Lb#>8=20#56;<<"%pstring.
Lemma uerB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uerB] fx R M V uerB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uerB] LibSegJu_uerB.regs0 LibSegJu_uerB.kn0 LibSegJu_uerB.BR LibSegJu_uerB.PSS LibSegJu_uerB.NX0 LibSegJu_uerB.F0 225452 LibSegJu_uerB.seg_sound_ax fx R M V uerB_conc_s. Qed.
End PMERUP.
