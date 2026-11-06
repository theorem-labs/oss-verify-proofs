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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_erA LibSegJs_erB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMERP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_erA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_erA.regs0 LibSegJs_erA.regs_out0).
Lemma KS_erA_ok : BG.kept_ok 48 LibSegJs_erA.regs0 LibSegJs_erA.regs_out0 KS_erA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition erA_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v21#7??????????0Hv21#8P_v2#80#80v21#10Iv21#10B#1v22#40Na#<6260#1,2_v2#20#20+v21##10,1,4X#36490#364>4Y,Lb+v21#8#;5?20Lbv21v22"%pstring.
Lemma erA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_erA] fx R M V erA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_erA] LibSegJs_erA.regs0 LibSegJs_erA.kn0 LibSegJs_erA.BR LibSegJs_erA.PSS LibSegJs_erA.NX0 LibSegJs_erA.F0 222352 LibSegJs_erA.seg_sound_ax fx R M V erA_conc_s. Qed.
Definition KS_erB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_erB.regs0 LibSegJs_erB.regs_out0).
Lemma KS_erB_ok : BG.kept_ok 48 LibSegJs_erB.regs0 LibSegJs_erB.regs_out0 KS_erB = true. Proof. vm_compute. reflexivity. Qed.
Definition erB_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v21#7??????????0Hv21#8P_v2#80#80v21#10Iv21#10B#1v22#40O#10000#;60=0O#<6260#<6262I#<6260#2O#>7<:8#>7<;0Ma#>7<;0#1O#>7<;4#>7<;8La#>7<;8#>7<<0O#>7<<0#>7<<8O#>7<=0#>7=<8O#>7==0#>7><8I#>7<:8#220O#>7>?3#>7>?4,6_v2#80#80+v21##10+##<6260#2+##>7<;0#4+##>7<=0#8+##>7==0#8,1,<X#36490#364>4Y,T,;#1T,<#8T,=#Lb+v21#8#;5?20Lbv21v22Nb#<6261#1Nb#<6260#1Mb#>7<;0#2Lb#>7==0#;5?20Lb#>7<=0#55;78"%pstring.
Lemma erB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_erB] fx R M V erB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_erB] LibSegJs_erB.regs0 LibSegJs_erB.kn0 LibSegJs_erB.BR LibSegJs_erB.PSS LibSegJs_erB.NX0 LibSegJs_erB.F0 222352 LibSegJs_erB.seg_sound_ax fx R M V erB_conc_s. Qed.
End PMERP.
