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
BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_acxA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMACXP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_acxA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_acxA.regs0 LibSegJa_acxA.regs_out0).
Lemma KS_acxA_ok : BG.kept_ok 48 LibSegJa_acxA.regs0 LibSegJa_acxA.regs_out0 KS_acxA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition acxA_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,4#66>=80S,:v21S,;v22S,<v24B#7???7?801400v2#800000000000Hv2#10I_v2#400#400O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1Ma#66>=90v23B#v23#7??????>I#66>=90#4Na#13;9=8#1La#1345>8#113744Na#68>==0#Ma#68>==4#Ma#68>==8#2La#68>=>0#68>=>8I#68>==0#220Na#68?013#,5_v2#400#400+##66>=90#4+##68>==8#4+##68>>00#10+##68>?00#10,1,<X#6=0<0#6=140Y,T,:#T,;#T,<#18T,=#Mb#66>=90v23Mb#68>==8#4Lb#68>?08#Lb#68>>08#6=144Lb#68>?00v22Lb#68>>00v21"%pstring.
Lemma acxA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_acxA] fx R M V acxA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_acxA] LibSegJa_acxA.regs0 LibSegJa_acxA.kn0 LibSegJa_acxA.BR LibSegJa_acxA.PSS LibSegJa_acxA.NX0 LibSegJa_acxA.F0 446656 LibSegJa_acxA.seg_sound_ax fx R M V acxA_conc_s. Qed.
End PMACXP.
