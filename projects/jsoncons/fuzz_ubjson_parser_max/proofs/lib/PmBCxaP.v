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
BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_acxA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBCXP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_acxA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_acxA.regs0 LibSegJb_acxA.regs_out0).
Lemma KS_acxA_ok : BG.kept_ok 48 LibSegJb_acxA.regs0 LibSegJb_acxA.regs_out0 KS_acxA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition acxA_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,4#670:<0S,:v21S,;v22S,<v24B#7???7?801400v2#800000000000Hv2#10I_v2#400#400O#12=000#136000La#13<:38#7???8000Ma#13<:40#1Ma#670:=0v23B#v23#7??????>I#670:=0#4Na#13=718#1La#136350#11557<Na#690;10#Ma#690;14#Ma#690;18#2La#690;20#690;28I#690;10#220Na#690=53#,5_v2#400#400+##670:=0#4+##690;18#4+##690;40#10+##690<40#10,1,<X#6=390#6=410Y,T,:#T,;#T,<#18T,=#Mb#670:=0v23Mb#690;18#4Lb#690<48#Lb#690;48#6=414Lb#690<40v22Lb#690;40v21"%pstring.
Lemma acxA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_acxA] fx R M V acxA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_acxA] LibSegJb_acxA.regs0 LibSegJb_acxA.kn0 LibSegJb_acxA.BR LibSegJb_acxA.PSS LibSegJb_acxA.NX0 LibSegJb_acxA.F0 447376 LibSegJb_acxA.seg_sound_ax fx R M V acxA_conc_s. Qed.
End PMBCXP.
