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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aglSiN_c1 LibSegJa_aglSlN_c1 LibSegJa_aglSIN LibSegJa_aglSLN.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAGL4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aglSiN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglSiN_c1.regs0 LibSegJa_aglSiN_c1.regs_out0).
Lemma KS_aglSiN_ok : BG.kept_ok 80 LibSegJa_aglSiN_c1.regs0 LibSegJa_aglSiN_c1.regs_out0 KS_aglSiN = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aglSiN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16#1S,17+v2?#30S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,6X#:??<4#:>974Y,T,1#:??=8T,:v26T,;#4T,16#4"%pstring.
Lemma aglSiN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSiN] fx R M V aglSiN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSiN] LibSegJa_aglSiN_c1.regs0 LibSegJa_aglSiN_c1.kn0 LibSegJa_aglSiN_c1.BR LibSegJa_aglSiN_c1.PSS LibSegJa_aglSiN_c1.NX0 LibSegJa_aglSiN_c1.F0 720836 LibSegJa_aglSiN_c1.seg_sound_ax fx R M V aglSiN_conc_s. Qed.
Definition KS_aglSlN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglSlN_c1.regs0 LibSegJa_aglSlN_c1.regs_out0).
Lemma KS_aglSlN_ok : BG.kept_ok 80 LibSegJa_aglSlN_c1.regs0 LibSegJa_aglSlN_c1.regs_out0 KS_aglSlN = true. Proof. vm_compute. reflexivity. Qed.
Definition aglSlN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16#4S,17+v2?#60S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,5X#;014<#:>974Y,T,1#;02?<T,:v26T,;#4"%pstring.
Lemma aglSlN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSlN] fx R M V aglSlN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSlN] LibSegJa_aglSlN_c1.regs0 LibSegJa_aglSlN_c1.kn0 LibSegJa_aglSlN_c1.BR LibSegJa_aglSlN_c1.PSS LibSegJa_aglSlN_c1.NX0 LibSegJa_aglSlN_c1.F0 721228 LibSegJa_aglSlN_c1.seg_sound_ax fx R M V aglSlN_conc_s. Qed.
Definition KS_aglSIN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglSIN.regs0 LibSegJa_aglSIN.regs_out0).
Lemma KS_aglSIN_ok : BG.kept_ok 80 LibSegJa_aglSIN.regs0 LibSegJa_aglSIN.regs_out0 KS_aglSIN = true. Proof. vm_compute. reflexivity. Qed.
Definition aglSIN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#50S,17#2S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,5X#;0184#:>974Y,T,1#;03:0T,:v26T,;#4"%pstring.
Lemma aglSIN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSIN] fx R M V aglSIN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSIN] LibSegJa_aglSIN.regs0 LibSegJa_aglSIN.kn0 LibSegJa_aglSIN.BR LibSegJa_aglSIN.PSS LibSegJa_aglSIN.NX0 LibSegJa_aglSIN.F0 721284 LibSegJa_aglSIN.seg_sound_ax fx R M V aglSIN_conc_s. Qed.
Definition KS_aglSLN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglSLN.regs0 LibSegJa_aglSLN.regs_out0).
Lemma KS_aglSLN_ok : BG.kept_ok 80 LibSegJa_aglSLN.regs0 LibSegJa_aglSLN.regs_out0 KS_aglSLN = true. Proof. vm_compute. reflexivity. Qed.
Definition aglSLN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#70S,17#8S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,5X#;00<8#:>974Y,T,1#;0338T,:v26T,;#4"%pstring.
Lemma aglSLN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSLN] fx R M V aglSLN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSLN] LibSegJa_aglSLN.regs0 LibSegJa_aglSLN.kn0 LibSegJa_aglSLN.BR LibSegJa_aglSLN.PSS LibSegJa_aglSLN.NX0 LibSegJa_aglSLN.F0 721096 LibSegJa_aglSLN.seg_sound_ax fx R M V aglSLN_conc_s. Qed.
End PMAGL4.
