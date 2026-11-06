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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_aglSiN_c1 LibSegJb_aglSlN_c1 LibSegJb_aglSIN LibSegJb_aglSLN.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBGL4.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aglSiN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_aglSiN_c1.regs0 LibSegJb_aglSiN_c1.regs_out0).
Lemma KS_aglSiN_ok : BG.kept_ok 80 LibSegJb_aglSiN_c1.regs0 LibSegJb_aglSiN_c1.regs_out0 KS_aglSiN = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aglSiN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16#1S,17+v2?#30S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,6X#;17:4#:?:18Y,T,1#;17;8T,:v26T,;#4T,16#4"%pstring.
Lemma aglSiN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSiN] fx R M V aglSiN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSiN] LibSegJb_aglSiN_c1.regs0 LibSegJb_aglSiN_c1.kn0 LibSegJb_aglSiN_c1.BR LibSegJb_aglSiN_c1.PSS LibSegJb_aglSiN_c1.NX0 LibSegJb_aglSiN_c1.F0 726948 LibSegJb_aglSiN_c1.seg_sound_ax fx R M V aglSiN_conc_s. Qed.
Definition KS_aglSlN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_aglSlN_c1.regs0 LibSegJb_aglSlN_c1.regs_out0).
Lemma KS_aglSlN_ok : BG.kept_ok 80 LibSegJb_aglSlN_c1.regs0 LibSegJb_aglSlN_c1.regs_out0 KS_aglSlN = true. Proof. vm_compute. reflexivity. Qed.
Definition aglSlN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16#4S,17+v2?#60S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,5X#;192<#:?:18Y,T,1#;1:=<T,:v26T,;#4"%pstring.
Lemma aglSlN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSlN] fx R M V aglSlN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSlN] LibSegJb_aglSlN_c1.regs0 LibSegJb_aglSlN_c1.kn0 LibSegJb_aglSlN_c1.BR LibSegJb_aglSlN_c1.PSS LibSegJb_aglSlN_c1.NX0 LibSegJb_aglSlN_c1.F0 727340 LibSegJb_aglSlN_c1.seg_sound_ax fx R M V aglSlN_conc_s. Qed.
Definition KS_aglSIN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_aglSIN.regs0 LibSegJb_aglSIN.regs_out0).
Lemma KS_aglSIN_ok : BG.kept_ok 80 LibSegJb_aglSIN.regs0 LibSegJb_aglSIN.regs_out0 KS_aglSIN = true. Proof. vm_compute. reflexivity. Qed.
Definition aglSIN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#50S,17#2S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,5X#;1964#:?:18Y,T,1#;1;80T,:v26T,;#4"%pstring.
Lemma aglSIN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSIN] fx R M V aglSIN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSIN] LibSegJb_aglSIN.regs0 LibSegJb_aglSIN.kn0 LibSegJb_aglSIN.BR LibSegJb_aglSIN.PSS LibSegJb_aglSIN.NX0 LibSegJb_aglSIN.F0 727396 LibSegJb_aglSIN.seg_sound_ax fx R M V aglSIN_conc_s. Qed.
Definition KS_aglSLN : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_aglSLN.regs0 LibSegJb_aglSLN.regs_out0).
Lemma KS_aglSLN_ok : BG.kept_ok 80 LibSegJb_aglSLN.regs0 LibSegJb_aglSLN.regs_out0 KS_aglSLN = true. Proof. vm_compute. reflexivity. Qed.
Definition aglSLN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#70S,17#8S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B^#8#v31^#?#???????????????,,1,5X#;18:8#:?:18Y,T,1#;1;18T,:v26T,;#4"%pstring.
Lemma aglSLN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglSLN] fx R M V aglSLN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglSLN] LibSegJb_aglSLN.regs0 LibSegJb_aglSLN.kn0 LibSegJb_aglSLN.BR LibSegJb_aglSLN.PSS LibSegJb_aglSLN.NX0 LibSegJb_aglSLN.F0 727208 LibSegJb_aglSLN.seg_sound_ax fx R M V aglSLN_conc_s. Qed.
End PMBGL4.
