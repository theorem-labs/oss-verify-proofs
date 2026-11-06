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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_brrA LibSegJb_brrB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBRRP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_brrA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_brrA.regs0 LibSegJb_brrA.regs_out0).
Lemma KS_brrA_ok : BG.kept_ok 48 LibSegJb_brrA.regs0 LibSegJb_brrA.regs_out0 KS_brrA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition brrA_conc_s := ",8A#v2p#2#40S,2v2O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20,1_v2#20#20,1,<X#:8738#:<>2<Y,T,1#:8764T,2_v2#20U,8,;U,9,:T,;#13<:38T,12#7???8000Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma brrA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_brrA] fx R M V brrA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_brrA] LibSegJb_brrA.regs0 LibSegJb_brrA.kn0 LibSegJb_brrA.BR LibSegJb_brrA.PSS LibSegJb_brrA.NX0 LibSegJb_brrA.F0 689976 LibSegJb_brrA.seg_sound_ax fx R M V brrA_conc_s. Qed.
Definition KS_brrB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_brrB.regs0 LibSegJb_brrB.regs_out0).
Lemma KS_brrB_ok : BG.kept_ok 48 LibSegJb_brrB.regs0 LibSegJb_brrB.regs_out0 KS_brrB = true. Proof. vm_compute. reflexivity. Qed.
Definition brrB_conc_s := ",1;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40S,2_v2#20S,8v29S,9v28S,12#7???8000B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000v28#7????????>78Hv28#8P#7???7000#100000001000v28#188P_v2#20#20v28#188La_v2#8v25La_v2#10v27La_v2#18v26La_v2#20v24La+v28#180v2;B#1000v2;#800000000000Hv2;#8Ka+/v28#8#7???8030#1,,1,:X#:8764#:=088Y,T,1v25T,2v2T,8v27T,9v26T,:v28T,;v2;T,<v29T,12v24"%pstring.
Lemma brrB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_brrB] fx R M V brrB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_brrB] LibSegJb_brrB.regs0 LibSegJb_brrB.kn0 LibSegJb_brrB.BR LibSegJb_brrB.PSS LibSegJb_brrB.NX0 LibSegJb_brrB.F0 690020 LibSegJb_brrB.seg_sound_ax fx R M V brrB_conc_s. Qed.
End PMBRRP.
