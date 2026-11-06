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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bvdA LibSegJb_bvdC LibSegJb_bvdD.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVDP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bvdA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_bvdA.regs0 LibSegJb_bvdA.regs_out0).
Lemma KS_bvdA_ok : BG.kept_ok 48 LibSegJb_bvdA.regs0 LibSegJb_bvdA.regs_out0 KS_bvdA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bvdA_conc_s := ",19A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000r:#7??????????8Hr:#8P#7???7000#100000001000r:#8Ka+/r:#8#7???8000#1P_v2#20#20r:#8Lar:v21B#693000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#20#20v21#18Pr:#8v21#18Lav21v22B#1000v22#800000000000Hv22#10,1_v2#20#20,1,=X#::=>4#::?04Y,T,1#::>44T,2_v2#20U,8,:T,9#7???8000T,:v21T,;v22T,12+/r:#8#7???8000Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bvdA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvdA] fx R M V bvdA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvdA] LibSegJb_bvdA.regs0 LibSegJb_bvdA.kn0 LibSegJb_bvdA.BR LibSegJb_bvdA.PSS LibSegJb_bvdA.NX0 LibSegJb_bvdA.F0 699876 LibSegJb_bvdA.seg_sound_ax fx R M V bvdA_conc_s. Qed.
Definition KS_bvdC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_bvdC.regs0 LibSegJb_bvdC.regs_out0).
Lemma KS_bvdC_ok : BG.kept_ok 48 LibSegJb_bvdC.regs0 LibSegJb_bvdC.regs_out0 KS_bvdC = true. Proof. vm_compute. reflexivity. Qed.
Definition bvdC_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v28p#2#40S,2_v2#20S,8v28S,9#7???8000S,12+/v28#8#7???8000B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000v28#7??????????8Hv28#8P#7???7000#100000001000v28#8Ka+/v28#8#7???8000#1P_v2#20#20v28#8Lav28v21B#693000v21#7?????????>8Hv21#8,,1,5X#::>44#::?98Y,T,1#::>60T,:v21T,;#"%pstring.
Lemma bvdC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvdC] fx R M V bvdC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvdC] LibSegJb_bvdC.regs0 LibSegJb_bvdC.kn0 LibSegJb_bvdC.BR LibSegJb_bvdC.PSS LibSegJb_bvdC.NX0 LibSegJb_bvdC.F0 699972 LibSegJb_bvdC.seg_sound_ax fx R M V bvdC_conc_s. Qed.
Definition KS_bvdD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_bvdD.regs0 LibSegJb_bvdD.regs_out0).
Lemma KS_bvdD_ok : BG.kept_ok 48 LibSegJb_bvdD.regs0 LibSegJb_bvdD.regs_out0 KS_bvdD = true. Proof. vm_compute. reflexivity. Qed.
Definition bvdD_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#20S,8v28S,9#7???8000S,12+/v28#8#7???8000B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000v28#7??????????8Hv28#8P#7???7000#100000001000v28#8Ka+/v28#8#7???8000#1P_v2#20#20v28#8Lav28v21B#693000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#20#20v21#18Pv28#8v21#18Lav21v22La+v21#10v23La_v2#8v26La_v2#10v27La_v2#18v29La_v2#20v2:,,1,:X#::>60#=0890Y,T,1v26T,2v2T,8v27T,9v29T,:v22T,;+*-1v22v23T,<#T,12v2:"%pstring.
Lemma bvdD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvdD] fx R M V bvdD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvdD] LibSegJb_bvdD.regs0 LibSegJb_bvdD.kn0 LibSegJb_bvdD.BR LibSegJb_bvdD.PSS LibSegJb_bvdD.NX0 LibSegJb_bvdD.F0 700000 LibSegJb_bvdD.seg_sound_ax fx R M V bvdD_conc_s. Qed.
End PMBVDP.
