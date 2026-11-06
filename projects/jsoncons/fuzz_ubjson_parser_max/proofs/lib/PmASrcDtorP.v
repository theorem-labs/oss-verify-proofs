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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_asdA LibSegJa_asdB LibSegJa_asdC.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMASDP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_asdA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_asdA.regs0 LibSegJa_asdA.regs_out0).
Lemma KS_asdA_ok : BG.kept_ok 48 LibSegJa_asdA.regs0 LibSegJa_asdA.regs_out0 KS_asdA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition asdA_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000r:#7????????>=8Hr:#8P#7???7000#100000001000r:#128Ka+/r:#8#7???8001#24P_v2#30#30r:#128La+r:#108v21B#1000v21#800000000000La+r:#110v22,1_v2#30#30,1,>X#::34<#<>:58Y,T,1#::3:<T,2_v2#30U,8,:T,:v21T,;v22T,<#T,13#7???8000Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma asdA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_asdA] fx R M V asdA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_asdA] LibSegJa_asdA.regs0 LibSegJa_asdA.kn0 LibSegJa_asdA.BR LibSegJa_asdA.PSS LibSegJa_asdA.NX0 LibSegJa_asdA.F0 697164 LibSegJa_asdA.seg_sound_ax fx R M V asdA_conc_s. Qed.
Definition KS_asdB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_asdB.regs0 LibSegJa_asdB.regs_out0).
Lemma KS_asdB_ok : BG.kept_ok 48 LibSegJa_asdB.regs0 LibSegJa_asdB.regs_out0 KS_asdB = true. Proof. vm_compute. reflexivity. Qed.
Definition asdB_conc_s := ",13A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28S,13#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7????????>=8Hv28#8P#7???7000#100000001000v28#128Ka+/v28#8#7???8001#24P_v2#30#30v28#128I+v28#58#8I+v28#8#8I+v28#18#8,3+v28#58#8+v28#8#8+v28#18#8,1,:X#::3:<#?9?><Y,T,1#::418T,9+v28#8T,:+v28#20T,;#T,12+v28#58Lb+v28#18#130138Lb+v28#58#12<;;8Lb+v28#8#12<;90"%pstring.
Lemma asdB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_asdB] fx R M V asdB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_asdB] LibSegJa_asdB.regs0 LibSegJa_asdB.kn0 LibSegJa_asdB.BR LibSegJa_asdB.PSS LibSegJa_asdB.NX0 LibSegJa_asdB.F0 697260 LibSegJa_asdB.seg_sound_ax fx R M V asdB_conc_s. Qed.
Definition KS_asdC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_asdC.regs0 LibSegJa_asdC.regs_out0).
Lemma KS_asdC_ok : BG.kept_ok 48 LibSegJa_asdC.regs0 LibSegJa_asdC.regs_out0 KS_asdC = true. Proof. vm_compute. reflexivity. Qed.
Definition asdC_conc_s := ",16A#v2p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#30S,9v29S,12v2:O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30La_v2#8v27La_v2#10v26La_v2#18v25La_v2#20v24La_v2#28v23,,1,:X#::418#=5808Y,T,1v27T,2v2T,8v26T,9v25T,:v2:T,;#12<;=0T,12v24T,13v23"%pstring.
Lemma asdC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_asdC] fx R M V asdC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_asdC] LibSegJa_asdC.regs0 LibSegJa_asdC.kn0 LibSegJa_asdC.BR LibSegJa_asdC.PSS LibSegJa_asdC.NX0 LibSegJa_asdC.F0 697368 LibSegJa_asdC.seg_sound_ax fx R M V asdC_conc_s. Qed.
End PMASDP.
