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
BigLinkBase BigLinkGlueUb0 L5Defs L5KnU L5KnAU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_usdA LibSegJu_usdB LibSegJu_usdC.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUSDP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_usdA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usdA.regs0 LibSegJu_usdA.regs_out0).
Lemma KS_usdA_ok : BG.kept_ok 48 LibSegJu_usdA.regs0 LibSegJu_usdA.regs_out0 KS_usdA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition usdA_conc_s := ",=A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#1000r:#800000000000Hr:#8P_v2#20#20r:#128La+r:#108v21B#1000v21#800000000000La+r:#110v22,1_v2#20#20,1,;X#357?4#55454Y,T,1#3581<T,2_v2#20U,8,:T,:v21T,;v22Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma usdA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usdA] fx R M V usdA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usdA] LibSegJu_usdA.regs0 LibSegJu_usdA.kn0 LibSegJu_usdA.BR LibSegJu_usdA.PSS LibSegJu_usdA.NX0 LibSegJu_usdA.F0 219124 LibSegJu_usdA.seg_sound_ax fx R M V usdA_conc_s. Qed.
Definition KS_usdB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usdB.regs0 LibSegJu_usdB.regs_out0).
Lemma KS_usdB_ok : BG.kept_ok 48 LibSegJu_usdB.regs0 LibSegJu_usdB.regs_out0 KS_usdB = true. Proof. vm_compute. reflexivity. Qed.
Definition usdB_conc_s := ",>A#v2p#2#40A#v28p#2#40S,2_v2#20S,8v28B#7???7?800020v2#800000000000Hv2#10I_v2#20#20O#10000#;7120B#1000v28#800000000000Hv28#8P_v2#20#20v28#128I+v28#58#8I+v28#8#8I+v28#18#8,3+v28#58#8+v28#8#8+v28#18#8,1,;X#3581<#809>8Y,T,1#35854T,9+v28#8T,:+v28#20T,;#;3978T,<#;04;0T,12+v28#58Lb+v28#18#;3978Lb+v28#8#;0488Lb+v28#58#;04;0"%pstring.
Lemma usdB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usdB] fx R M V usdB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usdB] LibSegJu_usdB.regs0 LibSegJu_usdB.kn0 LibSegJu_usdB.BR LibSegJu_usdB.PSS LibSegJu_usdB.NX0 LibSegJu_usdB.F0 219164 LibSegJu_usdB.seg_sound_ax fx R M V usdB_conc_s. Qed.
Definition KS_usdC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usdC.regs0 LibSegJu_usdC.regs_out0).
Lemma KS_usdC_ok : BG.kept_ok 48 LibSegJu_usdC.regs0 LibSegJu_usdC.regs_out0 KS_usdC = true. Proof. vm_compute. reflexivity. Qed.
Definition usdC_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#20S,9v29S,12v2:B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v26La_v2#10v27La_v2#18v25La_v2#20v24,,1,9X#35854#5<204Y,T,1v26T,2v2T,8v27T,9v25T,:v2:T,;#;04<8T,12v24"%pstring.
Lemma usdC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usdC] fx R M V usdC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usdC] LibSegJu_usdC.regs0 LibSegJu_usdC.kn0 LibSegJu_usdC.BR LibSegJu_usdC.PSS LibSegJu_usdC.NX0 LibSegJu_usdC.F0 219220 LibSegJu_usdC.seg_sound_ax fx R M V usdC_conc_s. Qed.
End PMUSDP.
