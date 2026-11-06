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
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_sdA LibSegJs_sdB LibSegJs_sdC.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSSDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_sdA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_sdA.regs0 LibSegJs_sdA.regs_out0).
Lemma KS_sdA_ok : BG.kept_ok 48 LibSegJs_sdA.regs0 LibSegJs_sdA.regs_out0 KS_sdA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition sdA_conc_s := ",=A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#1000r:#800000000000Hr:#8P_v2#20#20r:#128La+r:#108v21B#1000v21#800000000000La+r:#110v22,1_v2#20#20,1,;X#34?<<#54400Y,T,1#34??4T,2_v2#20U,8,:T,:v21T,;v22Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma sdA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_sdA] fx R M V sdA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_sdA] LibSegJs_sdA.regs0 LibSegJs_sdA.kn0 LibSegJs_sdA.BR LibSegJs_sdA.PSS LibSegJs_sdA.NX0 LibSegJs_sdA.F0 217036 LibSegJs_sdA.seg_sound_ax fx R M V sdA_conc_s. Qed.
Definition KS_sdB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_sdB.regs0 LibSegJs_sdB.regs_out0).
Lemma KS_sdB_ok : BG.kept_ok 48 LibSegJs_sdB.regs0 LibSegJs_sdB.regs_out0 KS_sdB = true. Proof. vm_compute. reflexivity. Qed.
Definition sdB_conc_s := ",>A#v2p#2#40A#v28p#2#40S,2_v2#20S,8v28B#7???7?800020v2#800000000000Hv2#10I_v2#20#20O#10000#;60=0B#1000v28#800000000000Hv28#8P_v2#20#20v28#128I+v28#58#8I+v28#8#8I+v28#18#8,3+v28#58#8+v28#8#8+v28#18#8,1,;X#34??4#7?994Y,T,1#3502<T,9+v28#8T,:+v28#20T,;#;2928T,<#:?460T,12+v28#58Lb+v28#18#;2928Lb+v28#8#:?438Lb+v28#58#:?460"%pstring.
Lemma sdB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_sdB] fx R M V sdB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_sdB] LibSegJs_sdB.regs0 LibSegJs_sdB.kn0 LibSegJs_sdB.BR LibSegJs_sdB.PSS LibSegJs_sdB.NX0 LibSegJs_sdB.F0 217076 LibSegJs_sdB.seg_sound_ax fx R M V sdB_conc_s. Qed.
Definition KS_sdC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_sdC.regs0 LibSegJs_sdC.regs_out0).
Lemma KS_sdC_ok : BG.kept_ok 48 LibSegJs_sdC.regs0 LibSegJs_sdC.regs_out0 KS_sdC = true. Proof. vm_compute. reflexivity. Qed.
Definition sdC_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#20S,9v29S,12v2:B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v26La_v2#10v27La_v2#18v25La_v2#20v24,,1,9X#3502<#5;1;0Y,T,1v26T,2v2T,8v27T,9v25T,:v2:T,;#:?478T,12v24"%pstring.
Lemma sdC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_sdC] fx R M V sdC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_sdC] LibSegJs_sdC.regs0 LibSegJs_sdC.kn0 LibSegJs_sdC.BR LibSegJs_sdC.PSS LibSegJs_sdC.NX0 LibSegJs_sdC.F0 217132 LibSegJs_sdC.seg_sound_ax fx R M V sdC_conc_s. Qed.
End PMSSDP.
