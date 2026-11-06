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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_aeaA LibSegJb_aeoA LibSegJb_aepB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBENP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aeaA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aeaA.regs0 LibSegJb_aeaA.regs_out0).
Lemma KS_aeaA_ok : BG.kept_ok 48 LibSegJb_aeaA.regs0 LibSegJb_aeaA.regs_out0 KS_aeaA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aeaA_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#20#20v24#180B#693000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#20#20v25#8Lav25#12>760Ka#8001=<>?#1Ma+v24#<v21Na+v24#10#Ma+v24#14#La+v24#168v22La+v24#170+v22v23B#1v21#400B#1000v22#7???????0000B#40v23#8020Hv23#20Pv24#180v25#8,3_v2#20#20+v24#8#1+v24#<#4,1,10X#:>43<#;1198Y,T,2_v2#10T,:+v24#168T,;_+v22v23#20T,<v23T,=#T,>+v22v23T,?v22T,10#20T,11_+v22v23#20Lb_v2#8r1Nb+v24#8#1Mb+v24#<_v21#1Lb_v2#18r9Lb_v2#10r8"%pstring.
Lemma aeaA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeaA] fx R M V aeaA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeaA] LibSegJb_aeaA.regs0 LibSegJb_aeaA.kn0 LibSegJb_aeaA.BR LibSegJb_aeaA.PSS LibSegJb_aeaA.NX0 LibSegJb_aeaA.F0 713788 LibSegJb_aeaA.seg_sound_ax fx R M V aeaA_conc_s. Qed.
Definition KS_aeoA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aeoA.regs0 LibSegJb_aeoA.regs_out0).
Lemma KS_aeoA_ok : BG.kept_ok 48 LibSegJb_aeoA.regs0 LibSegJb_aeoA.regs_out0 KS_aeoA = true. Proof. vm_compute. reflexivity. Qed.
Definition aeoA_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#20#20v24#180B#693000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#20#20v25#8Lav25#12>760Ka#8001=<?6#1Ma+v24#<v21Na+v24#10#Ma+v24#14#La+v24#168v22La+v24#170+v22v23B#1v21#400B#1000v22#7???????0000B#40v23#8020Hv23#20Pv24#180v25#8,3_v2#20#20+v24#8#1+v24#<#4,1,10X#;02:4#;1198Y,T,2_v2#10T,:+v24#168T,;_+v22v23#20T,<v23T,=#T,>+v22v23T,?v22T,10#20T,11_+v22v23#20Lb_v2#8r1Nb+v24#8#1Mb+v24#<_v21#1Lb_v2#18r9Lb_v2#10r8"%pstring.
Lemma aeoA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeoA] fx R M V aeoA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeoA] LibSegJb_aeoA.regs0 LibSegJb_aeoA.kn0 LibSegJb_aeoA.BR LibSegJb_aeoA.PSS LibSegJb_aeoA.NX0 LibSegJb_aeoA.F0 721572 LibSegJb_aeoA.seg_sound_ax fx R M V aeoA_conc_s. Qed.
Definition KS_aepB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_aepB.regs0 LibSegJb_aepB.regs_out0).
Lemma KS_aepB_ok : BG.kept_ok 48 LibSegJb_aepB.regs0 LibSegJb_aepB.regs_out0 KS_aepB = true. Proof. vm_compute. reflexivity. Qed.
Definition aepB_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10S,:+v24#168S,;v28S,<v27B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#693000v24#7????????>80Hv24#8P_v2#20#20v24#180La_v2#8v29I+v24#170#8,1+v24#170#8,1,6X#;119<#:;054Y,T,1v29T,2v2T,;v27Lb+v24#170v28"%pstring.
Lemma aepB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aepB] fx R M V aepB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aepB] LibSegJb_aepB.regs0 LibSegJb_aepB.kn0 LibSegJb_aepB.BR LibSegJb_aepB.PSS LibSegJb_aepB.NX0 LibSegJb_aepB.F0 725404 LibSegJb_aepB.seg_sound_ax fx R M V aepB_conc_s. Qed.
End PMBENP.
