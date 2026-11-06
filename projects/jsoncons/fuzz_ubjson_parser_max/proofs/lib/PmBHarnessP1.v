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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_haA0 LibSegJb_haA16 LibSegJb_haB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBHP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_haA0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haA0.regs0 LibSegJb_haA0.regs_out0).
Lemma KS_haA0_ok : BG.kept_ok 64 LibSegJb_haA0.regs0 LibSegJb_haA0.regs_out0 KS_haA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition haA0_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80O#12=000#136000La#13<:38#7???8000Ma#13<:40#1,1_v2#80#80,1,19X#:791<#5=;48Y,T,1#:798<T,2_v2#80T,8v2T,9_v2#80T,:#400T,;#13<:38T,<#1T,16v22T,17v21T,19#7???8000Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb_v2#80#"%pstring.
Lemma haA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haA0] fx R M V haA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haA0] LibSegJb_haA0.regs0 LibSegJb_haA0.kn0 LibSegJb_haA0.BR LibSegJb_haA0.PSS LibSegJb_haA0.NX0 LibSegJb_haA0.F0 686364 LibSegJb_haA0.seg_sound_ax fx R M V haA0_conc_s. Qed.
Definition KS_haA16 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haA16.regs0 LibSegJb_haA16.regs_out0).
Lemma KS_haA16_ok : BG.kept_ok 64 LibSegJb_haA16.regs0 LibSegJb_haA16.regs_out0 KS_haA16 = true. Proof. vm_compute. reflexivity. Qed.
Definition haA16_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2+v2#10S,:v21S,;v22B#7???7?8010<0v2#7??????????0Hv2#20I_v2#80#90O#12=000#136000La#13<:38#7???8000Ma#13<:40#1,1_v2#80#90,1,19X#:791<#5=;48Y,T,1#:798<T,2_v2#80T,8+v2#10T,9_v2#80T,:#400T,;#13<:38T,<#1T,16v22T,17v21T,19#7???8000Lb_v2#50r1:Lb_v2#48r19Lb_v2#40r18Lb_v2#38r17Lb_v2#30r16Lb_v2#28r15Lb_v2#20r14Lb_v2#18r13Lb_v2#10r12Lb_v2#8r9Lbv2r8Lb+v2#8r1Lb_v2#70#"%pstring.
Lemma haA16_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haA16] fx R M V haA16_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haA16] LibSegJb_haA16.regs0 LibSegJb_haA16.kn0 LibSegJb_haA16.BR LibSegJb_haA16.PSS LibSegJb_haA16.NX0 LibSegJb_haA16.F0 686364 LibSegJb_haA16.seg_sound_ax fx R M V haA16_conc_s. Qed.
Definition KS_haB : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haB.regs0 LibSegJb_haB.regs_out0).
Lemma KS_haB_ok : BG.kept_ok 64 LibSegJb_haB.regs0 LibSegJb_haB.regs_out0 KS_haB = true. Proof. vm_compute. reflexivity. Qed.
Definition haB_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,:v28S,16v22S,17v21S,19#7???8000B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80Ka+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1P#10000#683000v28#400P#10000#683000v29#1,3_v2#70#8+v28##18+/v28#8#7???8000#80,1,92X#:798<#:832<Y,T,1#:7<14T,:+v28#20T,;v21T,<v22T,=#:791<T,>^#?#??????????????1T,12v28T,13+/v28#8#7???8000T,14+v28#20T,15+v28#60T,18v28Nb+/v28#8#7???807;#?2Nb+/v28#8#7???807:#?2Nb+/v28#8#7???8079#?2Nb+/v28#8#7???8078#?2Nb+/v28#8#7???807?#?3Nb+/v28#8#7???807>#?3Nb+/v28#8#7???807=#?8Nb+/v28#8#7???807<#?8Nb+/v28#8#7???8073#?2Nb+/v28#8#7???8072#?2Nb+/v28#8#7???8071#?2Nb+/v28#8#7???8070#?2Nb+/v28#8#7???8077#?8Nb+/v28#8#7???8076#?8Nb+/v28#8#7???8075#?8Nb+/v28#8#7???8074#?8Nb+/v28#8#7???806;#?2Nb+/v28#8#7???806:#?8Nb+/v28#8#7???8069#?8Nb+/v28#8#7???8068#?8Nb+/v28#8#7???806?#?2Nb+/v28#8#7???806>#?2Nb+/v28#8#7???806=#?2Nb+/v28#8#7???806<#?2Nb+/v28#8#7???8063#?8Nb+/v28#8#7???8062#?8Nb+/v28#8#7???8061#?8Nb+/v28#8#7???8060#?8Nb+/v28#8#7???8067#?8Nb+/v28#8#7???8066#?8Nb+/v28#8#7???8065#?8Nb+/v28#8#7???8064#?8Nb+/v28#8#7???805;#?8Nb+/v28#8#7???805:#?8Nb+/v28#8#7???8059#?8Nb+/v28#8#7???8058#?8Nb+/v28#8#7???805?#?8Nb+/v28#8#7???805>#?8Nb+/v28#8#7???805=#?8Nb+/v28#8#7???805<#?8Nb+/v28#8#7???8053#?8Nb+/v28#8#7???8052#?8Nb+/v28#8#7???8051#?8Nb+/v28#8#7???8050#?8Nb+/v28#8#7???8057#?8Nb+/v28#8#7???8056#?8Nb+/v28#8#7???8055#?8Nb+/v28#8#7???8054#?8Nb+/v28#8#7???804;#?8Nb+/v28#8#7???804:#?8Nb+/v28#8#7???8049#?8Nb+/v28#8#7???8048#?8Nb+/v28#8#7???804?#?8Nb+/v28#8#7???804>#?8Nb+/v28#8#7???804=#?8Nb+/v28#8#7???804<#?8Nb+/v28#8#7???8043#?8Nb+/v28#8#7???8042#?8Nb+/v28#8#7???8041#?8Nb+/v28#8#7???8040#?8Nb+/v28#8#7???8047#?8Nb+/v28#8#7???8046#?8Nb+/v28#8#7???8045#?8Nb+/v28#8#7???8044#?8Nb+/v28#8#7???803;#?8Nb+/v28#8#7???803:#?8Nb+/v28#8#7???8039#?2Nb+/v28#8#7???8038#?2Nb+/v28#8#7???803?#?8Nb+/v28#8#7???803>#?8Nb+/v28#8#7???803=#?8Nb+/v28#8#7???803<#?8Nb+/v28#8#7???8033#?2Nb+/v28#8#7???8032#?2Nb+/v28#8#7???8031#?2Nb+/v28#8#7???8030#?2Nb+/v28#8#7???8037#?2Nb+/v28#8#7???8036#?8Nb+/v28#8#7???8035#?2Nb+/v28#8#7???8034#?2Nb+/v28#8#7???802;#?8Nb+/v28#8#7???802:#?8Nb+/v28#8#7???8029#?8Nb+/v28#8#7???8028#?8Nb+/v28#8#7???802?#?2Nb+/v28#8#7???802>#?2Nb+/v28#8#7???802=#?8Nb+/v28#8#7???802<#?8Nb+/v28#8#7???8023#?8Nb+/v28#8#7???8022#?8Nb+/v28#8#7???8021#?8Nb+/v28#8#7???8020#?8Nb+/v28#8#7???8027#?8Nb+/v28#8#7???8026#?8Nb+/v28#8#7???8025#?8Nb+/v28#8#7???8024#?8Nb+/v28#8#7???801;#?8Nb+/v28#8#7???801:#?8Nb+/v28#8#7???8019#?8Nb+/v28#8#7???8018#?8Nb+/v28#8#7???801?#?8Nb+/v28#8#7???801>#?8Nb+/v28#8#7???801=#?8Nb+/v28#8#7???801<#?8Nb+/v28#8#7???8013#?8Nb+/v28#8#7???8012#?8Nb+/v28#8#7???8011#?8Nb+/v28#8#7???8010#?8Nb+/v28#8#7???8017#?8Nb+/v28#8#7???8016#?8Nb+/v28#8#7???8015#?8Nb+/v28#8#7???8014#?8Nb+/v28#8#7???800;#?2Nb+/v28#8#7???800:#?2Nb+/v28#8#7???8009#?2Nb+/v28#8#7???8008#?2Nb+/v28#8#7???800?#?8Nb+/v28#8#7???800>#?8Nb+/v28#8#7???800=#?8Nb+/v28#8#7???800<#?8Nb+/v28#8#7???8007#?2Nb+/v28#8#7???8006#Nb+/v28#8#7???8005#Nb+/v28#8#7???8004#Nb+/v28#8#7???8003#?1Nb+/v28#8#7???8002#?1Nb+/v28#8#7???8001#?1Nb+/v28#8#7???8000#?1Lb+v28#10#:791<Lb+v28#8#1>8:5Lbv28#41;58:;3Lb_v2#70v28Jb+v28#18#3>8"%pstring.
Lemma haB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_haB] fx R M V haB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_haB] LibSegJb_haB.regs0 LibSegJb_haB.kn0 LibSegJb_haB.BR LibSegJb_haB.PSS LibSegJb_haB.NX0 LibSegJb_haB.F0 686476 LibSegJb_haB.seg_sound_ax fx R M V haB_conc_s. Qed.
End PMBHP1.
