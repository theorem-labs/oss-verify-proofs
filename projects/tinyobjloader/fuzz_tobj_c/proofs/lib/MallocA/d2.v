(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx ag.

(* [comment removed for export] *)
Module F0A_x1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_x1Be"; "XR_1Be"; "XM_1Be"; "REST_1Be"; "XK_1Be"; "sX_1Be"; "XEX_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be"; "q_1Be"; "W_1Be"; "Xf_1Be"; "st_1Be"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "sX_of"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_1Be : list axform := XEX_of Xf_1Be.
Definition XM_1Be : axst := XM_of Xf_1Be.
Definition XK_1Be : axst := XK_of 1 XM_1Be.
Definition REST_1Be : list sobj := REST_of 1 XM_1Be.
Definition XR_1Be : axst := XR_of XK_1Be.
Definition sX_1Be : wsub := ltac2:(tb__ "0|0|
S2aS18S1fS21A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_1Be : ltac2:(tb__ "0|0|
S0S12SbA1S30S20S1dA2S11SbS19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_1Be : ax_X XM_1Be = []. Proof. vmr. Qed.
Lemma OBJS_1Be : ltac2:(tb__ "0|1|
S0S10S1A1S5SaS19A1A1M0S13S1S22S1S24U1A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_1Be : ltac2:(tb__ "0|0|
S0S10S1A1S23S1S1S25S22S1S24U1A1S5SaS19A1A1A3A4S23S1S1S25S14S1S36S13S1S37S1fA1S34A3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_1Be : ltac2:(tb__ "0|1|
S0SbScS19S2fSaS19A1M0S22S1S24U1A1S5G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_1Be : ltac2:(tb__ "0|0|
S0SeS9SaS18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_1Be : ltac2:(tb__ "0|4|
S0S12S17S10S17S3S3A2M0A1M1S10S2A1M2A2M3A1S2dSaS1bA1SaS18A1A2S11G3S16G1G2S14G0S16S3S3S6S32A1S7P18A1A4S15G0A1A3S15S2A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_1Be : ltac2:(tb__ "0|0|
S0SbScS1bSaS18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_1Be : ltac2:(tb__ "0|0|
S0S2bS4SaS18A1A1S4SaS1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_1Be : ltac2:(tb__ "0|0|
S0SeSdS18S35S33S1fS21A3S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_1Be : ltac2:(tb__ "0|0|
S0SeS2eS1cS2cA2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_1Be : ltac2:(tb__ "0|0|
S0SeS39S31S4SaS20A1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_1Be : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_1Be : rcivb REST_1Be = true. Proof. Time vmr. Qed.
Lemma RCELL_1Be : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_1Be : rwrb REST_1Be = true. Proof. vmr. Qed.
Lemma RSHP_1Be : ltac2:(tb__ "0|0|
S0SeS29S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_1Be : ltac2:(tb__ "0|0|
S0S12S2A1S38S2S8SaS20A1A1U0A3S11S2S26S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_1Be : ax_base XM_1Be = base_sv. Proof. vmr. Qed.
End F0A_x1Be.

(* [comment removed for export] *)
Module F0A_xi1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be"; "Xf_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_x1Be.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2cVCST;R1A2S2S2cS32R2A2S4S35S33R2A2S36R2S34A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_1Be : ltac2:(tb__ "0|4|
S31OF_;S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S30Vsegs;R19S24Vsegs;S27U1M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF 1%nat UStopLe QBe Xf_1Be XM_1Be XK_1Be XR_1Be (firstn (nkeep 1) (ss_objs (ax_S XM_1Be))) REST_1Be sX_1Be XEX_1Be AXE_1Be OBJS_1Be EQK_1Be WXR_1Be DXR_1Be NXR_1Be EQR_1Be ENT_1Be SID_1Be RCLS_1Be RCIV_1Be RCELL_1Be RWR_1Be RSHP_1Be FQS_1Be). Qed.
Theorem ef0_exit_1Be : ltac2:(tb__ "0|4|
S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;S24Vsegs;S27U1M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF 1%nat UStopLe QBe Xf_1Be XM_1Be XK_1Be XR_1Be (firstn (nkeep 1) (ss_objs (ax_S XM_1Be))) REST_1Be sX_1Be XEX_1Be AXE_1Be OBJS_1Be EQK_1Be WXR_1Be DXR_1Be NXR_1Be EQR_1Be ENT_1Be SID_1Be RCLS_1Be RCIV_1Be RCELL_1Be RWR_1Be RSHP_1Be FQS_1Be). Qed.
End XI.
End F0A_xi1Be.

(* [comment removed for export] *)
Module F0A_x1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_x1Bf"; "XR_1Bf"; "XM_1Bf"; "REST_1Bf"; "XK_1Bf"; "sX_1Bf"; "XEX_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf"; "q_1Bf"; "W_1Bf"; "Xf_1Bf"; "st_1Bf"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "sX_of"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_1Bf : list axform := XEX_of Xf_1Bf.
Definition XM_1Bf : axst := XM_of Xf_1Bf.
Definition XK_1Bf : axst := XK_of 1 XM_1Bf.
Definition REST_1Bf : list sobj := REST_of 1 XM_1Bf.
Definition XR_1Bf : axst := XR_of XK_1Bf.
Definition sX_1Bf : wsub := ltac2:(tb__ "0|0|
S2aS18S1fS21A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_1Bf : ltac2:(tb__ "0|0|
S0S12SbA1S30S20S1dA2S11SbS19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_1Bf : ax_X XM_1Bf = []. Proof. vmr. Qed.
Lemma OBJS_1Bf : ltac2:(tb__ "0|1|
S0S10S1A1S5SaS19A1A1M0S13S1S22S1S24U1A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_1Bf : ltac2:(tb__ "0|0|
S0S10S1A1S23S1S1S25S22S1S24U1A1S5SaS19A1A1A3A4S23S1S1S25S14S1S36S13S1S37S1fA1S34A3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_1Bf : ltac2:(tb__ "0|1|
S0SbScS19S2fSaS19A1M0S22S1S24U1A1S5G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_1Bf : ltac2:(tb__ "0|0|
S0SeS9SaS18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_1Bf : ltac2:(tb__ "0|4|
S0S12S17S10S17S3S3A2M0A1M1S10S2A1M2A2M3A1S2dSaS1bA1SaS18A1A2S11G3S16G1G2S14G0S16S3S3S6S32A1S7P18A1A4S15G0A1A3S15S2A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_1Bf : ltac2:(tb__ "0|0|
S0SbScS1bSaS18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_1Bf : ltac2:(tb__ "0|0|
S0S2bS4SaS18A1A1S4SaS1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_1Bf : ltac2:(tb__ "0|0|
S0SeSdS18S35S33S1fS21A3S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_1Bf : ltac2:(tb__ "0|0|
S0SeS2eS1cS2cA2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_1Bf : ltac2:(tb__ "0|0|
S0SeS39S31S4SaS20A1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_1Bf : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_1Bf : rcivb REST_1Bf = true. Proof. Time vmr. Qed.
Lemma RCELL_1Bf : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_1Bf : rwrb REST_1Bf = true. Proof. vmr. Qed.
Lemma RSHP_1Bf : ltac2:(tb__ "0|0|
S0SeS29S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_1Bf : ltac2:(tb__ "0|0|
S0S12S2A1S38S2S8SaS20A1A1U0A3S11S2S26S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_1Bf : ax_base XM_1Bf = base_sv. Proof. vmr. Qed.
End F0A_x1Bf.

(* [comment removed for export] *)
Module F0A_xi1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf"; "Xf_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_x1Bf.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2cVCST;R1A2S2S2cS32R2A2S4S35S33R2A2S36R2S34A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_1Bf : ltac2:(tb__ "0|4|
S31OF_;S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S30Vsegs;R19S24Vsegs;S27U1M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF 1%nat UStopLe QBf Xf_1Bf XM_1Bf XK_1Bf XR_1Bf (firstn (nkeep 1) (ss_objs (ax_S XM_1Bf))) REST_1Bf sX_1Bf XEX_1Bf AXE_1Bf OBJS_1Bf EQK_1Bf WXR_1Bf DXR_1Bf NXR_1Bf EQR_1Bf ENT_1Bf SID_1Bf RCLS_1Bf RCIV_1Bf RCELL_1Bf RWR_1Bf RSHP_1Bf FQS_1Bf). Qed.
Theorem ef0_exit_1Bf : ltac2:(tb__ "0|4|
S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;S24Vsegs;S27U1M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF 1%nat UStopLe QBf Xf_1Bf XM_1Bf XK_1Bf XR_1Bf (firstn (nkeep 1) (ss_objs (ax_S XM_1Bf))) REST_1Bf sX_1Bf XEX_1Bf AXE_1Bf OBJS_1Bf EQK_1Bf WXR_1Bf DXR_1Bf NXR_1Bf EQR_1Bf ENT_1Bf SID_1Bf RCLS_1Bf RCIV_1Bf RCELL_1Bf RWR_1Bf RSHP_1Bf FQS_1Bf). Qed.
End XI.
End F0A_xi1Bf.

(* [comment removed for export] *)
Module F0A_x2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_x2A"; "XR_2A"; "XM_2A"; "REST_2A"; "XK_2A"; "sX_2A"; "XEX_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A"; "q_2A"; "Xf_2A"; "W_2A"; "st_2A"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_2A : list axform := XEX_of Xf_2A.
Definition XM_2A : axst := XM_of Xf_2A.
Definition XK_2A : axst := XK_of 2 XM_2A.
Definition REST_2A : list sobj := REST_of 2 XM_2A.
Definition XR_2A : axst := XR_of XK_2A.
Definition sX_2A : wsub := sX_of XR_2A W_2A st_2A.

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_2A : ltac2:(tb__ "0|0|
S0S12SbA1S2fS1fS1dA2S11SbS19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_2A : ax_X XM_2A = []. Proof. vmr. Qed.
Lemma OBJS_2A : ltac2:(tb__ "0|1|
S0S10S1A1S5SaS19A1A1M0S13S1S22S1S24U2A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_2A : ltac2:(tb__ "0|0|
S0S10S1A1S23S1S1S25S22S1S24U2A1S5SaS19A1A1A3A4S23S1S1S25S14S1S35S13S1S36S20A1S33A3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_2A : ltac2:(tb__ "0|1|
S0SbScS19S2eSaS19A1M0S22S1S24U2A1S5G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_2A : ltac2:(tb__ "0|0|
S0SeS9SaS18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_2A : ltac2:(tb__ "0|4|
S0S12S17S10S17S3S3A2M0A1M1S10S2A1M2A2M3A1S2cSaS1bA1SaS18A1A2S11G3S16G1G2S14G0S16S3S3S6S31A1S7P18A1A4S15G0A1A3S15S2A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_2A : ltac2:(tb__ "0|0|
S0SbScS1bSaS18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_2A : ltac2:(tb__ "0|0|
S0S2aS4SaS18A1A1S4SaS1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_2A : ltac2:(tb__ "0|0|
S0SeSdS18S34S32S20S21A3S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_2A : ltac2:(tb__ "0|0|
S0SeS2dS1cS2bA2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_2A : ltac2:(tb__ "0|0|
S0SeS38S30S4SaS1fA1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_2A : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_2A : rcivb REST_2A = true. Proof. Time vmr. Qed.
Lemma RCELL_2A : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_2A : rwrb REST_2A = true. Proof. vmr. Qed.
Lemma RSHP_2A : ltac2:(tb__ "0|0|
S0SeS29S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_2A : ltac2:(tb__ "0|0|
S0S12S2A1S37S2S8SaS1fA1A1U0A3S11S2S26S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_2A : ax_base XM_2A = base_sv. Proof. vmr. Qed.
End F0A_x2A.

(* [comment removed for export] *)
Module F0A_xi2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A"; "Xf_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_x2A.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2cVCST;R1A2S2S2cS32R2A2S4S35S33R2A2S36R2S34A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_2A : ltac2:(tb__ "0|4|
S31OF_;S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S30Vsegs;R19S24Vsegs;S27U2M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF 2%nat UStopLe QA Xf_2A XM_2A XK_2A XR_2A (firstn (nkeep 2) (ss_objs (ax_S XM_2A))) REST_2A sX_2A XEX_2A AXE_2A OBJS_2A EQK_2A WXR_2A DXR_2A NXR_2A EQR_2A ENT_2A SID_2A RCLS_2A RCIV_2A RCELL_2A RWR_2A RSHP_2A FQS_2A). Qed.
Theorem ef0_exit_2A : ltac2:(tb__ "0|4|
S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;S24Vsegs;S27U2M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF 2%nat UStopLe QA Xf_2A XM_2A XK_2A XR_2A (firstn (nkeep 2) (ss_objs (ax_S XM_2A))) REST_2A sX_2A XEX_2A AXE_2A OBJS_2A EQK_2A WXR_2A DXR_2A NXR_2A EQR_2A ENT_2A SID_2A RCLS_2A RCIV_2A RCELL_2A RWR_2A RSHP_2A FQS_2A). Qed.
End XI.
End F0A_xi2A.

