(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.

(* [comment removed for export] *)
Module F0T_xTA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xTA"; "XR_TA"; "XM_TA"; "REST_TA"; "XK_TA"; "sX_TA"; "XEX_TA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA"; "q_TA"; "Xf_TA"; "W_TA"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "stack_win"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_TA : list axform := XEX_of Xf_TA.
Definition XM_TA : axst := XM_of Xf_TA.
Definition XK_TA : axst := XK_of 0 XM_TA.
Definition REST_TA : list sobj := REST_of 0 XM_TA.
Definition XR_TA : axst := XR_of XK_TA.
Definition sX_TA : wsub := ltac2:(tb__ "0|0|
S31S29S1S18A1S1S2eS2aA1A1A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_TA : ltac2:(tb__ "0|0|
S0S12S2A1S34S1fS1dA2S11S2S19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_TA : ax_X XM_TA = []. Proof. vmr. Qed.
Lemma OBJS_TA : ltac2:(tb__ "0|1|
S0S10S5A1S9S1S19A1A1M0S13S5S21S5S23U0A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_TA : ltac2:(tb__ "0|0|
S0S10S5A1S22S5S5S24S21S5S23U0A1S9S1S19A1A1A3A4S22S5S5S24S14S5S2cS13S5S2dS20A1S2bA3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_TA : ltac2:(tb__ "0|1|
S0S2S3S19S33S1S19A1M0S21S5S23U0A1S9G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_TA : ltac2:(tb__ "0|0|
S0SeSdS1S18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_TA : ltac2:(tb__ "0|4|
S0S12S17S10S17S7S7A2M0A1M1S10S6A1M2A2M3A1S30S1S1bA1S1S18A1A2S11G3S16G1G2S14G0S16S7S7SaS36A1SbP18A1A4S15G0A1A3S15S6A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_TA : ltac2:(tb__ "0|0|
S0S2S3S1bS1S18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_TA : ltac2:(tb__ "0|0|
S0S2fS8S1S18A1A1S8S1S1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_TA : ltac2:(tb__ "0|0|
S0SeS4S18S2eS2aA1S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_TA : ltac2:(tb__ "0|0|
S0SeS32S1cS29A2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_TA : ltac2:(tb__ "0|0|
S0SeS38S35S8S1S1fA1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_TA : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_TA : rcivb REST_TA = true. Proof. Time vmr. Qed.
Lemma RCELL_TA : ltac2:(tb__ "0|0|
S0SeS26S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_TA : rwrb REST_TA = true. Proof. vmr. Qed.
Lemma RSHP_TA : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_TA : ltac2:(tb__ "0|0|
S0S12S6A1S37S6ScS1S1fA1A1U0A3S11S6S25S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_TA : ax_base XM_TA = base_sv. Proof. vmr. Qed.
End F0T_xTA.

(* [comment removed for export] *)
Module F0T_xiTA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA"; "Xf_TA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2S2bS31R2A2S4S34S32R2A2S35R2S33A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_TA : ltac2:(tb__ "0|3|
S30OF_;S16S26S5ScS1aQ40M0A1A1M1S0S0S0S14S0OF_;S1S0S19G0S6R7PcA2A2R5A3S1S0S19G0S6R8PdA2A2R5A3S2dS8S0S0A2S7S0S0R7R6A4S18RbA1A3S1dR8R7A2S1S9S17RdA1SeA3S15S21ReA2S20RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S23A3S0S2S28VCST;R12R1A3S29VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S16S5S5G1S1fR16R4A2S2cRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;R19S1cVsegs;S1eU0S27SbR6R17R5A6S22R4R3A5S11Vsegs;S1bR16R15SaS8SfS10A2M2S7SfS10S2aS24A1S25VAInv;VCST;VXGL;R18R17A5A4SdG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF QA Xf_TA XM_TA XK_TA XR_TA (firstn (nkeep 0) (ss_objs (ax_S XM_TA))) REST_TA sX_TA XEX_TA AXE_TA OBJS_TA EQK_TA WXR_TA DXR_TA NXR_TA EQR_TA ENT_TA SID_TA RCLS_TA RCIV_TA RCELL_TA RWR_TA RSHP_TA FQS_TA). Qed.
Theorem ef0_exit_TA : ltac2:(tb__ "0|3|
S16S26S5ScS1aQ40M0A1A1M1S0S0S0S14S0OF_;S1S0S19G0S6R7PcA2A2R5A3S1S0S19G0S6R8PdA2A2R5A3S2dS8S0S0A2S7S0S0R7R6A4S18RbA1A3S1dR8R7A2S1S9S17RdA1SeA3S15S21ReA2S20RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S23A3S0S2S28VCST;R12R1A3S29VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S16S5S5G1S1fR16R4A2S2cRfS12R17R15R13R12R11R10A6R4A3S2eVsegs;S1cVsegs;S1eU0S27SbR6R17R5A6S22R4R3A5S11Vsegs;S1bR16R15SaS8SfS10A2M2S7SfS10S2aS24A1S25VAInv;VCST;VXGL;R18R17A5A4SdG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF QA Xf_TA XM_TA XK_TA XR_TA (firstn (nkeep 0) (ss_objs (ax_S XM_TA))) REST_TA sX_TA XEX_TA AXE_TA OBJS_TA EQK_TA WXR_TA DXR_TA NXR_TA EQR_TA ENT_TA SID_TA RCLS_TA RCIV_TA RCELL_TA RWR_TA RSHP_TA FQS_TA). Qed.
End XI.
End F0T_xiTA.

(* [comment removed for export] *)
Module F0T_xTBe.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xTBe"; "XR_TBe"; "XM_TBe"; "REST_TBe"; "XK_TBe"; "sX_TBe"; "XEX_TBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "q_TBe"; "Xf_TBe"; "W_TBe"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "stack_win"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_TBe : list axform := XEX_of Xf_TBe.
Definition XM_TBe : axst := XM_of Xf_TBe.
Definition XK_TBe : axst := XK_of 0 XM_TBe.
Definition REST_TBe : list sobj := REST_of 0 XM_TBe.
Definition XR_TBe : axst := XR_of XK_TBe.
Definition sX_TBe : wsub := ltac2:(tb__ "0|0|
S31S29S1S18A1S1S2eS2aA1A1A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_TBe : ltac2:(tb__ "0|0|
S0S12S2A1S34S1fS1dA2S11S2S19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_TBe : ax_X XM_TBe = []. Proof. vmr. Qed.
Lemma OBJS_TBe : ltac2:(tb__ "0|1|
S0S10S5A1S9S1S19A1A1M0S13S5S21S5S23U0A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_TBe : ltac2:(tb__ "0|0|
S0S10S5A1S22S5S5S24S21S5S23U0A1S9S1S19A1A1A3A4S22S5S5S24S14S5S2cS13S5S2dS20A1S2bA3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_TBe : ltac2:(tb__ "0|1|
S0S2S3S19S33S1S19A1M0S21S5S23U0A1S9G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_TBe : ltac2:(tb__ "0|0|
S0SeSdS1S18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_TBe : ltac2:(tb__ "0|4|
S0S12S17S10S17S7S7A2M0A1M1S10S6A1M2A2M3A1S30S1S1bA1S1S18A1A2S11G3S16G1G2S14G0S16S7S7SaS36A1SbP18A1A4S15G0A1A3S15S6A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_TBe : ltac2:(tb__ "0|0|
S0S2S3S1bS1S18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_TBe : ltac2:(tb__ "0|0|
S0S2fS8S1S18A1A1S8S1S1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_TBe : ltac2:(tb__ "0|0|
S0SeS4S18S2eS2aA1S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_TBe : ltac2:(tb__ "0|0|
S0SeS32S1cS29A2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_TBe : ltac2:(tb__ "0|0|
S0SeS38S35S8S1S1fA1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_TBe : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_TBe : rcivb REST_TBe = true. Proof. Time vmr. Qed.
Lemma RCELL_TBe : ltac2:(tb__ "0|0|
S0SeS26S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_TBe : rwrb REST_TBe = true. Proof. vmr. Qed.
Lemma RSHP_TBe : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_TBe : ltac2:(tb__ "0|0|
S0S12S6A1S37S6ScS1S1fA1A1U0A3S11S6S25S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_TBe : ax_base XM_TBe = base_sv. Proof. vmr. Qed.
End F0T_xTBe.

(* [comment removed for export] *)
Module F0T_xiTBe.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "Xf_TBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xTBe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2S2bS31R2A2S4S34S32R2A2S35R2S33A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_TBe : ltac2:(tb__ "0|3|
S30OF_;S16S26S5ScS1aQ40M0A1A1M1S0S0S0S14S0OF_;S1S0S19G0S6R7PcA2A2R5A3S1S0S19G0S6R8PdA2A2R5A3S2dS8S0S0A2S7S0S0R7R6A4S18RbA1A3S1dR8R7A2S1S9S17RdA1SeA3S15S21ReA2S20RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S23A3S0S2S28VCST;R12R1A3S29VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S16S5S5G1S1fR16R4A2S2cRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;R19S1cVsegs;S1eU0S27SbR6R17R5A6S22R4R3A5S11Vsegs;S1bR16R15SaS8SfS10A2M2S7SfS10S2aS24A1S25VAInv;VCST;VXGL;R18R17A5A4SdG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF QBe Xf_TBe XM_TBe XK_TBe XR_TBe (firstn (nkeep 0) (ss_objs (ax_S XM_TBe))) REST_TBe sX_TBe XEX_TBe AXE_TBe OBJS_TBe EQK_TBe WXR_TBe DXR_TBe NXR_TBe EQR_TBe ENT_TBe SID_TBe RCLS_TBe RCIV_TBe RCELL_TBe RWR_TBe RSHP_TBe FQS_TBe). Qed.
Theorem ef0_exit_TBe : ltac2:(tb__ "0|3|
S16S26S5ScS1aQ40M0A1A1M1S0S0S0S14S0OF_;S1S0S19G0S6R7PcA2A2R5A3S1S0S19G0S6R8PdA2A2R5A3S2dS8S0S0A2S7S0S0R7R6A4S18RbA1A3S1dR8R7A2S1S9S17RdA1SeA3S15S21ReA2S20RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S23A3S0S2S28VCST;R12R1A3S29VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S16S5S5G1S1fR16R4A2S2cRfS12R17R15R13R12R11R10A6R4A3S2eVsegs;S1cVsegs;S1eU0S27SbR6R17R5A6S22R4R3A5S11Vsegs;S1bR16R15SaS8SfS10A2M2S7SfS10S2aS24A1S25VAInv;VCST;VXGL;R18R17A5A4SdG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF QBe Xf_TBe XM_TBe XK_TBe XR_TBe (firstn (nkeep 0) (ss_objs (ax_S XM_TBe))) REST_TBe sX_TBe XEX_TBe AXE_TBe OBJS_TBe EQK_TBe WXR_TBe DXR_TBe NXR_TBe EQR_TBe ENT_TBe SID_TBe RCLS_TBe RCIV_TBe RCELL_TBe RWR_TBe RSHP_TBe FQS_TBe). Qed.
End XI.
End F0T_xiTBe.

(* [comment removed for export] *)
Module F0T_xTBf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xTBf"; "XR_TBf"; "XM_TBf"; "REST_TBf"; "XK_TBf"; "sX_TBf"; "XEX_TBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "q_TBf"; "Xf_TBf"; "W_TBf"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "stack_win"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_TBf : list axform := XEX_of Xf_TBf.
Definition XM_TBf : axst := XM_of Xf_TBf.
Definition XK_TBf : axst := XK_of 0 XM_TBf.
Definition REST_TBf : list sobj := REST_of 0 XM_TBf.
Definition XR_TBf : axst := XR_of XK_TBf.
Definition sX_TBf : wsub := ltac2:(tb__ "0|0|
S31S29S1S18A1S1S2eS2aA1A1A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_TBf : ltac2:(tb__ "0|0|
S0S12S2A1S34S1fS1dA2S11S2S19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_TBf : ax_X XM_TBf = []. Proof. vmr. Qed.
Lemma OBJS_TBf : ltac2:(tb__ "0|1|
S0S10S5A1S9S1S19A1A1M0S13S5S21S5S23U0A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_TBf : ltac2:(tb__ "0|0|
S0S10S5A1S22S5S5S24S21S5S23U0A1S9S1S19A1A1A3A4S22S5S5S24S14S5S2cS13S5S2dS20A1S2bA3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_TBf : ltac2:(tb__ "0|1|
S0S2S3S19S33S1S19A1M0S21S5S23U0A1S9G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_TBf : ltac2:(tb__ "0|0|
S0SeSdS1S18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_TBf : ltac2:(tb__ "0|4|
S0S12S17S10S17S7S7A2M0A1M1S10S6A1M2A2M3A1S30S1S1bA1S1S18A1A2S11G3S16G1G2S14G0S16S7S7SaS36A1SbP18A1A4S15G0A1A3S15S6A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_TBf : ltac2:(tb__ "0|0|
S0S2S3S1bS1S18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_TBf : ltac2:(tb__ "0|0|
S0S2fS8S1S18A1A1S8S1S1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_TBf : ltac2:(tb__ "0|0|
S0SeS4S18S2eS2aA1S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_TBf : ltac2:(tb__ "0|0|
S0SeS32S1cS29A2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_TBf : ltac2:(tb__ "0|0|
S0SeS38S35S8S1S1fA1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_TBf : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_TBf : rcivb REST_TBf = true. Proof. Time vmr. Qed.
Lemma RCELL_TBf : ltac2:(tb__ "0|0|
S0SeS26S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_TBf : rwrb REST_TBf = true. Proof. vmr. Qed.
Lemma RSHP_TBf : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_TBf : ltac2:(tb__ "0|0|
S0S12S6A1S37S6ScS1S1fA1A1U0A3S11S6S25S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_TBf : ax_base XM_TBf = base_sv. Proof. vmr. Qed.
End F0T_xTBf.

(* [comment removed for export] *)
Module F0T_xiTBf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "Xf_TBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xTBf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2S2bS31R2A2S4S34S32R2A2S35R2S33A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_TBf : ltac2:(tb__ "0|3|
S30OF_;S16S26S5ScS1aQ40M0A1A1M1S0S0S0S14S0OF_;S1S0S19G0S6R7PcA2A2R5A3S1S0S19G0S6R8PdA2A2R5A3S2dS8S0S0A2S7S0S0R7R6A4S18RbA1A3S1dR8R7A2S1S9S17RdA1SeA3S15S21ReA2S20RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S23A3S0S2S28VCST;R12R1A3S29VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S16S5S5G1S1fR16R4A2S2cRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;R19S1cVsegs;S1eU0S27SbR6R17R5A6S22R4R3A5S11Vsegs;S1bR16R15SaS8SfS10A2M2S7SfS10S2aS24A1S25VAInv;VCST;VXGL;R18R17A5A4SdG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF QBf Xf_TBf XM_TBf XK_TBf XR_TBf (firstn (nkeep 0) (ss_objs (ax_S XM_TBf))) REST_TBf sX_TBf XEX_TBf AXE_TBf OBJS_TBf EQK_TBf WXR_TBf DXR_TBf NXR_TBf EQR_TBf ENT_TBf SID_TBf RCLS_TBf RCIV_TBf RCELL_TBf RWR_TBf RSHP_TBf FQS_TBf). Qed.
Theorem ef0_exit_TBf : ltac2:(tb__ "0|3|
S16S26S5ScS1aQ40M0A1A1M1S0S0S0S14S0OF_;S1S0S19G0S6R7PcA2A2R5A3S1S0S19G0S6R8PdA2A2R5A3S2dS8S0S0A2S7S0S0R7R6A4S18RbA1A3S1dR8R7A2S1S9S17RdA1SeA3S15S21ReA2S20RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S23A3S0S2S28VCST;R12R1A3S29VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S16S5S5G1S1fR16R4A2S2cRfS12R17R15R13R12R11R10A6R4A3S2eVsegs;S1cVsegs;S1eU0S27SbR6R17R5A6S22R4R3A5S11Vsegs;S1bR16R15SaS8SfS10A2M2S7SfS10S2aS24A1S25VAInv;VCST;VXGL;R18R17A5A4SdG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF QBf Xf_TBf XM_TBf XK_TBf XR_TBf (firstn (nkeep 0) (ss_objs (ax_S XM_TBf))) REST_TBf sX_TBf XEX_TBf AXE_TBf OBJS_TBf EQK_TBf WXR_TBf DXR_TBf NXR_TBf EQR_TBf ENT_TBf SID_TBf RCLS_TBf RCIV_TBf RCELL_TBf RWR_TBf RSHP_TBf FQS_TBf). Qed.
End XI.
End F0T_xiTBf.

