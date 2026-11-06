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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib F0A_exit.

(* [comment removed for export] *)
Module F0A_x2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_x2A"; "XR_2A"; "XM_2A"; "REST_2A"; "XK_2A"; "sX_2A"; "XEX_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "q_2A"; "Xf_2A"; "W_2A"; "st_2A"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "Xf_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_x2A.
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

(* [comment removed for export] *)
Module F0A_x2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_x2Be"; "XR_2Be"; "XM_2Be"; "REST_2Be"; "XK_2Be"; "sX_2Be"; "XEX_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "q_2Be"; "W_2Be"; "Xf_2Be"; "st_2Be"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "sX_of"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_2Be : list axform := XEX_of Xf_2Be.
Definition XM_2Be : axst := XM_of Xf_2Be.
Definition XK_2Be : axst := XK_of 2 XM_2Be.
Definition REST_2Be : list sobj := REST_of 2 XM_2Be.
Definition XR_2Be : axst := XR_of XK_2Be.
Definition sX_2Be : wsub := ltac2:(tb__ "0|0|
S2aS18S1fS21A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_2Be : ltac2:(tb__ "0|0|
S0S12SbA1S30S20S1dA2S11SbS19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_2Be : ax_X XM_2Be = []. Proof. vmr. Qed.
Lemma OBJS_2Be : ltac2:(tb__ "0|1|
S0S10S1A1S5SaS19A1A1M0S13S1S22S1S24U2A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_2Be : ltac2:(tb__ "0|0|
S0S10S1A1S23S1S1S25S22S1S24U2A1S5SaS19A1A1A3A4S23S1S1S25S14S1S36S13S1S37S1fA1S34A3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_2Be : ltac2:(tb__ "0|1|
S0SbScS19S2fSaS19A1M0S22S1S24U2A1S5G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_2Be : ltac2:(tb__ "0|0|
S0SeS9SaS18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_2Be : ltac2:(tb__ "0|4|
S0S12S17S10S17S3S3A2M0A1M1S10S2A1M2A2M3A1S2dSaS1bA1SaS18A1A2S11G3S16G1G2S14G0S16S3S3S6S32A1S7P18A1A4S15G0A1A3S15S2A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_2Be : ltac2:(tb__ "0|0|
S0SbScS1bSaS18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_2Be : ltac2:(tb__ "0|0|
S0S2bS4SaS18A1A1S4SaS1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_2Be : ltac2:(tb__ "0|0|
S0SeSdS18S35S33S1fS21A3S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_2Be : ltac2:(tb__ "0|0|
S0SeS2eS1cS2cA2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_2Be : ltac2:(tb__ "0|0|
S0SeS39S31S4SaS20A1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_2Be : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_2Be : rcivb REST_2Be = true. Proof. Time vmr. Qed.
Lemma RCELL_2Be : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_2Be : rwrb REST_2Be = true. Proof. vmr. Qed.
Lemma RSHP_2Be : ltac2:(tb__ "0|0|
S0SeS29S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_2Be : ltac2:(tb__ "0|0|
S0S12S2A1S38S2S8SaS20A1A1U0A3S11S2S26S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_2Be : ax_base XM_2Be = base_sv. Proof. vmr. Qed.
End F0A_x2Be.

(* [comment removed for export] *)
Module F0A_xi2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "Xf_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_x2Be.
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

Theorem f0_exit_2Be : ltac2:(tb__ "0|4|
S31OF_;S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S30Vsegs;R19S24Vsegs;S27U2M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF 2%nat UStopLe QBe Xf_2Be XM_2Be XK_2Be XR_2Be (firstn (nkeep 2) (ss_objs (ax_S XM_2Be))) REST_2Be sX_2Be XEX_2Be AXE_2Be OBJS_2Be EQK_2Be WXR_2Be DXR_2Be NXR_2Be EQR_2Be ENT_2Be SID_2Be RCLS_2Be RCIV_2Be RCELL_2Be RWR_2Be RSHP_2Be FQS_2Be). Qed.
Theorem ef0_exit_2Be : ltac2:(tb__ "0|4|
S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;S24Vsegs;S27U2M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF 2%nat UStopLe QBe Xf_2Be XM_2Be XK_2Be XR_2Be (firstn (nkeep 2) (ss_objs (ax_S XM_2Be))) REST_2Be sX_2Be XEX_2Be AXE_2Be OBJS_2Be EQK_2Be WXR_2Be DXR_2Be NXR_2Be EQR_2Be ENT_2Be SID_2Be RCLS_2Be RCIV_2Be RCELL_2Be RWR_2Be RSHP_2Be FQS_2Be). Qed.
End XI.
End F0A_xi2Be.

(* [comment removed for export] *)
Module F0A_x2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_x2Bf"; "XR_2Bf"; "XM_2Bf"; "REST_2Bf"; "XK_2Bf"; "sX_2Bf"; "XEX_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "q_2Bf"; "W_2Bf"; "Xf_2Bf"; "st_2Bf"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "sX_of"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_2Bf : list axform := XEX_of Xf_2Bf.
Definition XM_2Bf : axst := XM_of Xf_2Bf.
Definition XK_2Bf : axst := XK_of 2 XM_2Bf.
Definition REST_2Bf : list sobj := REST_of 2 XM_2Bf.
Definition XR_2Bf : axst := XR_of XK_2Bf.
Definition sX_2Bf : wsub := ltac2:(tb__ "0|0|
S2aS18S1fS21A3").

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_2Bf : ltac2:(tb__ "0|0|
S0S12SbA1S30S20S1dA2S11SbS19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_2Bf : ax_X XM_2Bf = []. Proof. vmr. Qed.
Lemma OBJS_2Bf : ltac2:(tb__ "0|1|
S0S10S1A1S5SaS19A1A1M0S13S1S22S1S24U2A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_2Bf : ltac2:(tb__ "0|0|
S0S10S1A1S23S1S1S25S22S1S24U2A1S5SaS19A1A1A3A4S23S1S1S25S14S1S36S13S1S37S1fA1S34A3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_2Bf : ltac2:(tb__ "0|1|
S0SbScS19S2fSaS19A1M0S22S1S24U2A1S5G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_2Bf : ltac2:(tb__ "0|0|
S0SeS9SaS18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_2Bf : ltac2:(tb__ "0|4|
S0S12S17S10S17S3S3A2M0A1M1S10S2A1M2A2M3A1S2dSaS1bA1SaS18A1A2S11G3S16G1G2S14G0S16S3S3S6S32A1S7P18A1A4S15G0A1A3S15S2A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_2Bf : ltac2:(tb__ "0|0|
S0SbScS1bSaS18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_2Bf : ltac2:(tb__ "0|0|
S0S2bS4SaS18A1A1S4SaS1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_2Bf : ltac2:(tb__ "0|0|
S0SeSdS18S35S33S1fS21A3S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_2Bf : ltac2:(tb__ "0|0|
S0SeS2eS1cS2cA2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_2Bf : ltac2:(tb__ "0|0|
S0SeS39S31S4SaS20A1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_2Bf : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_2Bf : rcivb REST_2Bf = true. Proof. Time vmr. Qed.
Lemma RCELL_2Bf : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_2Bf : rwrb REST_2Bf = true. Proof. vmr. Qed.
Lemma RSHP_2Bf : ltac2:(tb__ "0|0|
S0SeS29S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_2Bf : ltac2:(tb__ "0|0|
S0S12S2A1S38S2S8SaS20A1A1U0A3S11S2S26S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_2Bf : ax_base XM_2Bf = base_sv. Proof. vmr. Qed.
End F0A_x2Bf.

(* [comment removed for export] *)
Module F0A_xi2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "Xf_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_x2Bf.
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

Theorem f0_exit_2Bf : ltac2:(tb__ "0|4|
S31OF_;S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S30Vsegs;R19S24Vsegs;S27U2M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF 2%nat UStopLe QBf Xf_2Bf XM_2Bf XK_2Bf XR_2Bf (firstn (nkeep 2) (ss_objs (ax_S XM_2Bf))) REST_2Bf sX_2Bf XEX_2Bf AXE_2Bf OBJS_2Bf EQK_2Bf WXR_2Bf DXR_2Bf NXR_2Bf EQR_2Bf ENT_2Bf SID_2Bf RCLS_2Bf RCIV_2Bf RCELL_2Bf RWR_2Bf RSHP_2Bf FQS_2Bf). Qed.
Theorem ef0_exit_2Bf : ltac2:(tb__ "0|4|
S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;S24Vsegs;S27U2M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF 2%nat UStopLe QBf Xf_2Bf XM_2Bf XK_2Bf XR_2Bf (firstn (nkeep 2) (ss_objs (ax_S XM_2Bf))) REST_2Bf sX_2Bf XEX_2Bf AXE_2Bf OBJS_2Bf EQK_2Bf WXR_2Bf DXR_2Bf NXR_2Bf EQR_2Bf ENT_2Bf SID_2Bf RCLS_2Bf RCIV_2Bf RCELL_2Bf RWR_2Bf RSHP_2Bf FQS_2Bf). Qed.
End XI.
End F0A_xi2Bf.

