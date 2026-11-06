(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.

(* [comment removed for export] *)
Module F0A_qL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2A"; "Cd_L2A"; "XMd_L2A"; "RQ_L2A"; "XR2_L2A"; "sQ_L2A"; "RESTd_L2A"; "TQ_L2A"; "TQr_L2A"; "XKd_L2A"; "XM2_L2A"; "KEPTd_L2A"; "Xf2_L2A"; "run7_L2A"; "run7r_L2A"; "nkd_L2A"; "sX2_L2A"; "Edr_nf_L2A"; "XEX2_L2A"; "XEXd_L2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2A.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L2A : axst := Eval vm_compute in Edr_L2A.
Lemma Edr_eq_L2A : Edr_L2A = Edr_nf_L2A. Proof. vm_cast_no_check (eq_refl Edr_nf_L2A). Qed.

Definition XEXd_L2A : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L2A))].
Definition XMd_L2A : axst := Eval vm_compute in (axf Edr_nf_L2A XEXd_L2A).
Lemma AXEd_L2A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L2A)). Qed.
Definition nkd_L2A : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L2A) + 2 + 2)%nat.
Definition KEPTd_L2A : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L2A : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L2A : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L2A : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L2A : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L2A : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L2A : rcivb RESTd_L2A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L2A : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L2A : rwrb RESTd_L2A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L2A : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L2A : axst := Eval vm_compute in (ax_with_facts XKd_L2A (ss_facts (ax_S XKd_L2A) ++ [F_cne])).
Lemma ECd_L2A : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L2A). Qed.
Lemma FBCd_L2A : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L2A : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L2A) (ax_S PreQ3)).
Definition RQ_L2A : list sobj := Eval vm_compute in (optR (entails_frA Cd_L2A PreQ3 sQ_L2A)).
Lemma HEQ_L2A : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L2A)). Qed.
Lemma HCK_L2A : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L2A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L2A PreQ3 PostQ3 Cd_L2A RQ_L2A) (ss_facts (ax_S Cd_L2A))).
Lemma HTQ_L2A : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L2A). Qed.
Lemma QCHK_L2A : ltac2:(tb__ "0|0|
S0S7S61U2S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L2A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L2A PreQ3 PostQ3r Cd_L2A RQ_L2A) (ss_facts (ax_S Cd_L2A))).
Lemma HTQr_L2A : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L2A). Qed.
Lemma QCHKr_L2A : ltac2:(tb__ "0|0|
S0S7S61U2S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L2A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L2A).
Lemma RUN7_L2A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L2A). Qed.
Definition Xf2_L2A : axst := Eval vm_compute in (leaf 0 run7_L2A).
Lemma L7_L2A : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L2A)]. Qed.
Lemma NX7_L2A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L2A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L2A).
Lemma RUN7r_L2A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L2A). Qed.
Lemma L7r_L2A : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L2A)]. Qed.
Lemma NX7r_L2A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L2A : list axform := Eval vm_compute in (XEX_of Xf2_L2A).
Definition XM2_L2A : axst := Eval vm_compute in (axf Xf2_L2A XEX2_L2A).
Lemma AXE2_L2A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L2A)). Qed.
Definition XR2_L2A : axst := Eval vm_compute in (XR_of XM2_L2A).
Definition sX2_L2A : wsub := Eval vm_compute in (sX_of XR2_L2A (Wcan 2) UStopLe).
Lemma WXR2_L2A : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L2A : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L2A : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L2A))). Qed.
Lemma EQR2_L2A : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L2A). Qed.
Lemma ENT2_L2A : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU2A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L2A : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL2A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L2A (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U2M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L2A (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U2M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L2A : drain_stmt_L2A Edr_L2A.
Proof.
  rewrite Edr_eq_L2A.
  exact (f0_drain 2%nat QA CST XGL HCST HXGL HCSTQ Cd_L2A TQ_L2A TQr_L2A sQ_L2A RQ_L2A HEQ_L2A HCK_L2A HTQ_L2A HTQr_L2A QCHK_L2A QCHKr_L2A Xf2_L2A XM2_L2A XR2_L2A XEX2_L2A sX2_L2A run7_L2A
           NX7_L2A RUN7_L2A L7_L2A run7r_L2A NX7r_L2A RUN7r_L2A L7r_L2A AXE2_L2A WXR2_L2A DXR2_L2A NXR2_L2A EQR2_L2A ENT2_L2A SID2_L2A HCSTF Edr_nf_L2A XMd_L2A XKd_L2A KEPTd_L2A RESTd_L2A XEXd_L2A
           AXEd_L2A OBJSd_L2A EQKd_L2A RCLSd_L2A RCIVd_L2A RCELLd_L2A RWRd_L2A RSHPd_L2A ECd_L2A FBCd_L2A).
Qed.
Theorem ef0_drain_L2A : edrain_stmt_L2A Edr_L2A.
Proof.
  rewrite Edr_eq_L2A.
  exact (ef0_drain 2%nat QA CST XGL HCST HXGL HCSTQ Cd_L2A TQ_L2A TQr_L2A sQ_L2A RQ_L2A HEQ_L2A HCK_L2A HTQ_L2A HTQr_L2A QCHK_L2A QCHKr_L2A Xf2_L2A XM2_L2A XR2_L2A XEX2_L2A sX2_L2A run7_L2A
           NX7_L2A RUN7_L2A L7_L2A run7r_L2A NX7r_L2A RUN7r_L2A L7r_L2A AXE2_L2A WXR2_L2A DXR2_L2A NXR2_L2A EQR2_L2A ENT2_L2A SID2_L2A HCSTF Edr_nf_L2A XMd_L2A XKd_L2A KEPTd_L2A RESTd_L2A XEXd_L2A
           AXEd_L2A OBJSd_L2A EQKd_L2A RCLSd_L2A RCIVd_L2A RCELLd_L2A RWRd_L2A RSHPd_L2A ECd_L2A FBCd_L2A).
Qed.
End QL2A.
End F0A_qL2A.

(* [comment removed for export] *)
Module F0A_qL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Be"; "Cd_L2Be"; "XMd_L2Be"; "RQ_L2Be"; "XR2_L2Be"; "sQ_L2Be"; "RESTd_L2Be"; "TQ_L2Be"; "TQr_L2Be"; "XKd_L2Be"; "XM2_L2Be"; "KEPTd_L2Be"; "Xf2_L2Be"; "run7_L2Be"; "run7r_L2Be"; "nkd_L2Be"; "sX2_L2Be"; "Edr_nf_L2Be"; "XEX2_L2Be"; "XEXd_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L2Be : axst := Eval vm_compute in Edr_L2Be.
Lemma Edr_eq_L2Be : Edr_L2Be = Edr_nf_L2Be. Proof. vm_cast_no_check (eq_refl Edr_nf_L2Be). Qed.

Definition XEXd_L2Be : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L2Be))].
Definition XMd_L2Be : axst := Eval vm_compute in (axf Edr_nf_L2Be XEXd_L2Be).
Lemma AXEd_L2Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L2Be)). Qed.
Definition nkd_L2Be : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L2Be) + 2 + 2)%nat.
Definition KEPTd_L2Be : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L2Be : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L2Be : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L2Be : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L2Be : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L2Be : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L2Be : rcivb RESTd_L2Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L2Be : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L2Be : rwrb RESTd_L2Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L2Be : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L2Be : axst := Eval vm_compute in (ax_with_facts XKd_L2Be (ss_facts (ax_S XKd_L2Be) ++ [F_cne])).
Lemma ECd_L2Be : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L2Be). Qed.
Lemma FBCd_L2Be : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L2Be : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L2Be) (ax_S PreQ3)).
Definition RQ_L2Be : list sobj := Eval vm_compute in (optR (entails_frA Cd_L2Be PreQ3 sQ_L2Be)).
Lemma HEQ_L2Be : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L2Be)). Qed.
Lemma HCK_L2Be : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L2Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L2Be PreQ3 PostQ3 Cd_L2Be RQ_L2Be) (ss_facts (ax_S Cd_L2Be))).
Lemma HTQ_L2Be : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L2Be). Qed.
Lemma QCHK_L2Be : ltac2:(tb__ "0|0|
S0S7S61U2S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L2Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L2Be PreQ3 PostQ3r Cd_L2Be RQ_L2Be) (ss_facts (ax_S Cd_L2Be))).
Lemma HTQr_L2Be : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L2Be). Qed.
Lemma QCHKr_L2Be : ltac2:(tb__ "0|0|
S0S7S61U2S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L2Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L2Be).
Lemma RUN7_L2Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L2Be). Qed.
Definition Xf2_L2Be : axst := Eval vm_compute in (leaf 0 run7_L2Be).
Lemma L7_L2Be : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L2Be)]. Qed.
Lemma NX7_L2Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L2Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L2Be).
Lemma RUN7r_L2Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L2Be). Qed.
Lemma L7r_L2Be : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L2Be)]. Qed.
Lemma NX7r_L2Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L2Be : list axform := Eval vm_compute in (XEX_of Xf2_L2Be).
Definition XM2_L2Be : axst := Eval vm_compute in (axf Xf2_L2Be XEX2_L2Be).
Lemma AXE2_L2Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L2Be)). Qed.
Definition XR2_L2Be : axst := Eval vm_compute in (XR_of XM2_L2Be).
Definition sX2_L2Be : wsub := Eval vm_compute in (sX_of XR2_L2Be (Wcan 2) UStopLe).
Lemma WXR2_L2Be : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L2Be : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L2Be : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L2Be))). Qed.
Lemma EQR2_L2Be : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L2Be). Qed.
Lemma ENT2_L2Be : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU2A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L2Be : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL2Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L2Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U2M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L2Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U2M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L2Be : drain_stmt_L2Be Edr_L2Be.
Proof.
  rewrite Edr_eq_L2Be.
  exact (f0_drain 2%nat QBe CST XGL HCST HXGL HCSTQ Cd_L2Be TQ_L2Be TQr_L2Be sQ_L2Be RQ_L2Be HEQ_L2Be HCK_L2Be HTQ_L2Be HTQr_L2Be QCHK_L2Be QCHKr_L2Be Xf2_L2Be XM2_L2Be XR2_L2Be XEX2_L2Be sX2_L2Be run7_L2Be
           NX7_L2Be RUN7_L2Be L7_L2Be run7r_L2Be NX7r_L2Be RUN7r_L2Be L7r_L2Be AXE2_L2Be WXR2_L2Be DXR2_L2Be NXR2_L2Be EQR2_L2Be ENT2_L2Be SID2_L2Be HCSTF Edr_nf_L2Be XMd_L2Be XKd_L2Be KEPTd_L2Be RESTd_L2Be XEXd_L2Be
           AXEd_L2Be OBJSd_L2Be EQKd_L2Be RCLSd_L2Be RCIVd_L2Be RCELLd_L2Be RWRd_L2Be RSHPd_L2Be ECd_L2Be FBCd_L2Be).
Qed.
Theorem ef0_drain_L2Be : edrain_stmt_L2Be Edr_L2Be.
Proof.
  rewrite Edr_eq_L2Be.
  exact (ef0_drain 2%nat QBe CST XGL HCST HXGL HCSTQ Cd_L2Be TQ_L2Be TQr_L2Be sQ_L2Be RQ_L2Be HEQ_L2Be HCK_L2Be HTQ_L2Be HTQr_L2Be QCHK_L2Be QCHKr_L2Be Xf2_L2Be XM2_L2Be XR2_L2Be XEX2_L2Be sX2_L2Be run7_L2Be
           NX7_L2Be RUN7_L2Be L7_L2Be run7r_L2Be NX7r_L2Be RUN7r_L2Be L7r_L2Be AXE2_L2Be WXR2_L2Be DXR2_L2Be NXR2_L2Be EQR2_L2Be ENT2_L2Be SID2_L2Be HCSTF Edr_nf_L2Be XMd_L2Be XKd_L2Be KEPTd_L2Be RESTd_L2Be XEXd_L2Be
           AXEd_L2Be OBJSd_L2Be EQKd_L2Be RCLSd_L2Be RCIVd_L2Be RCELLd_L2Be RWRd_L2Be RSHPd_L2Be ECd_L2Be FBCd_L2Be).
Qed.
End QL2Be.
End F0A_qL2Be.

(* [comment removed for export] *)
Module F0A_qL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Bf"; "Cd_L2Bf"; "XMd_L2Bf"; "RQ_L2Bf"; "XR2_L2Bf"; "sQ_L2Bf"; "RESTd_L2Bf"; "TQ_L2Bf"; "TQr_L2Bf"; "XKd_L2Bf"; "XM2_L2Bf"; "KEPTd_L2Bf"; "Xf2_L2Bf"; "run7_L2Bf"; "run7r_L2Bf"; "nkd_L2Bf"; "sX2_L2Bf"; "Edr_nf_L2Bf"; "XEX2_L2Bf"; "XEXd_L2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L2Bf : axst := Eval vm_compute in Edr_L2Bf.
Lemma Edr_eq_L2Bf : Edr_L2Bf = Edr_nf_L2Bf. Proof. vm_cast_no_check (eq_refl Edr_nf_L2Bf). Qed.

Definition XEXd_L2Bf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L2Bf))].
Definition XMd_L2Bf : axst := Eval vm_compute in (axf Edr_nf_L2Bf XEXd_L2Bf).
Lemma AXEd_L2Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L2Bf)). Qed.
Definition nkd_L2Bf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L2Bf) + 2 + 2)%nat.
Definition KEPTd_L2Bf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L2Bf : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L2Bf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L2Bf : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L2Bf : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L2Bf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L2Bf : rcivb RESTd_L2Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L2Bf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L2Bf : rwrb RESTd_L2Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L2Bf : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L2Bf : axst := Eval vm_compute in (ax_with_facts XKd_L2Bf (ss_facts (ax_S XKd_L2Bf) ++ [F_cne])).
Lemma ECd_L2Bf : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L2Bf). Qed.
Lemma FBCd_L2Bf : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L2Bf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L2Bf) (ax_S PreQ3)).
Definition RQ_L2Bf : list sobj := Eval vm_compute in (optR (entails_frA Cd_L2Bf PreQ3 sQ_L2Bf)).
Lemma HEQ_L2Bf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L2Bf)). Qed.
Lemma HCK_L2Bf : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L2Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L2Bf PreQ3 PostQ3 Cd_L2Bf RQ_L2Bf) (ss_facts (ax_S Cd_L2Bf))).
Lemma HTQ_L2Bf : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L2Bf). Qed.
Lemma QCHK_L2Bf : ltac2:(tb__ "0|0|
S0S7S61U2S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L2Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L2Bf PreQ3 PostQ3r Cd_L2Bf RQ_L2Bf) (ss_facts (ax_S Cd_L2Bf))).
Lemma HTQr_L2Bf : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L2Bf). Qed.
Lemma QCHKr_L2Bf : ltac2:(tb__ "0|0|
S0S7S61U2S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L2Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L2Bf).
Lemma RUN7_L2Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L2Bf). Qed.
Definition Xf2_L2Bf : axst := Eval vm_compute in (leaf 0 run7_L2Bf).
Lemma L7_L2Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L2Bf)]. Qed.
Lemma NX7_L2Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L2Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L2Bf).
Lemma RUN7r_L2Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L2Bf). Qed.
Lemma L7r_L2Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L2Bf)]. Qed.
Lemma NX7r_L2Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L2Bf : list axform := Eval vm_compute in (XEX_of Xf2_L2Bf).
Definition XM2_L2Bf : axst := Eval vm_compute in (axf Xf2_L2Bf XEX2_L2Bf).
Lemma AXE2_L2Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L2Bf)). Qed.
Definition XR2_L2Bf : axst := Eval vm_compute in (XR_of XM2_L2Bf).
Definition sX2_L2Bf : wsub := Eval vm_compute in (sX_of XR2_L2Bf (Wcan 2) UStopLe).
Lemma WXR2_L2Bf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L2Bf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L2Bf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L2Bf))). Qed.
Lemma EQR2_L2Bf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L2Bf). Qed.
Lemma ENT2_L2Bf : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU2A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L2Bf : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL2Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L2Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U2M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L2Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U2M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L2Bf : drain_stmt_L2Bf Edr_L2Bf.
Proof.
  rewrite Edr_eq_L2Bf.
  exact (f0_drain 2%nat QBf CST XGL HCST HXGL HCSTQ Cd_L2Bf TQ_L2Bf TQr_L2Bf sQ_L2Bf RQ_L2Bf HEQ_L2Bf HCK_L2Bf HTQ_L2Bf HTQr_L2Bf QCHK_L2Bf QCHKr_L2Bf Xf2_L2Bf XM2_L2Bf XR2_L2Bf XEX2_L2Bf sX2_L2Bf run7_L2Bf
           NX7_L2Bf RUN7_L2Bf L7_L2Bf run7r_L2Bf NX7r_L2Bf RUN7r_L2Bf L7r_L2Bf AXE2_L2Bf WXR2_L2Bf DXR2_L2Bf NXR2_L2Bf EQR2_L2Bf ENT2_L2Bf SID2_L2Bf HCSTF Edr_nf_L2Bf XMd_L2Bf XKd_L2Bf KEPTd_L2Bf RESTd_L2Bf XEXd_L2Bf
           AXEd_L2Bf OBJSd_L2Bf EQKd_L2Bf RCLSd_L2Bf RCIVd_L2Bf RCELLd_L2Bf RWRd_L2Bf RSHPd_L2Bf ECd_L2Bf FBCd_L2Bf).
Qed.
Theorem ef0_drain_L2Bf : edrain_stmt_L2Bf Edr_L2Bf.
Proof.
  rewrite Edr_eq_L2Bf.
  exact (ef0_drain 2%nat QBf CST XGL HCST HXGL HCSTQ Cd_L2Bf TQ_L2Bf TQr_L2Bf sQ_L2Bf RQ_L2Bf HEQ_L2Bf HCK_L2Bf HTQ_L2Bf HTQr_L2Bf QCHK_L2Bf QCHKr_L2Bf Xf2_L2Bf XM2_L2Bf XR2_L2Bf XEX2_L2Bf sX2_L2Bf run7_L2Bf
           NX7_L2Bf RUN7_L2Bf L7_L2Bf run7r_L2Bf NX7r_L2Bf RUN7r_L2Bf L7r_L2Bf AXE2_L2Bf WXR2_L2Bf DXR2_L2Bf NXR2_L2Bf EQR2_L2Bf ENT2_L2Bf SID2_L2Bf HCSTF Edr_nf_L2Bf XMd_L2Bf XKd_L2Bf KEPTd_L2Bf RESTd_L2Bf XEXd_L2Bf
           AXEd_L2Bf OBJSd_L2Bf EQKd_L2Bf RCLSd_L2Bf RCIVd_L2Bf RCELLd_L2Bf RWRd_L2Bf RSHPd_L2Bf ECd_L2Bf FBCd_L2Bf).
Qed.
End QL2Bf.
End F0A_qL2Bf.

(* [comment removed for export] *)
Module F0A_q0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0A"; "Cd_0A"; "XMd_0A"; "RQ_0A"; "XR2_0A"; "sQ_0A"; "RESTd_0A"; "TQ_0A"; "TQr_0A"; "XKd_0A"; "XM2_0A"; "KEPTd_0A"; "Xf2_0A"; "run7_0A"; "run7r_0A"; "nkd_0A"; "sX2_0A"; "Edr_nf_0A"; "XEX2_0A"; "XEXd_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_0A : axst := Eval vm_compute in Edr_0A.
Lemma Edr_eq_0A : Edr_0A = Edr_nf_0A. Proof. vm_cast_no_check (eq_refl Edr_nf_0A). Qed.

Definition XEXd_0A : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_0A))].
Definition XMd_0A : axst := Eval vm_compute in (axf Edr_nf_0A XEXd_0A).
Lemma AXEd_0A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_0A)). Qed.
Definition nkd_0A : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_0A) + 0 + 2)%nat.
Definition KEPTd_0A : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_0A : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_0A : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_0A : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_0A : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_0A : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_0A : rcivb RESTd_0A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_0A : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_0A : rwrb RESTd_0A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_0A : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_0A : axst := Eval vm_compute in (ax_with_facts XKd_0A (ss_facts (ax_S XKd_0A) ++ [F_cne])).
Lemma ECd_0A : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_0A). Qed.
Lemma FBCd_0A : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_0A : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_0A) (ax_S PreQ3)).
Definition RQ_0A : list sobj := Eval vm_compute in (optR (entails_frA Cd_0A PreQ3 sQ_0A)).
Lemma HEQ_0A : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_0A)). Qed.
Lemma HCK_0A : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_0A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_0A PreQ3 PostQ3 Cd_0A RQ_0A) (ss_facts (ax_S Cd_0A))).
Lemma HTQ_0A : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_0A). Qed.
Lemma QCHK_0A : ltac2:(tb__ "0|0|
S0S7S61U0S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_0A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_0A PreQ3 PostQ3r Cd_0A RQ_0A) (ss_facts (ax_S Cd_0A))).
Lemma HTQr_0A : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_0A). Qed.
Lemma QCHKr_0A : ltac2:(tb__ "0|0|
S0S7S61U0S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_0A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_0A).
Lemma RUN7_0A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_0A). Qed.
Definition Xf2_0A : axst := Eval vm_compute in (leaf 0 run7_0A).
Lemma L7_0A : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_0A)]. Qed.
Lemma NX7_0A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_0A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_0A).
Lemma RUN7r_0A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_0A). Qed.
Lemma L7r_0A : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_0A)]. Qed.
Lemma NX7r_0A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_0A : list axform := Eval vm_compute in (XEX_of Xf2_0A).
Definition XM2_0A : axst := Eval vm_compute in (axf Xf2_0A XEX2_0A).
Lemma AXE2_0A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_0A)). Qed.
Definition XR2_0A : axst := Eval vm_compute in (XR_of XM2_0A).
Definition sX2_0A : wsub := Eval vm_compute in (sX_of XR2_0A (Wcan 0) UStopLe).
Lemma WXR2_0A : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_0A : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_0A : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_0A))). Qed.
Lemma EQR2_0A : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_0A). Qed.
Lemma ENT2_0A : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU0A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_0A : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_0A (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U0M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_0A (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U0M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_0A : drain_stmt_0A Edr_0A.
Proof.
  rewrite Edr_eq_0A.
  exact (f0_drain 0%nat QA CST XGL HCST HXGL HCSTQ Cd_0A TQ_0A TQr_0A sQ_0A RQ_0A HEQ_0A HCK_0A HTQ_0A HTQr_0A QCHK_0A QCHKr_0A Xf2_0A XM2_0A XR2_0A XEX2_0A sX2_0A run7_0A
           NX7_0A RUN7_0A L7_0A run7r_0A NX7r_0A RUN7r_0A L7r_0A AXE2_0A WXR2_0A DXR2_0A NXR2_0A EQR2_0A ENT2_0A SID2_0A HCSTF Edr_nf_0A XMd_0A XKd_0A KEPTd_0A RESTd_0A XEXd_0A
           AXEd_0A OBJSd_0A EQKd_0A RCLSd_0A RCIVd_0A RCELLd_0A RWRd_0A RSHPd_0A ECd_0A FBCd_0A).
Qed.
Theorem ef0_drain_0A : edrain_stmt_0A Edr_0A.
Proof.
  rewrite Edr_eq_0A.
  exact (ef0_drain 0%nat QA CST XGL HCST HXGL HCSTQ Cd_0A TQ_0A TQr_0A sQ_0A RQ_0A HEQ_0A HCK_0A HTQ_0A HTQr_0A QCHK_0A QCHKr_0A Xf2_0A XM2_0A XR2_0A XEX2_0A sX2_0A run7_0A
           NX7_0A RUN7_0A L7_0A run7r_0A NX7r_0A RUN7r_0A L7r_0A AXE2_0A WXR2_0A DXR2_0A NXR2_0A EQR2_0A ENT2_0A SID2_0A HCSTF Edr_nf_0A XMd_0A XKd_0A KEPTd_0A RESTd_0A XEXd_0A
           AXEd_0A OBJSd_0A EQKd_0A RCLSd_0A RCIVd_0A RCELLd_0A RWRd_0A RSHPd_0A ECd_0A FBCd_0A).
Qed.
End Q0A.
End F0A_q0A.

(* [comment removed for export] *)
Module F0A_q0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0Be"; "Cd_0Be"; "XMd_0Be"; "RQ_0Be"; "XR2_0Be"; "sQ_0Be"; "RESTd_0Be"; "TQ_0Be"; "TQr_0Be"; "XKd_0Be"; "XM2_0Be"; "KEPTd_0Be"; "Xf2_0Be"; "run7_0Be"; "run7r_0Be"; "nkd_0Be"; "sX2_0Be"; "Edr_nf_0Be"; "XEX2_0Be"; "XEXd_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_0Be : axst := Eval vm_compute in Edr_0Be.
Lemma Edr_eq_0Be : Edr_0Be = Edr_nf_0Be. Proof. vm_cast_no_check (eq_refl Edr_nf_0Be). Qed.

Definition XEXd_0Be : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_0Be))].
Definition XMd_0Be : axst := Eval vm_compute in (axf Edr_nf_0Be XEXd_0Be).
Lemma AXEd_0Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_0Be)). Qed.
Definition nkd_0Be : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_0Be) + 0 + 2)%nat.
Definition KEPTd_0Be : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_0Be : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_0Be : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_0Be : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_0Be : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_0Be : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_0Be : rcivb RESTd_0Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_0Be : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_0Be : rwrb RESTd_0Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_0Be : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_0Be : axst := Eval vm_compute in (ax_with_facts XKd_0Be (ss_facts (ax_S XKd_0Be) ++ [F_cne])).
Lemma ECd_0Be : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_0Be). Qed.
Lemma FBCd_0Be : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_0Be : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_0Be) (ax_S PreQ3)).
Definition RQ_0Be : list sobj := Eval vm_compute in (optR (entails_frA Cd_0Be PreQ3 sQ_0Be)).
Lemma HEQ_0Be : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_0Be)). Qed.
Lemma HCK_0Be : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_0Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_0Be PreQ3 PostQ3 Cd_0Be RQ_0Be) (ss_facts (ax_S Cd_0Be))).
Lemma HTQ_0Be : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_0Be). Qed.
Lemma QCHK_0Be : ltac2:(tb__ "0|0|
S0S7S61U0S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_0Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_0Be PreQ3 PostQ3r Cd_0Be RQ_0Be) (ss_facts (ax_S Cd_0Be))).
Lemma HTQr_0Be : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_0Be). Qed.
Lemma QCHKr_0Be : ltac2:(tb__ "0|0|
S0S7S61U0S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_0Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_0Be).
Lemma RUN7_0Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_0Be). Qed.
Definition Xf2_0Be : axst := Eval vm_compute in (leaf 0 run7_0Be).
Lemma L7_0Be : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_0Be)]. Qed.
Lemma NX7_0Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_0Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_0Be).
Lemma RUN7r_0Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_0Be). Qed.
Lemma L7r_0Be : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_0Be)]. Qed.
Lemma NX7r_0Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_0Be : list axform := Eval vm_compute in (XEX_of Xf2_0Be).
Definition XM2_0Be : axst := Eval vm_compute in (axf Xf2_0Be XEX2_0Be).
Lemma AXE2_0Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_0Be)). Qed.
Definition XR2_0Be : axst := Eval vm_compute in (XR_of XM2_0Be).
Definition sX2_0Be : wsub := Eval vm_compute in (sX_of XR2_0Be (Wcan 0) UStopLe).
Lemma WXR2_0Be : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_0Be : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_0Be : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_0Be))). Qed.
Lemma EQR2_0Be : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_0Be). Qed.
Lemma ENT2_0Be : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU0A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_0Be : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_0Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U0M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_0Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U0M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_0Be : drain_stmt_0Be Edr_0Be.
Proof.
  rewrite Edr_eq_0Be.
  exact (f0_drain 0%nat QBe CST XGL HCST HXGL HCSTQ Cd_0Be TQ_0Be TQr_0Be sQ_0Be RQ_0Be HEQ_0Be HCK_0Be HTQ_0Be HTQr_0Be QCHK_0Be QCHKr_0Be Xf2_0Be XM2_0Be XR2_0Be XEX2_0Be sX2_0Be run7_0Be
           NX7_0Be RUN7_0Be L7_0Be run7r_0Be NX7r_0Be RUN7r_0Be L7r_0Be AXE2_0Be WXR2_0Be DXR2_0Be NXR2_0Be EQR2_0Be ENT2_0Be SID2_0Be HCSTF Edr_nf_0Be XMd_0Be XKd_0Be KEPTd_0Be RESTd_0Be XEXd_0Be
           AXEd_0Be OBJSd_0Be EQKd_0Be RCLSd_0Be RCIVd_0Be RCELLd_0Be RWRd_0Be RSHPd_0Be ECd_0Be FBCd_0Be).
Qed.
Theorem ef0_drain_0Be : edrain_stmt_0Be Edr_0Be.
Proof.
  rewrite Edr_eq_0Be.
  exact (ef0_drain 0%nat QBe CST XGL HCST HXGL HCSTQ Cd_0Be TQ_0Be TQr_0Be sQ_0Be RQ_0Be HEQ_0Be HCK_0Be HTQ_0Be HTQr_0Be QCHK_0Be QCHKr_0Be Xf2_0Be XM2_0Be XR2_0Be XEX2_0Be sX2_0Be run7_0Be
           NX7_0Be RUN7_0Be L7_0Be run7r_0Be NX7r_0Be RUN7r_0Be L7r_0Be AXE2_0Be WXR2_0Be DXR2_0Be NXR2_0Be EQR2_0Be ENT2_0Be SID2_0Be HCSTF Edr_nf_0Be XMd_0Be XKd_0Be KEPTd_0Be RESTd_0Be XEXd_0Be
           AXEd_0Be OBJSd_0Be EQKd_0Be RCLSd_0Be RCIVd_0Be RCELLd_0Be RWRd_0Be RSHPd_0Be ECd_0Be FBCd_0Be).
Qed.
End Q0Be.
End F0A_q0Be.

(* [comment removed for export] *)
Module F0A_q0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0Bf"; "Cd_0Bf"; "XMd_0Bf"; "RQ_0Bf"; "XR2_0Bf"; "sQ_0Bf"; "RESTd_0Bf"; "TQ_0Bf"; "TQr_0Bf"; "XKd_0Bf"; "XM2_0Bf"; "KEPTd_0Bf"; "Xf2_0Bf"; "run7_0Bf"; "run7r_0Bf"; "nkd_0Bf"; "sX2_0Bf"; "Edr_nf_0Bf"; "XEX2_0Bf"; "XEXd_0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_0Bf : axst := Eval vm_compute in Edr_0Bf.
Lemma Edr_eq_0Bf : Edr_0Bf = Edr_nf_0Bf. Proof. vm_cast_no_check (eq_refl Edr_nf_0Bf). Qed.

Definition XEXd_0Bf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_0Bf))].
Definition XMd_0Bf : axst := Eval vm_compute in (axf Edr_nf_0Bf XEXd_0Bf).
Lemma AXEd_0Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_0Bf)). Qed.
Definition nkd_0Bf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_0Bf) + 0 + 2)%nat.
Definition KEPTd_0Bf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_0Bf : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_0Bf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_0Bf : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_0Bf : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_0Bf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_0Bf : rcivb RESTd_0Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_0Bf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_0Bf : rwrb RESTd_0Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_0Bf : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_0Bf : axst := Eval vm_compute in (ax_with_facts XKd_0Bf (ss_facts (ax_S XKd_0Bf) ++ [F_cne])).
Lemma ECd_0Bf : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_0Bf). Qed.
Lemma FBCd_0Bf : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_0Bf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_0Bf) (ax_S PreQ3)).
Definition RQ_0Bf : list sobj := Eval vm_compute in (optR (entails_frA Cd_0Bf PreQ3 sQ_0Bf)).
Lemma HEQ_0Bf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_0Bf)). Qed.
Lemma HCK_0Bf : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_0Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_0Bf PreQ3 PostQ3 Cd_0Bf RQ_0Bf) (ss_facts (ax_S Cd_0Bf))).
Lemma HTQ_0Bf : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_0Bf). Qed.
Lemma QCHK_0Bf : ltac2:(tb__ "0|0|
S0S7S61U0S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_0Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_0Bf PreQ3 PostQ3r Cd_0Bf RQ_0Bf) (ss_facts (ax_S Cd_0Bf))).
Lemma HTQr_0Bf : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_0Bf). Qed.
Lemma QCHKr_0Bf : ltac2:(tb__ "0|0|
S0S7S61U0S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_0Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_0Bf).
Lemma RUN7_0Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_0Bf). Qed.
Definition Xf2_0Bf : axst := Eval vm_compute in (leaf 0 run7_0Bf).
Lemma L7_0Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_0Bf)]. Qed.
Lemma NX7_0Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_0Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_0Bf).
Lemma RUN7r_0Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_0Bf). Qed.
Lemma L7r_0Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_0Bf)]. Qed.
Lemma NX7r_0Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_0Bf : list axform := Eval vm_compute in (XEX_of Xf2_0Bf).
Definition XM2_0Bf : axst := Eval vm_compute in (axf Xf2_0Bf XEX2_0Bf).
Lemma AXE2_0Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_0Bf)). Qed.
Definition XR2_0Bf : axst := Eval vm_compute in (XR_of XM2_0Bf).
Definition sX2_0Bf : wsub := Eval vm_compute in (sX_of XR2_0Bf (Wcan 0) UStopLe).
Lemma WXR2_0Bf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_0Bf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_0Bf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_0Bf))). Qed.
Lemma EQR2_0Bf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_0Bf). Qed.
Lemma ENT2_0Bf : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU0A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_0Bf : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q0Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_0Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U0M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_0Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U0M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_0Bf : drain_stmt_0Bf Edr_0Bf.
Proof.
  rewrite Edr_eq_0Bf.
  exact (f0_drain 0%nat QBf CST XGL HCST HXGL HCSTQ Cd_0Bf TQ_0Bf TQr_0Bf sQ_0Bf RQ_0Bf HEQ_0Bf HCK_0Bf HTQ_0Bf HTQr_0Bf QCHK_0Bf QCHKr_0Bf Xf2_0Bf XM2_0Bf XR2_0Bf XEX2_0Bf sX2_0Bf run7_0Bf
           NX7_0Bf RUN7_0Bf L7_0Bf run7r_0Bf NX7r_0Bf RUN7r_0Bf L7r_0Bf AXE2_0Bf WXR2_0Bf DXR2_0Bf NXR2_0Bf EQR2_0Bf ENT2_0Bf SID2_0Bf HCSTF Edr_nf_0Bf XMd_0Bf XKd_0Bf KEPTd_0Bf RESTd_0Bf XEXd_0Bf
           AXEd_0Bf OBJSd_0Bf EQKd_0Bf RCLSd_0Bf RCIVd_0Bf RCELLd_0Bf RWRd_0Bf RSHPd_0Bf ECd_0Bf FBCd_0Bf).
Qed.
Theorem ef0_drain_0Bf : edrain_stmt_0Bf Edr_0Bf.
Proof.
  rewrite Edr_eq_0Bf.
  exact (ef0_drain 0%nat QBf CST XGL HCST HXGL HCSTQ Cd_0Bf TQ_0Bf TQr_0Bf sQ_0Bf RQ_0Bf HEQ_0Bf HCK_0Bf HTQ_0Bf HTQr_0Bf QCHK_0Bf QCHKr_0Bf Xf2_0Bf XM2_0Bf XR2_0Bf XEX2_0Bf sX2_0Bf run7_0Bf
           NX7_0Bf RUN7_0Bf L7_0Bf run7r_0Bf NX7r_0Bf RUN7r_0Bf L7r_0Bf AXE2_0Bf WXR2_0Bf DXR2_0Bf NXR2_0Bf EQR2_0Bf ENT2_0Bf SID2_0Bf HCSTF Edr_nf_0Bf XMd_0Bf XKd_0Bf KEPTd_0Bf RESTd_0Bf XEXd_0Bf
           AXEd_0Bf OBJSd_0Bf EQKd_0Bf RCLSd_0Bf RCIVd_0Bf RCELLd_0Bf RWRd_0Bf RSHPd_0Bf ECd_0Bf FBCd_0Bf).
Qed.
End Q0Bf.
End F0A_q0Bf.

