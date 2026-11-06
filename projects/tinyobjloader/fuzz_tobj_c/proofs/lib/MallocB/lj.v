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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain ib.

(* [comment removed for export] *)
Module F0A_q1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1A"; "Cd_1A"; "XMd_1A"; "RQ_1A"; "XR2_1A"; "sQ_1A"; "RESTd_1A"; "TQ_1A"; "TQr_1A"; "XKd_1A"; "XM2_1A"; "KEPTd_1A"; "Xf2_1A"; "run7_1A"; "run7r_1A"; "nkd_1A"; "sX2_1A"; "Edr_nf_1A"; "XEX2_1A"; "XEXd_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_1A : axst := Eval vm_compute in Edr_1A.
Lemma Edr_eq_1A : Edr_1A = Edr_nf_1A. Proof. vm_cast_no_check (eq_refl Edr_nf_1A). Qed.

Definition XEXd_1A : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_1A))].
Definition XMd_1A : axst := Eval vm_compute in (axf Edr_nf_1A XEXd_1A).
Lemma AXEd_1A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_1A)). Qed.
Definition nkd_1A : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_1A) + 1 + 2)%nat.
Definition KEPTd_1A : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_1A : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_1A : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_1A : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_1A : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_1A : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_1A : rcivb RESTd_1A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_1A : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_1A : rwrb RESTd_1A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_1A : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_1A : axst := Eval vm_compute in (ax_with_facts XKd_1A (ss_facts (ax_S XKd_1A) ++ [F_cne])).
Lemma ECd_1A : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_1A). Qed.
Lemma FBCd_1A : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_1A : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_1A) (ax_S PreQ3)).
Definition RQ_1A : list sobj := Eval vm_compute in (optR (entails_frA Cd_1A PreQ3 sQ_1A)).
Lemma HEQ_1A : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_1A)). Qed.
Lemma HCK_1A : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_1A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_1A PreQ3 PostQ3 Cd_1A RQ_1A) (ss_facts (ax_S Cd_1A))).
Lemma HTQ_1A : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_1A). Qed.
Lemma QCHK_1A : ltac2:(tb__ "0|0|
S0S7S61U1S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_1A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_1A PreQ3 PostQ3r Cd_1A RQ_1A) (ss_facts (ax_S Cd_1A))).
Lemma HTQr_1A : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_1A). Qed.
Lemma QCHKr_1A : ltac2:(tb__ "0|0|
S0S7S61U1S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_1A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_1A).
Lemma RUN7_1A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_1A). Qed.
Definition Xf2_1A : axst := Eval vm_compute in (leaf 0 run7_1A).
Lemma L7_1A : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_1A)]. Qed.
Lemma NX7_1A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_1A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_1A).
Lemma RUN7r_1A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_1A). Qed.
Lemma L7r_1A : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_1A)]. Qed.
Lemma NX7r_1A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_1A : list axform := Eval vm_compute in (XEX_of Xf2_1A).
Definition XM2_1A : axst := Eval vm_compute in (axf Xf2_1A XEX2_1A).
Lemma AXE2_1A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_1A)). Qed.
Definition XR2_1A : axst := Eval vm_compute in (XR_of XM2_1A).
Definition sX2_1A : wsub := Eval vm_compute in (sX_of XR2_1A (Wcan 1) UStopLe).
Lemma WXR2_1A : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_1A : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_1A : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_1A))). Qed.
Lemma EQR2_1A : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_1A). Qed.
Lemma ENT2_1A : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU1A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_1A : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q1A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_1A (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U1M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_1A (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U1M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_1A : drain_stmt_1A Edr_1A.
Proof.
  rewrite Edr_eq_1A.
  exact (f0_drain 1%nat QA CST XGL HCST HXGL HCSTQ Cd_1A TQ_1A TQr_1A sQ_1A RQ_1A HEQ_1A HCK_1A HTQ_1A HTQr_1A QCHK_1A QCHKr_1A Xf2_1A XM2_1A XR2_1A XEX2_1A sX2_1A run7_1A
           NX7_1A RUN7_1A L7_1A run7r_1A NX7r_1A RUN7r_1A L7r_1A AXE2_1A WXR2_1A DXR2_1A NXR2_1A EQR2_1A ENT2_1A SID2_1A HCSTF Edr_nf_1A XMd_1A XKd_1A KEPTd_1A RESTd_1A XEXd_1A
           AXEd_1A OBJSd_1A EQKd_1A RCLSd_1A RCIVd_1A RCELLd_1A RWRd_1A RSHPd_1A ECd_1A FBCd_1A).
Qed.
Theorem ef0_drain_1A : edrain_stmt_1A Edr_1A.
Proof.
  rewrite Edr_eq_1A.
  exact (ef0_drain 1%nat QA CST XGL HCST HXGL HCSTQ Cd_1A TQ_1A TQr_1A sQ_1A RQ_1A HEQ_1A HCK_1A HTQ_1A HTQr_1A QCHK_1A QCHKr_1A Xf2_1A XM2_1A XR2_1A XEX2_1A sX2_1A run7_1A
           NX7_1A RUN7_1A L7_1A run7r_1A NX7r_1A RUN7r_1A L7r_1A AXE2_1A WXR2_1A DXR2_1A NXR2_1A EQR2_1A ENT2_1A SID2_1A HCSTF Edr_nf_1A XMd_1A XKd_1A KEPTd_1A RESTd_1A XEXd_1A
           AXEd_1A OBJSd_1A EQKd_1A RCLSd_1A RCIVd_1A RCELLd_1A RWRd_1A RSHPd_1A ECd_1A FBCd_1A).
Qed.
End Q1A.
End F0A_q1A.

(* [comment removed for export] *)
Module F0A_q1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Be"; "Cd_1Be"; "XMd_1Be"; "RQ_1Be"; "XR2_1Be"; "sQ_1Be"; "RESTd_1Be"; "TQ_1Be"; "TQr_1Be"; "XKd_1Be"; "XM2_1Be"; "KEPTd_1Be"; "Xf2_1Be"; "run7_1Be"; "run7r_1Be"; "nkd_1Be"; "sX2_1Be"; "Edr_nf_1Be"; "XEX2_1Be"; "XEXd_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_1Be : axst := Eval vm_compute in Edr_1Be.
Lemma Edr_eq_1Be : Edr_1Be = Edr_nf_1Be. Proof. vm_cast_no_check (eq_refl Edr_nf_1Be). Qed.

Definition XEXd_1Be : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_1Be))].
Definition XMd_1Be : axst := Eval vm_compute in (axf Edr_nf_1Be XEXd_1Be).
Lemma AXEd_1Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_1Be)). Qed.
Definition nkd_1Be : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_1Be) + 1 + 2)%nat.
Definition KEPTd_1Be : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_1Be : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_1Be : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_1Be : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_1Be : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_1Be : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_1Be : rcivb RESTd_1Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_1Be : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_1Be : rwrb RESTd_1Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_1Be : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_1Be : axst := Eval vm_compute in (ax_with_facts XKd_1Be (ss_facts (ax_S XKd_1Be) ++ [F_cne])).
Lemma ECd_1Be : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_1Be). Qed.
Lemma FBCd_1Be : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_1Be : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_1Be) (ax_S PreQ3)).
Definition RQ_1Be : list sobj := Eval vm_compute in (optR (entails_frA Cd_1Be PreQ3 sQ_1Be)).
Lemma HEQ_1Be : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_1Be)). Qed.
Lemma HCK_1Be : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_1Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_1Be PreQ3 PostQ3 Cd_1Be RQ_1Be) (ss_facts (ax_S Cd_1Be))).
Lemma HTQ_1Be : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_1Be). Qed.
Lemma QCHK_1Be : ltac2:(tb__ "0|0|
S0S7S61U1S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_1Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_1Be PreQ3 PostQ3r Cd_1Be RQ_1Be) (ss_facts (ax_S Cd_1Be))).
Lemma HTQr_1Be : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_1Be). Qed.
Lemma QCHKr_1Be : ltac2:(tb__ "0|0|
S0S7S61U1S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_1Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_1Be).
Lemma RUN7_1Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_1Be). Qed.
Definition Xf2_1Be : axst := Eval vm_compute in (leaf 0 run7_1Be).
Lemma L7_1Be : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_1Be)]. Qed.
Lemma NX7_1Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_1Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_1Be).
Lemma RUN7r_1Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_1Be). Qed.
Lemma L7r_1Be : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_1Be)]. Qed.
Lemma NX7r_1Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_1Be : list axform := Eval vm_compute in (XEX_of Xf2_1Be).
Definition XM2_1Be : axst := Eval vm_compute in (axf Xf2_1Be XEX2_1Be).
Lemma AXE2_1Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_1Be)). Qed.
Definition XR2_1Be : axst := Eval vm_compute in (XR_of XM2_1Be).
Definition sX2_1Be : wsub := Eval vm_compute in (sX_of XR2_1Be (Wcan 1) UStopLe).
Lemma WXR2_1Be : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_1Be : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_1Be : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_1Be))). Qed.
Lemma EQR2_1Be : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_1Be). Qed.
Lemma ENT2_1Be : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU1A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_1Be : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q1Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_1Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U1M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_1Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U1M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_1Be : drain_stmt_1Be Edr_1Be.
Proof.
  rewrite Edr_eq_1Be.
  exact (f0_drain 1%nat QBe CST XGL HCST HXGL HCSTQ Cd_1Be TQ_1Be TQr_1Be sQ_1Be RQ_1Be HEQ_1Be HCK_1Be HTQ_1Be HTQr_1Be QCHK_1Be QCHKr_1Be Xf2_1Be XM2_1Be XR2_1Be XEX2_1Be sX2_1Be run7_1Be
           NX7_1Be RUN7_1Be L7_1Be run7r_1Be NX7r_1Be RUN7r_1Be L7r_1Be AXE2_1Be WXR2_1Be DXR2_1Be NXR2_1Be EQR2_1Be ENT2_1Be SID2_1Be HCSTF Edr_nf_1Be XMd_1Be XKd_1Be KEPTd_1Be RESTd_1Be XEXd_1Be
           AXEd_1Be OBJSd_1Be EQKd_1Be RCLSd_1Be RCIVd_1Be RCELLd_1Be RWRd_1Be RSHPd_1Be ECd_1Be FBCd_1Be).
Qed.
Theorem ef0_drain_1Be : edrain_stmt_1Be Edr_1Be.
Proof.
  rewrite Edr_eq_1Be.
  exact (ef0_drain 1%nat QBe CST XGL HCST HXGL HCSTQ Cd_1Be TQ_1Be TQr_1Be sQ_1Be RQ_1Be HEQ_1Be HCK_1Be HTQ_1Be HTQr_1Be QCHK_1Be QCHKr_1Be Xf2_1Be XM2_1Be XR2_1Be XEX2_1Be sX2_1Be run7_1Be
           NX7_1Be RUN7_1Be L7_1Be run7r_1Be NX7r_1Be RUN7r_1Be L7r_1Be AXE2_1Be WXR2_1Be DXR2_1Be NXR2_1Be EQR2_1Be ENT2_1Be SID2_1Be HCSTF Edr_nf_1Be XMd_1Be XKd_1Be KEPTd_1Be RESTd_1Be XEXd_1Be
           AXEd_1Be OBJSd_1Be EQKd_1Be RCLSd_1Be RCIVd_1Be RCELLd_1Be RWRd_1Be RSHPd_1Be ECd_1Be FBCd_1Be).
Qed.
End Q1Be.
End F0A_q1Be.

(* [comment removed for export] *)
Module F0A_q1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Bf"; "Cd_1Bf"; "XMd_1Bf"; "RQ_1Bf"; "XR2_1Bf"; "sQ_1Bf"; "RESTd_1Bf"; "TQ_1Bf"; "TQr_1Bf"; "XKd_1Bf"; "XM2_1Bf"; "KEPTd_1Bf"; "Xf2_1Bf"; "run7_1Bf"; "run7r_1Bf"; "nkd_1Bf"; "sX2_1Bf"; "Edr_nf_1Bf"; "XEX2_1Bf"; "XEXd_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_1Bf : axst := Eval vm_compute in Edr_1Bf.
Lemma Edr_eq_1Bf : Edr_1Bf = Edr_nf_1Bf. Proof. vm_cast_no_check (eq_refl Edr_nf_1Bf). Qed.

Definition XEXd_1Bf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_1Bf))].
Definition XMd_1Bf : axst := Eval vm_compute in (axf Edr_nf_1Bf XEXd_1Bf).
Lemma AXEd_1Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_1Bf)). Qed.
Definition nkd_1Bf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_1Bf) + 1 + 2)%nat.
Definition KEPTd_1Bf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_1Bf : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_1Bf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_1Bf : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_1Bf : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_1Bf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_1Bf : rcivb RESTd_1Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_1Bf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_1Bf : rwrb RESTd_1Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_1Bf : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_1Bf : axst := Eval vm_compute in (ax_with_facts XKd_1Bf (ss_facts (ax_S XKd_1Bf) ++ [F_cne])).
Lemma ECd_1Bf : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_1Bf). Qed.
Lemma FBCd_1Bf : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_1Bf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_1Bf) (ax_S PreQ3)).
Definition RQ_1Bf : list sobj := Eval vm_compute in (optR (entails_frA Cd_1Bf PreQ3 sQ_1Bf)).
Lemma HEQ_1Bf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_1Bf)). Qed.
Lemma HCK_1Bf : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_1Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_1Bf PreQ3 PostQ3 Cd_1Bf RQ_1Bf) (ss_facts (ax_S Cd_1Bf))).
Lemma HTQ_1Bf : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_1Bf). Qed.
Lemma QCHK_1Bf : ltac2:(tb__ "0|0|
S0S7S61U1S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_1Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_1Bf PreQ3 PostQ3r Cd_1Bf RQ_1Bf) (ss_facts (ax_S Cd_1Bf))).
Lemma HTQr_1Bf : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_1Bf). Qed.
Lemma QCHKr_1Bf : ltac2:(tb__ "0|0|
S0S7S61U1S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_1Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_1Bf).
Lemma RUN7_1Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_1Bf). Qed.
Definition Xf2_1Bf : axst := Eval vm_compute in (leaf 0 run7_1Bf).
Lemma L7_1Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_1Bf)]. Qed.
Lemma NX7_1Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_1Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_1Bf).
Lemma RUN7r_1Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_1Bf). Qed.
Lemma L7r_1Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_1Bf)]. Qed.
Lemma NX7r_1Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_1Bf : list axform := Eval vm_compute in (XEX_of Xf2_1Bf).
Definition XM2_1Bf : axst := Eval vm_compute in (axf Xf2_1Bf XEX2_1Bf).
Lemma AXE2_1Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_1Bf)). Qed.
Definition XR2_1Bf : axst := Eval vm_compute in (XR_of XM2_1Bf).
Definition sX2_1Bf : wsub := Eval vm_compute in (sX_of XR2_1Bf (Wcan 1) UStopLe).
Lemma WXR2_1Bf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_1Bf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_1Bf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_1Bf))). Qed.
Lemma EQR2_1Bf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_1Bf). Qed.
Lemma ENT2_1Bf : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU1A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_1Bf : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q1Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_1Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U1M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_1Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U1M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_1Bf : drain_stmt_1Bf Edr_1Bf.
Proof.
  rewrite Edr_eq_1Bf.
  exact (f0_drain 1%nat QBf CST XGL HCST HXGL HCSTQ Cd_1Bf TQ_1Bf TQr_1Bf sQ_1Bf RQ_1Bf HEQ_1Bf HCK_1Bf HTQ_1Bf HTQr_1Bf QCHK_1Bf QCHKr_1Bf Xf2_1Bf XM2_1Bf XR2_1Bf XEX2_1Bf sX2_1Bf run7_1Bf
           NX7_1Bf RUN7_1Bf L7_1Bf run7r_1Bf NX7r_1Bf RUN7r_1Bf L7r_1Bf AXE2_1Bf WXR2_1Bf DXR2_1Bf NXR2_1Bf EQR2_1Bf ENT2_1Bf SID2_1Bf HCSTF Edr_nf_1Bf XMd_1Bf XKd_1Bf KEPTd_1Bf RESTd_1Bf XEXd_1Bf
           AXEd_1Bf OBJSd_1Bf EQKd_1Bf RCLSd_1Bf RCIVd_1Bf RCELLd_1Bf RWRd_1Bf RSHPd_1Bf ECd_1Bf FBCd_1Bf).
Qed.
Theorem ef0_drain_1Bf : edrain_stmt_1Bf Edr_1Bf.
Proof.
  rewrite Edr_eq_1Bf.
  exact (ef0_drain 1%nat QBf CST XGL HCST HXGL HCSTQ Cd_1Bf TQ_1Bf TQr_1Bf sQ_1Bf RQ_1Bf HEQ_1Bf HCK_1Bf HTQ_1Bf HTQr_1Bf QCHK_1Bf QCHKr_1Bf Xf2_1Bf XM2_1Bf XR2_1Bf XEX2_1Bf sX2_1Bf run7_1Bf
           NX7_1Bf RUN7_1Bf L7_1Bf run7r_1Bf NX7r_1Bf RUN7r_1Bf L7r_1Bf AXE2_1Bf WXR2_1Bf DXR2_1Bf NXR2_1Bf EQR2_1Bf ENT2_1Bf SID2_1Bf HCSTF Edr_nf_1Bf XMd_1Bf XKd_1Bf KEPTd_1Bf RESTd_1Bf XEXd_1Bf
           AXEd_1Bf OBJSd_1Bf EQKd_1Bf RCLSd_1Bf RCIVd_1Bf RCELLd_1Bf RWRd_1Bf RSHPd_1Bf ECd_1Bf FBCd_1Bf).
Qed.
End Q1Bf.
End F0A_q1Bf.

