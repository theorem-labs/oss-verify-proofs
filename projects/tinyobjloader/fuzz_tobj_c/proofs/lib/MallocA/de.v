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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From Stdlib Require NArith PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cn.

(* [comment removed for export] *)
Module F0A_q1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q1A"; "Cd_1A"; "XMd_1A"; "RQ_1A"; "XR2_1A"; "sQ_1A"; "RESTd_1A"; "TQ_1A"; "TQr_1A"; "XKd_1A"; "XM2_1A"; "KEPTd_1A"; "Xf2_1A"; "run7_1A"; "run7r_1A"; "nkd_1A"; "sX2_1A"; "Edr_nf_1A"; "XEX2_1A"; "XEXd_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q1Be"; "Cd_1Be"; "XMd_1Be"; "RQ_1Be"; "XR2_1Be"; "sQ_1Be"; "RESTd_1Be"; "TQ_1Be"; "TQr_1Be"; "XKd_1Be"; "XM2_1Be"; "KEPTd_1Be"; "Xf2_1Be"; "run7_1Be"; "run7r_1Be"; "nkd_1Be"; "sX2_1Be"; "Edr_nf_1Be"; "XEX2_1Be"; "XEXd_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.
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
Module MallocHitTail0E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineMallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9j OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cn.MallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineMallocEi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.DepotCallI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineMallocS5t.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0TE.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S5VCST;R1A2S5S1bR2A2S19F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S6S5VCST;R1A2S1aS1cR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S13VAInv;VW;Vst;VA;VKc;S1PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Theorem emalloc_hit_tail_0_P : ltac2:(tb__ "0|1|
S16S10S0S2S18Q40A1A1S2S4SbSdA2M0A1ScVsegs;S9R3R2R1A5S7S1dG0S3SbSdS14SfVW0;Vst0;A3S12VAInv;VCST;VXGL;R6R5A5A4R2A3S11R6A1S0S8Vsegs;SaVsegs;S17VW0;Vst0;R9R8R7A5SeVW0;Vst0;Z2A3R1R6A5R4A3FrhoX;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc.
  pose proof (depot_call_HDE_0 CST XGL HCST HXGL HCSTD A Kc rho Q HKc) as HD.
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).
  set (nv := bv_unsigned (rw rho 12%positive)).
  apply (espine_s3p_tail 0%nat st0 2 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.
  apply (espine_s4 0%nat st0 2 NXC3_0 s4_ecert_0 (KEEP CST XGL A) A Kc rho tp Q HUS HKc HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  assert (K7 : forall tpY rhoY, etriple segs (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (espine_s7 0%nat st0 2 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 NXC7_0 s7_ecert_0 A' Kc rho' tpY Q HUS HKc Hcnt').
    - intros Hm0 rhoY8.
      apply (espine_s8_gen 0%nat st0 2 (C8 W0 st0 2) (C9 W0 st0 2) (E8a W0 st0 2) (E8b W0 st0 2) CC8ma_0 HCC8ma_0 W8a_0 D8a_0 NX8a_0 s8_0 sd8_0 R8_0 T8_0 He8_0 Hchk8_0 HT8_0 FBC8_0 FBT8_0 ENT8_0 SID8_0 NXC8_0 i8_0 S8s_0 SPL8_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i.s8b_0 sd8b_0 R8b_0 T8b_0 He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0 i9_0 SU_0 SM_0 ENTU_0 SIDU_0 MRG_0 s9m_0 ENTM_0 SIDM_0 NXCC8_0 s8_ecert_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY9 tpY9.
      exact (espine_s9_P 0%nat st0 CST XGL HCST HXGL HCSTM law_die false (C9 W0 st0 2) F9a_nf F9b_nf ECert9a_0 ECert9b_0 NX9_0 FGC_0
               swc_a scells_a hcells_a swc_b scells_b hcells_b s9_a s9_b FH_a_0 FH_b_0 A A' Kc rho rho' (KEEP CST XGL A) tp Posts HPin HW HUS HKc HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (espine_s7p 0%nat st0 2 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 NXC7p_0 s7p_ecert_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY8.
      apply (espine_s8_gen 0%nat st0 2 (C8p W0 st0 2) (C9p W0 st0 2) (E8pa W0 st0 2) (E8pb W0 st0 2) CC8map_0 HCC8map_0 W8ap_0 D8ap_0 NX8ap_0 s8p_0 sd8p_0 R8p_0 T8p_0 He8p_0 Hchk8p_0 HT8p_0 FBC8p_0 FBT8p_0 ENT8p_0 SID8p_0 NXC8p_0 i8p_0 S8sp_0 SPL8p_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i.s8bp_0 sd8bp_0 R8bp_0 T8bp_0 He8bp_0 Hchk8bp_0 HT8bp_0 FBC8bp_0 FBT8bp_0 NXC8bp_0 i9p_0 SUp_0 SMp_0 ENTUp_0 SIDUp_0 MRGp_0 s9mp_0 ENTMp_0 SIDMp_0 NXCC8p_0 s8p_ecert_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY9 tpY9.
      exact (espine_s9_P 0%nat st0 CST XGL HCST HXGL HCSTM law_die true (C9p W0 st0 2) F9pa_nf F9pb_nf ECert9pa_0 ECert9pb_0 NX9p_0 FGCp_0
               swc_pa scells_pa hcells_pa swc_pb scells_pb hcells_pb s9_pa s9_pb FH_pa_0 FH_pb_0 A A' Kc rho rho' (KEEP CST XGL A) tp Posts HPin HW HUS HKc HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }
  assert (K6 : forall tpY rhoY, etriple segs (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (espine_s6 0%nat st0 2 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 NXC6_0 s6_ecert_0 A' Kc rho' tpY Q HUS HKc Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    assert (NXC6m_f : (GW <= ss_next (ax_S (C6m W0 st0 2)))%positive) by (apply Pos.leb_le; vm_cast_no_check (eq_refl true)).
    apply (espine_s6l 0%nat st0 2 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6m_f NXC6l_0 s6l_ecert_0 A' Kc rho' tpY Q HUS HKc).
    intros rhoY6b tpY6b.
    apply (espine_s6b 0%nat st0 2 s7j_0 ENT7j_0 SID7j_0 NXC6b_0 s6b_ecert_0 A' Kc rho' tpY6b Q HUS HKc). exact (K7 tpY6b). }
  apply (espine_s5 0%nat st0 2 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 NXC5_0 s5_ecert_0 A' Kc rho' tp' Q HUS HKc Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (espine_s5b 0%nat st0 2 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0 NXC5b_0 s5b_ecert_0
           A' Kc rho' tp' Q HUS HKc).
  intros rhoX5c.
  apply (espine_s5c 0%nat st0 2 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0 NXC5c_0 s5c_ecert_0
           A' Kc rho' tp' Q HUS HKc Hcnt').
  intros rhoX5d tp5d.
  apply (espine_s5d 0%nat st0 2 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0 NXC5d_0 s5d_ecert_0
           A' Kc rho' tp5d Q HUS HKc Hcnt').
  intros rhoX5e tp5e.
  apply (espine_s5e 0%nat st0 2 s6j_0 ENT6j_0 SID6j_0 NXC5e_0 s5e_ecert_0 A' Kc rho' tp5e Q HUS HKc). exact (K6 tp5e).
Qed.

Theorem emalloc_hit_tail_0 : ltac2:(tb__ "0|0|
S16S10S0S2S18Q40A1A1ScVsegs;S9R2R1S15SfVAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5S7S11R4A1S0S8Vsegs;SaVsegs;S17VW0;Vst0;R7R6R5A5SeVW0;Vst0;Z2A3R1R4A5R3A3FrhoX;F_;TQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp. exact (emalloc_hit_tail_0_P A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0TE.
End MallocHitTail0E.

(* [comment removed for export] *)
Module F0A_q1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q1Bf"; "Cd_1Bf"; "XMd_1Bf"; "RQ_1Bf"; "XR2_1Bf"; "sQ_1Bf"; "RESTd_1Bf"; "TQ_1Bf"; "TQr_1Bf"; "XKd_1Bf"; "XM2_1Bf"; "KEPTd_1Bf"; "Xf2_1Bf"; "run7_1Bf"; "run7r_1Bf"; "nkd_1Bf"; "sX2_1Bf"; "Edr_nf_1Bf"; "XEX2_1Bf"; "XEXd_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf.
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

(* [comment removed for export] *)
Module F0A_q2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q2Be"; "Cd_2Be"; "XMd_2Be"; "RQ_2Be"; "XR2_2Be"; "sQ_2Be"; "RESTd_2Be"; "TQ_2Be"; "TQr_2Be"; "XKd_2Be"; "XM2_2Be"; "KEPTd_2Be"; "Xf2_2Be"; "run7_2Be"; "run7r_2Be"; "nkd_2Be"; "sX2_2Be"; "Edr_nf_2Be"; "XEX2_2Be"; "XEXd_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_2Be : axst := Eval vm_compute in Edr_2Be.
Lemma Edr_eq_2Be : Edr_2Be = Edr_nf_2Be. Proof. vm_cast_no_check (eq_refl Edr_nf_2Be). Qed.

Definition XEXd_2Be : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_2Be))].
Definition XMd_2Be : axst := Eval vm_compute in (axf Edr_nf_2Be XEXd_2Be).
Lemma AXEd_2Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_2Be)). Qed.
Definition nkd_2Be : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_2Be) + 2 + 2)%nat.
Definition KEPTd_2Be : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_2Be : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_2Be : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_2Be : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_2Be : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_2Be : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_2Be : rcivb RESTd_2Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_2Be : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_2Be : rwrb RESTd_2Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_2Be : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_2Be : axst := Eval vm_compute in (ax_with_facts XKd_2Be (ss_facts (ax_S XKd_2Be) ++ [F_cne])).
Lemma ECd_2Be : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_2Be). Qed.
Lemma FBCd_2Be : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_2Be : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_2Be) (ax_S PreQ3)).
Definition RQ_2Be : list sobj := Eval vm_compute in (optR (entails_frA Cd_2Be PreQ3 sQ_2Be)).
Lemma HEQ_2Be : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_2Be)). Qed.
Lemma HCK_2Be : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_2Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_2Be PreQ3 PostQ3 Cd_2Be RQ_2Be) (ss_facts (ax_S Cd_2Be))).
Lemma HTQ_2Be : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_2Be). Qed.
Lemma QCHK_2Be : ltac2:(tb__ "0|0|
S0S7S61U2S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_2Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_2Be PreQ3 PostQ3r Cd_2Be RQ_2Be) (ss_facts (ax_S Cd_2Be))).
Lemma HTQr_2Be : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_2Be). Qed.
Lemma QCHKr_2Be : ltac2:(tb__ "0|0|
S0S7S61U2S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_2Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_2Be).
Lemma RUN7_2Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_2Be). Qed.
Definition Xf2_2Be : axst := Eval vm_compute in (leaf 0 run7_2Be).
Lemma L7_2Be : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_2Be)]. Qed.
Lemma NX7_2Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_2Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_2Be).
Lemma RUN7r_2Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_2Be). Qed.
Lemma L7r_2Be : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_2Be)]. Qed.
Lemma NX7r_2Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_2Be : list axform := Eval vm_compute in (XEX_of Xf2_2Be).
Definition XM2_2Be : axst := Eval vm_compute in (axf Xf2_2Be XEX2_2Be).
Lemma AXE2_2Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_2Be)). Qed.
Definition XR2_2Be : axst := Eval vm_compute in (XR_of XM2_2Be).
Definition sX2_2Be : wsub := Eval vm_compute in (sX_of XR2_2Be (Wcan 2) UStopLe).
Lemma WXR2_2Be : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_2Be : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_2Be : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_2Be))). Qed.
Lemma EQR2_2Be : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_2Be). Qed.
Lemma ENT2_2Be : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU2A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_2Be : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q2Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_2Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U2M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_2Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U2M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_2Be : drain_stmt_2Be Edr_2Be.
Proof.
  rewrite Edr_eq_2Be.
  exact (f0_drain 2%nat QBe CST XGL HCST HXGL HCSTQ Cd_2Be TQ_2Be TQr_2Be sQ_2Be RQ_2Be HEQ_2Be HCK_2Be HTQ_2Be HTQr_2Be QCHK_2Be QCHKr_2Be Xf2_2Be XM2_2Be XR2_2Be XEX2_2Be sX2_2Be run7_2Be
           NX7_2Be RUN7_2Be L7_2Be run7r_2Be NX7r_2Be RUN7r_2Be L7r_2Be AXE2_2Be WXR2_2Be DXR2_2Be NXR2_2Be EQR2_2Be ENT2_2Be SID2_2Be HCSTF Edr_nf_2Be XMd_2Be XKd_2Be KEPTd_2Be RESTd_2Be XEXd_2Be
           AXEd_2Be OBJSd_2Be EQKd_2Be RCLSd_2Be RCIVd_2Be RCELLd_2Be RWRd_2Be RSHPd_2Be ECd_2Be FBCd_2Be).
Qed.
Theorem ef0_drain_2Be : edrain_stmt_2Be Edr_2Be.
Proof.
  rewrite Edr_eq_2Be.
  exact (ef0_drain 2%nat QBe CST XGL HCST HXGL HCSTQ Cd_2Be TQ_2Be TQr_2Be sQ_2Be RQ_2Be HEQ_2Be HCK_2Be HTQ_2Be HTQr_2Be QCHK_2Be QCHKr_2Be Xf2_2Be XM2_2Be XR2_2Be XEX2_2Be sX2_2Be run7_2Be
           NX7_2Be RUN7_2Be L7_2Be run7r_2Be NX7r_2Be RUN7r_2Be L7r_2Be AXE2_2Be WXR2_2Be DXR2_2Be NXR2_2Be EQR2_2Be ENT2_2Be SID2_2Be HCSTF Edr_nf_2Be XMd_2Be XKd_2Be KEPTd_2Be RESTd_2Be XEXd_2Be
           AXEd_2Be OBJSd_2Be EQKd_2Be RCLSd_2Be RCIVd_2Be RCELLd_2Be RWRd_2Be RSHPd_2Be ECd_2Be FBCd_2Be).
Qed.
End Q2Be.
End F0A_q2Be.

(* [comment removed for export] *)
Module F0A_q2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q2A"; "Cd_2A"; "XMd_2A"; "RQ_2A"; "XR2_2A"; "sQ_2A"; "RESTd_2A"; "TQ_2A"; "TQr_2A"; "XKd_2A"; "XM2_2A"; "KEPTd_2A"; "Xf2_2A"; "run7_2A"; "run7r_2A"; "nkd_2A"; "sX2_2A"; "Edr_nf_2A"; "XEX2_2A"; "XEXd_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_2A : axst := Eval vm_compute in Edr_2A.
Lemma Edr_eq_2A : Edr_2A = Edr_nf_2A. Proof. vm_cast_no_check (eq_refl Edr_nf_2A). Qed.

Definition XEXd_2A : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_2A))].
Definition XMd_2A : axst := Eval vm_compute in (axf Edr_nf_2A XEXd_2A).
Lemma AXEd_2A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_2A)). Qed.
Definition nkd_2A : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_2A) + 2 + 2)%nat.
Definition KEPTd_2A : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_2A : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_2A : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_2A : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_2A : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_2A : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_2A : rcivb RESTd_2A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_2A : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_2A : rwrb RESTd_2A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_2A : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_2A : axst := Eval vm_compute in (ax_with_facts XKd_2A (ss_facts (ax_S XKd_2A) ++ [F_cne])).
Lemma ECd_2A : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_2A). Qed.
Lemma FBCd_2A : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_2A : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_2A) (ax_S PreQ3)).
Definition RQ_2A : list sobj := Eval vm_compute in (optR (entails_frA Cd_2A PreQ3 sQ_2A)).
Lemma HEQ_2A : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_2A)). Qed.
Lemma HCK_2A : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_2A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_2A PreQ3 PostQ3 Cd_2A RQ_2A) (ss_facts (ax_S Cd_2A))).
Lemma HTQ_2A : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_2A). Qed.
Lemma QCHK_2A : ltac2:(tb__ "0|0|
S0S7S61U2S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_2A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_2A PreQ3 PostQ3r Cd_2A RQ_2A) (ss_facts (ax_S Cd_2A))).
Lemma HTQr_2A : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_2A). Qed.
Lemma QCHKr_2A : ltac2:(tb__ "0|0|
S0S7S61U2S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_2A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_2A).
Lemma RUN7_2A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_2A). Qed.
Definition Xf2_2A : axst := Eval vm_compute in (leaf 0 run7_2A).
Lemma L7_2A : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_2A)]. Qed.
Lemma NX7_2A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_2A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_2A).
Lemma RUN7r_2A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_2A). Qed.
Lemma L7r_2A : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_2A)]. Qed.
Lemma NX7r_2A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_2A : list axform := Eval vm_compute in (XEX_of Xf2_2A).
Definition XM2_2A : axst := Eval vm_compute in (axf Xf2_2A XEX2_2A).
Lemma AXE2_2A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_2A)). Qed.
Definition XR2_2A : axst := Eval vm_compute in (XR_of XM2_2A).
Definition sX2_2A : wsub := Eval vm_compute in (sX_of XR2_2A (Wcan 2) UStopLe).
Lemma WXR2_2A : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_2A : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_2A : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_2A))). Qed.
Lemma EQR2_2A : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_2A). Qed.
Lemma ENT2_2A : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU2A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_2A : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q2A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_2A (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U2M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_2A (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U2M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_2A : drain_stmt_2A Edr_2A.
Proof.
  rewrite Edr_eq_2A.
  exact (f0_drain 2%nat QA CST XGL HCST HXGL HCSTQ Cd_2A TQ_2A TQr_2A sQ_2A RQ_2A HEQ_2A HCK_2A HTQ_2A HTQr_2A QCHK_2A QCHKr_2A Xf2_2A XM2_2A XR2_2A XEX2_2A sX2_2A run7_2A
           NX7_2A RUN7_2A L7_2A run7r_2A NX7r_2A RUN7r_2A L7r_2A AXE2_2A WXR2_2A DXR2_2A NXR2_2A EQR2_2A ENT2_2A SID2_2A HCSTF Edr_nf_2A XMd_2A XKd_2A KEPTd_2A RESTd_2A XEXd_2A
           AXEd_2A OBJSd_2A EQKd_2A RCLSd_2A RCIVd_2A RCELLd_2A RWRd_2A RSHPd_2A ECd_2A FBCd_2A).
Qed.
Theorem ef0_drain_2A : edrain_stmt_2A Edr_2A.
Proof.
  rewrite Edr_eq_2A.
  exact (ef0_drain 2%nat QA CST XGL HCST HXGL HCSTQ Cd_2A TQ_2A TQr_2A sQ_2A RQ_2A HEQ_2A HCK_2A HTQ_2A HTQr_2A QCHK_2A QCHKr_2A Xf2_2A XM2_2A XR2_2A XEX2_2A sX2_2A run7_2A
           NX7_2A RUN7_2A L7_2A run7r_2A NX7r_2A RUN7r_2A L7r_2A AXE2_2A WXR2_2A DXR2_2A NXR2_2A EQR2_2A ENT2_2A SID2_2A HCSTF Edr_nf_2A XMd_2A XKd_2A KEPTd_2A RESTd_2A XEXd_2A
           AXEd_2A OBJSd_2A EQKd_2A RCLSd_2A RCIVd_2A RCELLd_2A RWRd_2A RSHPd_2A ECd_2A FBCd_2A).
Qed.
End Q2A.
End F0A_q2A.

