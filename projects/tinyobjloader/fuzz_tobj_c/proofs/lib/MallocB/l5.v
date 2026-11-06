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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km j2.

(* [comment removed for export] *)
Module F0T_qLTA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTA"; "Cd_LTA"; "XMd_LTA"; "RQ_LTA"; "XR2_LTA"; "sQ_LTA"; "RESTd_LTA"; "TQ_LTA"; "TQr_LTA"; "XKd_LTA"; "XM2_LTA"; "KEPTd_LTA"; "Xf2_LTA"; "run7_LTA"; "run7r_LTA"; "nkd_LTA"; "sX2_LTA"; "Edr_nf_LTA"; "XEX2_LTA"; "XEXd_LTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_LTA : axst := Eval vm_compute in Edr_LTA.
Lemma Edr_eq_LTA : Edr_LTA = Edr_nf_LTA. Proof. vm_cast_no_check (eq_refl Edr_nf_LTA). Qed.

Definition XEXd_LTA : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_LTA))].
Definition XMd_LTA : axst := Eval vm_compute in (axf Edr_nf_LTA XEXd_LTA).
Lemma AXEd_LTA : ltac2:(tb__ "0|0|
S0S10S12A1S5cS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_LTA)). Qed.
Definition nkd_LTA : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_LTA) + 0 + 2)%nat.
Definition KEPTd_LTA : list sobj := ltac2:(tb__ "0|0|
S6dS19S32S1eS13S25A1A1A3").
Definition RESTd_LTA : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Lemma OBJSd_LTA : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_LTA : axst := ltac2:(tb__ "0|0|
S14S25S58S13S25A1S2eA2A2").
Lemma EQKd_LTA : ltac2:(tb__ "0|0|
S0S12S14S25S58S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_LTA : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_LTA : rcivb RESTd_LTA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_LTA : ltac2:(tb__ "0|0|
S0S7S76S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_LTA : rwrb RESTd_LTA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_LTA : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_LTA : axst := Eval vm_compute in (ax_with_facts XKd_LTA (ss_facts (ax_S XKd_LTA) ++ [F_cne])).
Lemma ECd_LTA : ltac2:(tb__ "0|0|
S0S12S24S4dS2cS11S17S1cS13S2cA1A1S9S17S62SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_LTA). Qed.
Lemma FBCd_LTA : ltac2:(tb__ "0|1|
S0S7S6bS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S62SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_LTA : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_LTA) (ax_S PreQ3)).
Definition RQ_LTA : list sobj := Eval vm_compute in (optR (entails_frA Cd_LTA PreQ3 sQ_LTA)).
Lemma HEQ_LTA : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S3fS24S48S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_LTA)). Qed.
Lemma HCK_LTA : ltac2:(tb__ "0|0|
S0S7S3eS24S48S28S26S9S12S49S9S12S57SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_LTA : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_LTA PreQ3 PostQ3 Cd_LTA RQ_LTA) (ss_facts (ax_S Cd_LTA))).
Lemma HTQ_LTA : ltac2:(tb__ "0|0|
S0S12S2aS4dS3dS28S48S49S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_LTA). Qed.
Lemma QCHK_LTA : ltac2:(tb__ "0|0|
S0S7S63U0S24S49S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_LTA : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_LTA PreQ3 PostQ3r Cd_LTA RQ_LTA) (ss_facts (ax_S Cd_LTA))).
Lemma HTQr_LTA : ltac2:(tb__ "0|0|
S0S12S2bS4dS3dS28S48S57S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_LTA). Qed.
Lemma QCHKr_LTA : ltac2:(tb__ "0|0|
S0S7S63U0S24S57S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_LTA : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_LTA).
Lemma RUN7_LTA : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_LTA). Qed.
Definition Xf2_LTA : axst := Eval vm_compute in (leaf 0 run7_LTA).
Lemma L7_LTA : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S67U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_LTA)]. Qed.
Lemma NX7_LTA : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_LTA : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_LTA).
Lemma RUN7r_LTA : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_LTA). Qed.
Lemma L7r_LTA : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S67U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_LTA)]. Qed.
Lemma NX7r_LTA : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_LTA : list axform := Eval vm_compute in (XEX_of Xf2_LTA).
Definition XM2_LTA : axst := Eval vm_compute in (axf Xf2_LTA XEX2_LTA).
Lemma AXE2_LTA : ltac2:(tb__ "0|0|
S0S10S12A1S5cS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_LTA)). Qed.
Definition XR2_LTA : axst := Eval vm_compute in (XR_of XM2_LTA).
Definition sX2_LTA : wsub := Eval vm_compute in (infer_sub NF (ax_S XR2_LTA) (ax_S (L_free_tol AE_A))).
Lemma WXR2_LTA : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_LTA : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S72S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S74A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_LTA : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_LTA))). Qed.
Lemma EQR2_LTA : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_LTA). Qed.
Lemma ENT2_LTA : ltac2:(tb__ "0|0|
S0S7S16S27S55S4eA1S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_LTA : ltac2:(tb__ "0|0|
S0S7S73S33S4cA2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QLTA.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S4S7bR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S2S56S75R2A2S1S7cS79R2A2S7dR2S7aA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_LTA (E : axst) : Prop := ltac2:(tb__ "0|3|
S71OF_;S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S5bVsegs;RbS5aR9A1A3S64RcRaA2S47RcA1S0S5S4aG0S1bRbPcA2A2R9A3S0S5S4aG0S1bRcPdA2A2R9A3S6aSdS5S5A2ScS5S5RbRaA4S46RfA1A3S5eRcRbA2S0S7S45R11A1S8A3S43S37R12A2S61R11S40R13R11RfReRdRcA6A2S0S5S41RdA1S66A3S5S2S53VCST;R16R1A3S54VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S44S18S18G1S60R1aR4A2S69R13S40R1bR19R17R16R15R14A6R4A3S70Vsegs;R1dS59Vsegs;S5fU0S52SfR6R1bR5A6VE;R4R3A5S3cVsegs;S4cR1aR19S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1cR1bA5A4SaG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_LTA (E : axst) : Prop := ltac2:(tb__ "0|3|
S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S65R9A1S47RbA1S0S5S4aG0S1bRaPcA2A2R8A3S0S5S4aG0S1bRbPdA2A2R8A3S6aSdS5S5A2ScS5S5RaR9A4S46ReA1A3S5eRbRaA2S0S7S45R10A1S8A3S43S37R11A2S61R10S40R12R10ReRdRcRbA6A2S0S5S41RcA1S66A3S5S2S53VCST;R15R1A3S54VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S44S18S18G1S60R19R4A2S69R12S40R1aR18R16R15R14R13A6R4A3S6fVsegs;S59Vsegs;S5fU0S52SfR6R1aR5A6VE;R4R3A5S3cVsegs;S4cR19R18S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1bR1aA5A4SaG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_LTA : drain_stmt_LTA Edr_LTA.
Proof.
  rewrite Edr_eq_LTA.
  exact (f0_drain QA CST XGL HCST HXGL HCSTQ Cd_LTA TQ_LTA TQr_LTA sQ_LTA RQ_LTA HEQ_LTA HCK_LTA HTQ_LTA HTQr_LTA QCHK_LTA QCHKr_LTA Xf2_LTA XM2_LTA XR2_LTA XEX2_LTA sX2_LTA run7_LTA
           NX7_LTA RUN7_LTA L7_LTA run7r_LTA NX7r_LTA RUN7r_LTA L7r_LTA AXE2_LTA WXR2_LTA DXR2_LTA NXR2_LTA EQR2_LTA ENT2_LTA SID2_LTA HCSTF Edr_nf_LTA XMd_LTA XKd_LTA KEPTd_LTA RESTd_LTA XEXd_LTA
           AXEd_LTA OBJSd_LTA EQKd_LTA RCLSd_LTA RCIVd_LTA RCELLd_LTA RWRd_LTA RSHPd_LTA ECd_LTA FBCd_LTA).
Qed.
Theorem ef0_drain_LTA : edrain_stmt_LTA Edr_LTA.
Proof.
  rewrite Edr_eq_LTA.
  exact (ef0_drain QA CST XGL HCST HXGL HCSTQ Cd_LTA TQ_LTA TQr_LTA sQ_LTA RQ_LTA HEQ_LTA HCK_LTA HTQ_LTA HTQr_LTA QCHK_LTA QCHKr_LTA Xf2_LTA XM2_LTA XR2_LTA XEX2_LTA sX2_LTA run7_LTA
           NX7_LTA RUN7_LTA L7_LTA run7r_LTA NX7r_LTA RUN7r_LTA L7r_LTA AXE2_LTA WXR2_LTA DXR2_LTA NXR2_LTA EQR2_LTA ENT2_LTA SID2_LTA HCSTF Edr_nf_LTA XMd_LTA XKd_LTA KEPTd_LTA RESTd_LTA XEXd_LTA
           AXEd_LTA OBJSd_LTA EQKd_LTA RCLSd_LTA RCIVd_LTA RCELLd_LTA RWRd_LTA RSHPd_LTA ECd_LTA FBCd_LTA).
Qed.
End QLTA.
End F0T_qLTA.

(* [comment removed for export] *)
Module F0T_qLTBe.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBe"; "Cd_LTBe"; "XMd_LTBe"; "RQ_LTBe"; "XR2_LTBe"; "sQ_LTBe"; "RESTd_LTBe"; "TQ_LTBe"; "TQr_LTBe"; "XKd_LTBe"; "XM2_LTBe"; "KEPTd_LTBe"; "Xf2_LTBe"; "run7_LTBe"; "run7r_LTBe"; "nkd_LTBe"; "sX2_LTBe"; "Edr_nf_LTBe"; "XEX2_LTBe"; "XEXd_LTBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild";
"IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_LTBe : axst := Eval vm_compute in Edr_LTBe.
Lemma Edr_eq_LTBe : Edr_LTBe = Edr_nf_LTBe. Proof. vm_cast_no_check (eq_refl Edr_nf_LTBe). Qed.

Definition XEXd_LTBe : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_LTBe))].
Definition XMd_LTBe : axst := Eval vm_compute in (axf Edr_nf_LTBe XEXd_LTBe).
Lemma AXEd_LTBe : ltac2:(tb__ "0|0|
S0S10S12A1S5cS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_LTBe)). Qed.
Definition nkd_LTBe : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_LTBe) + 0 + 2)%nat.
Definition KEPTd_LTBe : list sobj := ltac2:(tb__ "0|0|
S6dS19S32S1eS13S25A1A1A3").
Definition RESTd_LTBe : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Lemma OBJSd_LTBe : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_LTBe : axst := ltac2:(tb__ "0|0|
S14S25S58S13S25A1S2eA2A2").
Lemma EQKd_LTBe : ltac2:(tb__ "0|0|
S0S12S14S25S58S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_LTBe : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_LTBe : rcivb RESTd_LTBe = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_LTBe : ltac2:(tb__ "0|0|
S0S7S76S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_LTBe : rwrb RESTd_LTBe = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_LTBe : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_LTBe : axst := Eval vm_compute in (ax_with_facts XKd_LTBe (ss_facts (ax_S XKd_LTBe) ++ [F_cne])).
Lemma ECd_LTBe : ltac2:(tb__ "0|0|
S0S12S24S4dS2cS11S17S1cS13S2cA1A1S9S17S62SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_LTBe). Qed.
Lemma FBCd_LTBe : ltac2:(tb__ "0|1|
S0S7S6bS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S62SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_LTBe : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_LTBe) (ax_S PreQ3)).
Definition RQ_LTBe : list sobj := Eval vm_compute in (optR (entails_frA Cd_LTBe PreQ3 sQ_LTBe)).
Lemma HEQ_LTBe : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S3fS24S48S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_LTBe)). Qed.
Lemma HCK_LTBe : ltac2:(tb__ "0|0|
S0S7S3eS24S48S28S26S9S12S49S9S12S57SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_LTBe : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_LTBe PreQ3 PostQ3 Cd_LTBe RQ_LTBe) (ss_facts (ax_S Cd_LTBe))).
Lemma HTQ_LTBe : ltac2:(tb__ "0|0|
S0S12S2aS4dS3dS28S48S49S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_LTBe). Qed.
Lemma QCHK_LTBe : ltac2:(tb__ "0|0|
S0S7S63U0S24S49S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_LTBe : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_LTBe PreQ3 PostQ3r Cd_LTBe RQ_LTBe) (ss_facts (ax_S Cd_LTBe))).
Lemma HTQr_LTBe : ltac2:(tb__ "0|0|
S0S12S2bS4dS3dS28S48S57S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_LTBe). Qed.
Lemma QCHKr_LTBe : ltac2:(tb__ "0|0|
S0S7S63U0S24S57S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_LTBe : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_LTBe).
Lemma RUN7_LTBe : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_LTBe). Qed.
Definition Xf2_LTBe : axst := Eval vm_compute in (leaf 0 run7_LTBe).
Lemma L7_LTBe : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S67U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_LTBe)]. Qed.
Lemma NX7_LTBe : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_LTBe : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_LTBe).
Lemma RUN7r_LTBe : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_LTBe). Qed.
Lemma L7r_LTBe : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S67U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_LTBe)]. Qed.
Lemma NX7r_LTBe : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_LTBe : list axform := Eval vm_compute in (XEX_of Xf2_LTBe).
Definition XM2_LTBe : axst := Eval vm_compute in (axf Xf2_LTBe XEX2_LTBe).
Lemma AXE2_LTBe : ltac2:(tb__ "0|0|
S0S10S12A1S5cS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_LTBe)). Qed.
Definition XR2_LTBe : axst := Eval vm_compute in (XR_of XM2_LTBe).
Definition sX2_LTBe : wsub := Eval vm_compute in (infer_sub NF (ax_S XR2_LTBe) (ax_S (L_free_tol AE_A))).
Lemma WXR2_LTBe : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_LTBe : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S72S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S74A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_LTBe : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_LTBe))). Qed.
Lemma EQR2_LTBe : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_LTBe). Qed.
Lemma ENT2_LTBe : ltac2:(tb__ "0|0|
S0S7S16S27S55S4eA1S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_LTBe : ltac2:(tb__ "0|0|
S0S7S73S33S4cA2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QLTBe.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S4S7bR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S2S56S75R2A2S1S7cS79R2A2S7dR2S7aA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_LTBe (E : axst) : Prop := ltac2:(tb__ "0|3|
S71OF_;S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S5bVsegs;RbS5aR9A1A3S64RcRaA2S47RcA1S0S5S4aG0S1bRbPcA2A2R9A3S0S5S4aG0S1bRcPdA2A2R9A3S6aSdS5S5A2ScS5S5RbRaA4S46RfA1A3S5eRcRbA2S0S7S45R11A1S8A3S43S37R12A2S61R11S40R13R11RfReRdRcA6A2S0S5S41RdA1S66A3S5S2S53VCST;R16R1A3S54VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S44S18S18G1S60R1aR4A2S69R13S40R1bR19R17R16R15R14A6R4A3S70Vsegs;R1dS59Vsegs;S5fU0S52SfR6R1bR5A6VE;R4R3A5S3cVsegs;S4cR1aR19S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1cR1bA5A4SaG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_LTBe (E : axst) : Prop := ltac2:(tb__ "0|3|
S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S65R9A1S47RbA1S0S5S4aG0S1bRaPcA2A2R8A3S0S5S4aG0S1bRbPdA2A2R8A3S6aSdS5S5A2ScS5S5RaR9A4S46ReA1A3S5eRbRaA2S0S7S45R10A1S8A3S43S37R11A2S61R10S40R12R10ReRdRcRbA6A2S0S5S41RcA1S66A3S5S2S53VCST;R15R1A3S54VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S44S18S18G1S60R19R4A2S69R12S40R1aR18R16R15R14R13A6R4A3S6fVsegs;S59Vsegs;S5fU0S52SfR6R1aR5A6VE;R4R3A5S3cVsegs;S4cR19R18S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1bR1aA5A4SaG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_LTBe : drain_stmt_LTBe Edr_LTBe.
Proof.
  rewrite Edr_eq_LTBe.
  exact (f0_drain QBe CST XGL HCST HXGL HCSTQ Cd_LTBe TQ_LTBe TQr_LTBe sQ_LTBe RQ_LTBe HEQ_LTBe HCK_LTBe HTQ_LTBe HTQr_LTBe QCHK_LTBe QCHKr_LTBe Xf2_LTBe XM2_LTBe XR2_LTBe XEX2_LTBe sX2_LTBe run7_LTBe
           NX7_LTBe RUN7_LTBe L7_LTBe run7r_LTBe NX7r_LTBe RUN7r_LTBe L7r_LTBe AXE2_LTBe WXR2_LTBe DXR2_LTBe NXR2_LTBe EQR2_LTBe ENT2_LTBe SID2_LTBe HCSTF Edr_nf_LTBe XMd_LTBe XKd_LTBe KEPTd_LTBe RESTd_LTBe XEXd_LTBe
           AXEd_LTBe OBJSd_LTBe EQKd_LTBe RCLSd_LTBe RCIVd_LTBe RCELLd_LTBe RWRd_LTBe RSHPd_LTBe ECd_LTBe FBCd_LTBe).
Qed.
Theorem ef0_drain_LTBe : edrain_stmt_LTBe Edr_LTBe.
Proof.
  rewrite Edr_eq_LTBe.
  exact (ef0_drain QBe CST XGL HCST HXGL HCSTQ Cd_LTBe TQ_LTBe TQr_LTBe sQ_LTBe RQ_LTBe HEQ_LTBe HCK_LTBe HTQ_LTBe HTQr_LTBe QCHK_LTBe QCHKr_LTBe Xf2_LTBe XM2_LTBe XR2_LTBe XEX2_LTBe sX2_LTBe run7_LTBe
           NX7_LTBe RUN7_LTBe L7_LTBe run7r_LTBe NX7r_LTBe RUN7r_LTBe L7r_LTBe AXE2_LTBe WXR2_LTBe DXR2_LTBe NXR2_LTBe EQR2_LTBe ENT2_LTBe SID2_LTBe HCSTF Edr_nf_LTBe XMd_LTBe XKd_LTBe KEPTd_LTBe RESTd_LTBe XEXd_LTBe
           AXEd_LTBe OBJSd_LTBe EQKd_LTBe RCLSd_LTBe RCIVd_LTBe RCELLd_LTBe RWRd_LTBe RSHPd_LTBe ECd_LTBe FBCd_LTBe).
Qed.
End QLTBe.
End F0T_qLTBe.

(* [comment removed for export] *)
Module F0T_qLTBf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBf"; "Cd_LTBf"; "XMd_LTBf"; "RQ_LTBf"; "XR2_LTBf"; "sQ_LTBf"; "RESTd_LTBf"; "TQ_LTBf"; "TQr_LTBf"; "XKd_LTBf"; "XM2_LTBf"; "KEPTd_LTBf"; "Xf2_LTBf"; "run7_LTBf"; "run7r_LTBf"; "nkd_LTBf"; "sX2_LTBf"; "Edr_nf_LTBf"; "XEX2_LTBf"; "XEXd_LTBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild";
"IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_LTBf : axst := Eval vm_compute in Edr_LTBf.
Lemma Edr_eq_LTBf : Edr_LTBf = Edr_nf_LTBf. Proof. vm_cast_no_check (eq_refl Edr_nf_LTBf). Qed.

Definition XEXd_LTBf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_LTBf))].
Definition XMd_LTBf : axst := Eval vm_compute in (axf Edr_nf_LTBf XEXd_LTBf).
Lemma AXEd_LTBf : ltac2:(tb__ "0|0|
S0S10S12A1S5cS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_LTBf)). Qed.
Definition nkd_LTBf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_LTBf) + 0 + 2)%nat.
Definition KEPTd_LTBf : list sobj := ltac2:(tb__ "0|0|
S6dS19S32S1eS13S25A1A1A3").
Definition RESTd_LTBf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Lemma OBJSd_LTBf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_LTBf : axst := ltac2:(tb__ "0|0|
S14S25S58S13S25A1S2eA2A2").
Lemma EQKd_LTBf : ltac2:(tb__ "0|0|
S0S12S14S25S58S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_LTBf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_LTBf : rcivb RESTd_LTBf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_LTBf : ltac2:(tb__ "0|0|
S0S7S76S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_LTBf : rwrb RESTd_LTBf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_LTBf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_LTBf : axst := Eval vm_compute in (ax_with_facts XKd_LTBf (ss_facts (ax_S XKd_LTBf) ++ [F_cne])).
Lemma ECd_LTBf : ltac2:(tb__ "0|0|
S0S12S24S4dS2cS11S17S1cS13S2cA1A1S9S17S62SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_LTBf). Qed.
Lemma FBCd_LTBf : ltac2:(tb__ "0|1|
S0S7S6bS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S62SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_LTBf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_LTBf) (ax_S PreQ3)).
Definition RQ_LTBf : list sobj := Eval vm_compute in (optR (entails_frA Cd_LTBf PreQ3 sQ_LTBf)).
Lemma HEQ_LTBf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S3fS24S48S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_LTBf)). Qed.
Lemma HCK_LTBf : ltac2:(tb__ "0|0|
S0S7S3eS24S48S28S26S9S12S49S9S12S57SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_LTBf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_LTBf PreQ3 PostQ3 Cd_LTBf RQ_LTBf) (ss_facts (ax_S Cd_LTBf))).
Lemma HTQ_LTBf : ltac2:(tb__ "0|0|
S0S12S2aS4dS3dS28S48S49S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_LTBf). Qed.
Lemma QCHK_LTBf : ltac2:(tb__ "0|0|
S0S7S63U0S24S49S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_LTBf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_LTBf PreQ3 PostQ3r Cd_LTBf RQ_LTBf) (ss_facts (ax_S Cd_LTBf))).
Lemma HTQr_LTBf : ltac2:(tb__ "0|0|
S0S12S2bS4dS3dS28S48S57S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_LTBf). Qed.
Lemma QCHKr_LTBf : ltac2:(tb__ "0|0|
S0S7S63U0S24S57S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_LTBf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_LTBf).
Lemma RUN7_LTBf : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_LTBf). Qed.
Definition Xf2_LTBf : axst := Eval vm_compute in (leaf 0 run7_LTBf).
Lemma L7_LTBf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S67U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_LTBf)]. Qed.
Lemma NX7_LTBf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_LTBf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_LTBf).
Lemma RUN7r_LTBf : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_LTBf). Qed.
Lemma L7r_LTBf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S67U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_LTBf)]. Qed.
Lemma NX7r_LTBf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_LTBf : list axform := Eval vm_compute in (XEX_of Xf2_LTBf).
Definition XM2_LTBf : axst := Eval vm_compute in (axf Xf2_LTBf XEX2_LTBf).
Lemma AXE2_LTBf : ltac2:(tb__ "0|0|
S0S10S12A1S5cS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_LTBf)). Qed.
Definition XR2_LTBf : axst := Eval vm_compute in (XR_of XM2_LTBf).
Definition sX2_LTBf : wsub := Eval vm_compute in (infer_sub NF (ax_S XR2_LTBf) (ax_S (L_free_tol AE_A))).
Lemma WXR2_LTBf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_LTBf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S72S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S74A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_LTBf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_LTBf))). Qed.
Lemma EQR2_LTBf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_LTBf). Qed.
Lemma ENT2_LTBf : ltac2:(tb__ "0|0|
S0S7S16S27S55S4eA1S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_LTBf : ltac2:(tb__ "0|0|
S0S7S73S33S4cA2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QLTBf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S4S7bR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S2S56S75R2A2S1S7cS79R2A2S7dR2S7aA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_LTBf (E : axst) : Prop := ltac2:(tb__ "0|3|
S71OF_;S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S5bVsegs;RbS5aR9A1A3S64RcRaA2S47RcA1S0S5S4aG0S1bRbPcA2A2R9A3S0S5S4aG0S1bRcPdA2A2R9A3S6aSdS5S5A2ScS5S5RbRaA4S46RfA1A3S5eRcRbA2S0S7S45R11A1S8A3S43S37R12A2S61R11S40R13R11RfReRdRcA6A2S0S5S41RdA1S66A3S5S2S53VCST;R16R1A3S54VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S44S18S18G1S60R1aR4A2S69R13S40R1bR19R17R16R15R14A6R4A3S70Vsegs;R1dS59Vsegs;S5fU0S52SfR6R1bR5A6VE;R4R3A5S3cVsegs;S4cR1aR19S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1cR1bA5A4SaG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_LTBf (E : axst) : Prop := ltac2:(tb__ "0|3|
S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S65R9A1S47RbA1S0S5S4aG0S1bRaPcA2A2R8A3S0S5S4aG0S1bRbPdA2A2R8A3S6aSdS5S5A2ScS5S5RaR9A4S46ReA1A3S5eRbRaA2S0S7S45R10A1S8A3S43S37R11A2S61R10S40R12R10ReRdRcRbA6A2S0S5S41RcA1S66A3S5S2S53VCST;R15R1A3S54VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S44S18S18G1S60R19R4A2S69R12S40R1aR18R16R15R14R13A6R4A3S6fVsegs;S59Vsegs;S5fU0S52SfR6R1aR5A6VE;R4R3A5S3cVsegs;S4cR19R18S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1bR1aA5A4SaG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_LTBf : drain_stmt_LTBf Edr_LTBf.
Proof.
  rewrite Edr_eq_LTBf.
  exact (f0_drain QBf CST XGL HCST HXGL HCSTQ Cd_LTBf TQ_LTBf TQr_LTBf sQ_LTBf RQ_LTBf HEQ_LTBf HCK_LTBf HTQ_LTBf HTQr_LTBf QCHK_LTBf QCHKr_LTBf Xf2_LTBf XM2_LTBf XR2_LTBf XEX2_LTBf sX2_LTBf run7_LTBf
           NX7_LTBf RUN7_LTBf L7_LTBf run7r_LTBf NX7r_LTBf RUN7r_LTBf L7r_LTBf AXE2_LTBf WXR2_LTBf DXR2_LTBf NXR2_LTBf EQR2_LTBf ENT2_LTBf SID2_LTBf HCSTF Edr_nf_LTBf XMd_LTBf XKd_LTBf KEPTd_LTBf RESTd_LTBf XEXd_LTBf
           AXEd_LTBf OBJSd_LTBf EQKd_LTBf RCLSd_LTBf RCIVd_LTBf RCELLd_LTBf RWRd_LTBf RSHPd_LTBf ECd_LTBf FBCd_LTBf).
Qed.
Theorem ef0_drain_LTBf : edrain_stmt_LTBf Edr_LTBf.
Proof.
  rewrite Edr_eq_LTBf.
  exact (ef0_drain QBf CST XGL HCST HXGL HCSTQ Cd_LTBf TQ_LTBf TQr_LTBf sQ_LTBf RQ_LTBf HEQ_LTBf HCK_LTBf HTQ_LTBf HTQr_LTBf QCHK_LTBf QCHKr_LTBf Xf2_LTBf XM2_LTBf XR2_LTBf XEX2_LTBf sX2_LTBf run7_LTBf
           NX7_LTBf RUN7_LTBf L7_LTBf run7r_LTBf NX7r_LTBf RUN7r_LTBf L7r_LTBf AXE2_LTBf WXR2_LTBf DXR2_LTBf NXR2_LTBf EQR2_LTBf ENT2_LTBf SID2_LTBf HCSTF Edr_nf_LTBf XMd_LTBf XKd_LTBf KEPTd_LTBf RESTd_LTBf XEXd_LTBf
           AXEd_LTBf OBJSd_LTBf EQKd_LTBf RCLSd_LTBf RCIVd_LTBf RCELLd_LTBf RWRd_LTBf RSHPd_LTBf ECd_LTBf FBCd_LTBf).
Qed.
End QLTBf.
End F0T_qLTBf.

(* [comment removed for export] *)
Module F0T_qTA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTA"; "Cd_TA"; "XMd_TA"; "RQ_TA"; "XR2_TA"; "sQ_TA"; "RESTd_TA"; "TQ_TA"; "TQr_TA"; "XKd_TA"; "XM2_TA"; "KEPTd_TA"; "Xf2_TA"; "run7_TA"; "run7r_TA"; "nkd_TA"; "sX2_TA"; "Edr_nf_TA"; "XEX2_TA"; "XEXd_TA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_TA : axst := Eval vm_compute in Edr_TA.
Lemma Edr_eq_TA : Edr_TA = Edr_nf_TA. Proof. vm_cast_no_check (eq_refl Edr_nf_TA). Qed.

Definition XEXd_TA : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_TA))].
Definition XMd_TA : axst := Eval vm_compute in (axf Edr_nf_TA XEXd_TA).
Lemma AXEd_TA : ltac2:(tb__ "0|0|
S0S10S12A1S5cS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_TA)). Qed.
Definition nkd_TA : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_TA) + 0 + 2)%nat.
Definition KEPTd_TA : list sobj := ltac2:(tb__ "0|0|
S6dS19S32S1eS13S25A1A1A3").
Definition RESTd_TA : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Lemma OBJSd_TA : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_TA : axst := ltac2:(tb__ "0|0|
S14S25S58S13S25A1S2eA2A2").
Lemma EQKd_TA : ltac2:(tb__ "0|0|
S0S12S14S25S58S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_TA : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_TA : rcivb RESTd_TA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_TA : ltac2:(tb__ "0|0|
S0S7S76S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_TA : rwrb RESTd_TA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_TA : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_TA : axst := Eval vm_compute in (ax_with_facts XKd_TA (ss_facts (ax_S XKd_TA) ++ [F_cne])).
Lemma ECd_TA : ltac2:(tb__ "0|0|
S0S12S24S4dS2cS11S17S1cS13S2cA1A1S9S17S62SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_TA). Qed.
Lemma FBCd_TA : ltac2:(tb__ "0|1|
S0S7S6bS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S62SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_TA : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_TA) (ax_S PreQ3)).
Definition RQ_TA : list sobj := Eval vm_compute in (optR (entails_frA Cd_TA PreQ3 sQ_TA)).
Lemma HEQ_TA : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S3fS24S48S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_TA)). Qed.
Lemma HCK_TA : ltac2:(tb__ "0|0|
S0S7S3eS24S48S28S26S9S12S49S9S12S57SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_TA : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_TA PreQ3 PostQ3 Cd_TA RQ_TA) (ss_facts (ax_S Cd_TA))).
Lemma HTQ_TA : ltac2:(tb__ "0|0|
S0S12S2aS4dS3dS28S48S49S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_TA). Qed.
Lemma QCHK_TA : ltac2:(tb__ "0|0|
S0S7S63U0S24S49S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_TA : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_TA PreQ3 PostQ3r Cd_TA RQ_TA) (ss_facts (ax_S Cd_TA))).
Lemma HTQr_TA : ltac2:(tb__ "0|0|
S0S12S2bS4dS3dS28S48S57S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_TA). Qed.
Lemma QCHKr_TA : ltac2:(tb__ "0|0|
S0S7S63U0S24S57S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_TA : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_TA).
Lemma RUN7_TA : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_TA). Qed.
Definition Xf2_TA : axst := Eval vm_compute in (leaf 0 run7_TA).
Lemma L7_TA : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S67U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_TA)]. Qed.
Lemma NX7_TA : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_TA : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_TA).
Lemma RUN7r_TA : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_TA). Qed.
Lemma L7r_TA : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S67U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_TA)]. Qed.
Lemma NX7r_TA : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_TA : list axform := Eval vm_compute in (XEX_of Xf2_TA).
Definition XM2_TA : axst := Eval vm_compute in (axf Xf2_TA XEX2_TA).
Lemma AXE2_TA : ltac2:(tb__ "0|0|
S0S10S12A1S5cS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_TA)). Qed.
Definition XR2_TA : axst := Eval vm_compute in (XR_of XM2_TA).
Definition sX2_TA : wsub := Eval vm_compute in (infer_sub NF (ax_S XR2_TA) (ax_S (L_free_tol AE_A))).
Lemma WXR2_TA : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_TA : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S72S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S74A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_TA : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_TA))). Qed.
Lemma EQR2_TA : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_TA). Qed.
Lemma ENT2_TA : ltac2:(tb__ "0|0|
S0S7S16S27S55S4eA1S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_TA : ltac2:(tb__ "0|0|
S0S7S73S33S4cA2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QTA.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S4S7bR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S2S56S75R2A2S1S7cS79R2A2S7dR2S7aA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_TA (E : axst) : Prop := ltac2:(tb__ "0|3|
S71OF_;S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S5bVsegs;RbS5aR9A1A3S64RcRaA2S47RcA1S0S5S4aG0S1bRbPcA2A2R9A3S0S5S4aG0S1bRcPdA2A2R9A3S6aSdS5S5A2ScS5S5RbRaA4S46RfA1A3S5eRcRbA2S0S7S45R11A1S8A3S43S37R12A2S61R11S40R13R11RfReRdRcA6A2S0S5S41RdA1S66A3S5S2S53VCST;R16R1A3S54VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S44S18S18G1S60R1aR4A2S69R13S40R1bR19R17R16R15R14A6R4A3S70Vsegs;R1dS59Vsegs;S5fU0S52SfR6R1bR5A6VE;R4R3A5S3cVsegs;S4cR1aR19S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1cR1bA5A4SaG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_TA (E : axst) : Prop := ltac2:(tb__ "0|3|
S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S65R9A1S47RbA1S0S5S4aG0S1bRaPcA2A2R8A3S0S5S4aG0S1bRbPdA2A2R8A3S6aSdS5S5A2ScS5S5RaR9A4S46ReA1A3S5eRbRaA2S0S7S45R10A1S8A3S43S37R11A2S61R10S40R12R10ReRdRcRbA6A2S0S5S41RcA1S66A3S5S2S53VCST;R15R1A3S54VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S44S18S18G1S60R19R4A2S69R12S40R1aR18R16R15R14R13A6R4A3S6fVsegs;S59Vsegs;S5fU0S52SfR6R1aR5A6VE;R4R3A5S3cVsegs;S4cR19R18S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1bR1aA5A4SaG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_TA : drain_stmt_TA Edr_TA.
Proof.
  rewrite Edr_eq_TA.
  exact (f0_drain QA CST XGL HCST HXGL HCSTQ Cd_TA TQ_TA TQr_TA sQ_TA RQ_TA HEQ_TA HCK_TA HTQ_TA HTQr_TA QCHK_TA QCHKr_TA Xf2_TA XM2_TA XR2_TA XEX2_TA sX2_TA run7_TA
           NX7_TA RUN7_TA L7_TA run7r_TA NX7r_TA RUN7r_TA L7r_TA AXE2_TA WXR2_TA DXR2_TA NXR2_TA EQR2_TA ENT2_TA SID2_TA HCSTF Edr_nf_TA XMd_TA XKd_TA KEPTd_TA RESTd_TA XEXd_TA
           AXEd_TA OBJSd_TA EQKd_TA RCLSd_TA RCIVd_TA RCELLd_TA RWRd_TA RSHPd_TA ECd_TA FBCd_TA).
Qed.
Theorem ef0_drain_TA : edrain_stmt_TA Edr_TA.
Proof.
  rewrite Edr_eq_TA.
  exact (ef0_drain QA CST XGL HCST HXGL HCSTQ Cd_TA TQ_TA TQr_TA sQ_TA RQ_TA HEQ_TA HCK_TA HTQ_TA HTQr_TA QCHK_TA QCHKr_TA Xf2_TA XM2_TA XR2_TA XEX2_TA sX2_TA run7_TA
           NX7_TA RUN7_TA L7_TA run7r_TA NX7r_TA RUN7r_TA L7r_TA AXE2_TA WXR2_TA DXR2_TA NXR2_TA EQR2_TA ENT2_TA SID2_TA HCSTF Edr_nf_TA XMd_TA XKd_TA KEPTd_TA RESTd_TA XEXd_TA
           AXEd_TA OBJSd_TA EQKd_TA RCLSd_TA RCIVd_TA RCELLd_TA RWRd_TA RSHPd_TA ECd_TA FBCd_TA).
Qed.
End QTA.
End F0T_qTA.

(* [comment removed for export] *)
Module F0T_qTBe.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBe"; "Cd_TBe"; "XMd_TBe"; "RQ_TBe"; "XR2_TBe"; "sQ_TBe"; "RESTd_TBe"; "TQ_TBe"; "TQr_TBe"; "XKd_TBe"; "XM2_TBe"; "KEPTd_TBe"; "Xf2_TBe"; "run7_TBe"; "run7r_TBe"; "nkd_TBe"; "sX2_TBe"; "Edr_nf_TBe"; "XEX2_TBe"; "XEXd_TBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_TBe : axst := Eval vm_compute in Edr_TBe.
Lemma Edr_eq_TBe : Edr_TBe = Edr_nf_TBe. Proof. vm_cast_no_check (eq_refl Edr_nf_TBe). Qed.

Definition XEXd_TBe : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_TBe))].
Definition XMd_TBe : axst := Eval vm_compute in (axf Edr_nf_TBe XEXd_TBe).
Lemma AXEd_TBe : ltac2:(tb__ "0|0|
S0S10S12A1S5cS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_TBe)). Qed.
Definition nkd_TBe : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_TBe) + 0 + 2)%nat.
Definition KEPTd_TBe : list sobj := ltac2:(tb__ "0|0|
S6dS19S32S1eS13S25A1A1A3").
Definition RESTd_TBe : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Lemma OBJSd_TBe : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_TBe : axst := ltac2:(tb__ "0|0|
S14S25S58S13S25A1S2eA2A2").
Lemma EQKd_TBe : ltac2:(tb__ "0|0|
S0S12S14S25S58S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_TBe : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_TBe : rcivb RESTd_TBe = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_TBe : ltac2:(tb__ "0|0|
S0S7S76S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_TBe : rwrb RESTd_TBe = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_TBe : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_TBe : axst := Eval vm_compute in (ax_with_facts XKd_TBe (ss_facts (ax_S XKd_TBe) ++ [F_cne])).
Lemma ECd_TBe : ltac2:(tb__ "0|0|
S0S12S24S4dS2cS11S17S1cS13S2cA1A1S9S17S62SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_TBe). Qed.
Lemma FBCd_TBe : ltac2:(tb__ "0|1|
S0S7S6bS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S62SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_TBe : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_TBe) (ax_S PreQ3)).
Definition RQ_TBe : list sobj := Eval vm_compute in (optR (entails_frA Cd_TBe PreQ3 sQ_TBe)).
Lemma HEQ_TBe : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S3fS24S48S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_TBe)). Qed.
Lemma HCK_TBe : ltac2:(tb__ "0|0|
S0S7S3eS24S48S28S26S9S12S49S9S12S57SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_TBe : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_TBe PreQ3 PostQ3 Cd_TBe RQ_TBe) (ss_facts (ax_S Cd_TBe))).
Lemma HTQ_TBe : ltac2:(tb__ "0|0|
S0S12S2aS4dS3dS28S48S49S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_TBe). Qed.
Lemma QCHK_TBe : ltac2:(tb__ "0|0|
S0S7S63U0S24S49S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_TBe : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_TBe PreQ3 PostQ3r Cd_TBe RQ_TBe) (ss_facts (ax_S Cd_TBe))).
Lemma HTQr_TBe : ltac2:(tb__ "0|0|
S0S12S2bS4dS3dS28S48S57S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_TBe). Qed.
Lemma QCHKr_TBe : ltac2:(tb__ "0|0|
S0S7S63U0S24S57S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_TBe : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_TBe).
Lemma RUN7_TBe : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_TBe). Qed.
Definition Xf2_TBe : axst := Eval vm_compute in (leaf 0 run7_TBe).
Lemma L7_TBe : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S67U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_TBe)]. Qed.
Lemma NX7_TBe : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_TBe : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_TBe).
Lemma RUN7r_TBe : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_TBe). Qed.
Lemma L7r_TBe : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S67U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_TBe)]. Qed.
Lemma NX7r_TBe : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_TBe : list axform := Eval vm_compute in (XEX_of Xf2_TBe).
Definition XM2_TBe : axst := Eval vm_compute in (axf Xf2_TBe XEX2_TBe).
Lemma AXE2_TBe : ltac2:(tb__ "0|0|
S0S10S12A1S5cS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_TBe)). Qed.
Definition XR2_TBe : axst := Eval vm_compute in (XR_of XM2_TBe).
Definition sX2_TBe : wsub := Eval vm_compute in (infer_sub NF (ax_S XR2_TBe) (ax_S (L_free_tol AE_A))).
Lemma WXR2_TBe : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_TBe : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S72S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S74A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_TBe : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_TBe))). Qed.
Lemma EQR2_TBe : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_TBe). Qed.
Lemma ENT2_TBe : ltac2:(tb__ "0|0|
S0S7S16S27S55S4eA1S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_TBe : ltac2:(tb__ "0|0|
S0S7S73S33S4cA2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QTBe.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S4S7bR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S2S56S75R2A2S1S7cS79R2A2S7dR2S7aA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_TBe (E : axst) : Prop := ltac2:(tb__ "0|3|
S71OF_;S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S5bVsegs;RbS5aR9A1A3S64RcRaA2S47RcA1S0S5S4aG0S1bRbPcA2A2R9A3S0S5S4aG0S1bRcPdA2A2R9A3S6aSdS5S5A2ScS5S5RbRaA4S46RfA1A3S5eRcRbA2S0S7S45R11A1S8A3S43S37R12A2S61R11S40R13R11RfReRdRcA6A2S0S5S41RdA1S66A3S5S2S53VCST;R16R1A3S54VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S44S18S18G1S60R1aR4A2S69R13S40R1bR19R17R16R15R14A6R4A3S70Vsegs;R1dS59Vsegs;S5fU0S52SfR6R1bR5A6VE;R4R3A5S3cVsegs;S4cR1aR19S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1cR1bA5A4SaG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_TBe (E : axst) : Prop := ltac2:(tb__ "0|3|
S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S65R9A1S47RbA1S0S5S4aG0S1bRaPcA2A2R8A3S0S5S4aG0S1bRbPdA2A2R8A3S6aSdS5S5A2ScS5S5RaR9A4S46ReA1A3S5eRbRaA2S0S7S45R10A1S8A3S43S37R11A2S61R10S40R12R10ReRdRcRbA6A2S0S5S41RcA1S66A3S5S2S53VCST;R15R1A3S54VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S44S18S18G1S60R19R4A2S69R12S40R1aR18R16R15R14R13A6R4A3S6fVsegs;S59Vsegs;S5fU0S52SfR6R1aR5A6VE;R4R3A5S3cVsegs;S4cR19R18S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1bR1aA5A4SaG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_TBe : drain_stmt_TBe Edr_TBe.
Proof.
  rewrite Edr_eq_TBe.
  exact (f0_drain QBe CST XGL HCST HXGL HCSTQ Cd_TBe TQ_TBe TQr_TBe sQ_TBe RQ_TBe HEQ_TBe HCK_TBe HTQ_TBe HTQr_TBe QCHK_TBe QCHKr_TBe Xf2_TBe XM2_TBe XR2_TBe XEX2_TBe sX2_TBe run7_TBe
           NX7_TBe RUN7_TBe L7_TBe run7r_TBe NX7r_TBe RUN7r_TBe L7r_TBe AXE2_TBe WXR2_TBe DXR2_TBe NXR2_TBe EQR2_TBe ENT2_TBe SID2_TBe HCSTF Edr_nf_TBe XMd_TBe XKd_TBe KEPTd_TBe RESTd_TBe XEXd_TBe
           AXEd_TBe OBJSd_TBe EQKd_TBe RCLSd_TBe RCIVd_TBe RCELLd_TBe RWRd_TBe RSHPd_TBe ECd_TBe FBCd_TBe).
Qed.
Theorem ef0_drain_TBe : edrain_stmt_TBe Edr_TBe.
Proof.
  rewrite Edr_eq_TBe.
  exact (ef0_drain QBe CST XGL HCST HXGL HCSTQ Cd_TBe TQ_TBe TQr_TBe sQ_TBe RQ_TBe HEQ_TBe HCK_TBe HTQ_TBe HTQr_TBe QCHK_TBe QCHKr_TBe Xf2_TBe XM2_TBe XR2_TBe XEX2_TBe sX2_TBe run7_TBe
           NX7_TBe RUN7_TBe L7_TBe run7r_TBe NX7r_TBe RUN7r_TBe L7r_TBe AXE2_TBe WXR2_TBe DXR2_TBe NXR2_TBe EQR2_TBe ENT2_TBe SID2_TBe HCSTF Edr_nf_TBe XMd_TBe XKd_TBe KEPTd_TBe RESTd_TBe XEXd_TBe
           AXEd_TBe OBJSd_TBe EQKd_TBe RCLSd_TBe RCIVd_TBe RCELLd_TBe RWRd_TBe RSHPd_TBe ECd_TBe FBCd_TBe).
Qed.
End QTBe.
End F0T_qTBe.

(* [comment removed for export] *)
Module F0T_qTBf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBf"; "Cd_TBf"; "XMd_TBf"; "RQ_TBf"; "XR2_TBf"; "sQ_TBf"; "RESTd_TBf"; "TQ_TBf"; "TQr_TBf"; "XKd_TBf"; "XM2_TBf"; "KEPTd_TBf"; "Xf2_TBf"; "run7_TBf"; "run7r_TBf"; "nkd_TBf"; "sX2_TBf"; "Edr_nf_TBf"; "XEX2_TBf"; "XEXd_TBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "UStopLe"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_TBf : axst := Eval vm_compute in Edr_TBf.
Lemma Edr_eq_TBf : Edr_TBf = Edr_nf_TBf. Proof. vm_cast_no_check (eq_refl Edr_nf_TBf). Qed.

Definition XEXd_TBf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_TBf))].
Definition XMd_TBf : axst := Eval vm_compute in (axf Edr_nf_TBf XEXd_TBf).
Lemma AXEd_TBf : ltac2:(tb__ "0|0|
S0S10S12A1S5cS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_TBf)). Qed.
Definition nkd_TBf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_TBf) + 0 + 2)%nat.
Definition KEPTd_TBf : list sobj := ltac2:(tb__ "0|0|
S6dS19S32S1eS13S25A1A1A3").
Definition RESTd_TBf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Lemma OBJSd_TBf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_TBf : axst := ltac2:(tb__ "0|0|
S14S25S58S13S25A1S2eA2A2").
Lemma EQKd_TBf : ltac2:(tb__ "0|0|
S0S12S14S25S58S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_TBf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_TBf : rcivb RESTd_TBf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_TBf : ltac2:(tb__ "0|0|
S0S7S76S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_TBf : rwrb RESTd_TBf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_TBf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_TBf : axst := Eval vm_compute in (ax_with_facts XKd_TBf (ss_facts (ax_S XKd_TBf) ++ [F_cne])).
Lemma ECd_TBf : ltac2:(tb__ "0|0|
S0S12S24S4dS2cS11S17S1cS13S2cA1A1S9S17S62SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_TBf). Qed.
Lemma FBCd_TBf : ltac2:(tb__ "0|1|
S0S7S6bS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S62SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_TBf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_TBf) (ax_S PreQ3)).
Definition RQ_TBf : list sobj := Eval vm_compute in (optR (entails_frA Cd_TBf PreQ3 sQ_TBf)).
Lemma HEQ_TBf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S3fS24S48S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_TBf)). Qed.
Lemma HCK_TBf : ltac2:(tb__ "0|0|
S0S7S3eS24S48S28S26S9S12S49S9S12S57SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_TBf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_TBf PreQ3 PostQ3 Cd_TBf RQ_TBf) (ss_facts (ax_S Cd_TBf))).
Lemma HTQ_TBf : ltac2:(tb__ "0|0|
S0S12S2aS4dS3dS28S48S49S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_TBf). Qed.
Lemma QCHK_TBf : ltac2:(tb__ "0|0|
S0S7S63U0S24S49S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_TBf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_TBf PreQ3 PostQ3r Cd_TBf RQ_TBf) (ss_facts (ax_S Cd_TBf))).
Lemma HTQr_TBf : ltac2:(tb__ "0|0|
S0S12S2bS4dS3dS28S48S57S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_TBf). Qed.
Lemma QCHKr_TBf : ltac2:(tb__ "0|0|
S0S7S63U0S24S57S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_TBf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_TBf).
Lemma RUN7_TBf : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_TBf). Qed.
Definition Xf2_TBf : axst := Eval vm_compute in (leaf 0 run7_TBf).
Lemma L7_TBf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S67U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_TBf)]. Qed.
Lemma NX7_TBf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_TBf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_TBf).
Lemma RUN7r_TBf : ltac2:(tb__ "0|0|
S0SbS15A1S68S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_TBf). Qed.
Lemma L7r_TBf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S67U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_TBf)]. Qed.
Lemma NX7r_TBf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6cS5dS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_TBf : list axform := Eval vm_compute in (XEX_of Xf2_TBf).
Definition XM2_TBf : axst := Eval vm_compute in (axf Xf2_TBf XEX2_TBf).
Lemma AXE2_TBf : ltac2:(tb__ "0|0|
S0S10S12A1S5cS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_TBf)). Qed.
Definition XR2_TBf : axst := Eval vm_compute in (XR_of XM2_TBf).
Definition sX2_TBf : wsub := Eval vm_compute in (infer_sub NF (ax_S XR2_TBf) (ax_S (L_free_tol AE_A))).
Lemma WXR2_TBf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_TBf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S72S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S74A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_TBf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_TBf))). Qed.
Lemma EQR2_TBf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_TBf). Qed.
Lemma ENT2_TBf : ltac2:(tb__ "0|0|
S0S7S16S27S55S4eA1S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_TBf : ltac2:(tb__ "0|0|
S0S7S73S33S4cA2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QTBf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S4S7bR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S56VCST;R1A2S2S56S75R2A2S1S7cS79R2A2S7dR2S7aA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_TBf (E : axst) : Prop := ltac2:(tb__ "0|3|
S71OF_;S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S5bVsegs;RbS5aR9A1A3S64RcRaA2S47RcA1S0S5S4aG0S1bRbPcA2A2R9A3S0S5S4aG0S1bRcPdA2A2R9A3S6aSdS5S5A2ScS5S5RbRaA4S46RfA1A3S5eRcRbA2S0S7S45R11A1S8A3S43S37R12A2S61R11S40R13R11RfReRdRcA6A2S0S5S41RdA1S66A3S5S2S53VCST;R16R1A3S54VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S44S18S18G1S60R1aR4A2S69R13S40R1bR19R17R16R15R14A6R4A3S70Vsegs;R1dS59Vsegs;S5fU0S52SfR6R1bR5A6VE;R4R3A5S3cVsegs;S4cR1aR19S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1cR1bA5A4SaG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_TBf (E : axst) : Prop := ltac2:(tb__ "0|3|
S44S50S18SbS4bQ40M0A1A1M1S5S5S5S42S5OF_;S51R8A1S65R9A1S47RbA1S0S5S4aG0S1bRaPcA2A2R8A3S0S5S4aG0S1bRbPdA2A2R8A3S6aSdS5S5A2ScS5S5RaR9A4S46ReA1A3S5eRbRaA2S0S7S45R10A1S8A3S43S37R11A2S61R10S40R12R10ReRdRcRbA6A2S0S5S41RcA1S66A3S5S2S53VCST;R15R1A3S54VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S44S18S18G1S60R19R4A2S69R12S40R1aR18R16R15R14R13A6R4A3S6fVsegs;S59Vsegs;S5fU0S52SfR6R1aR5A6VE;R4R3A5S3cVsegs;S4cR19R18S9SdS12S3bA2M2ScS12S3bS55S4eA1S4fVAInv;VCST;VXGL;R1bR1aA5A4SaG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_TBf : drain_stmt_TBf Edr_TBf.
Proof.
  rewrite Edr_eq_TBf.
  exact (f0_drain QBf CST XGL HCST HXGL HCSTQ Cd_TBf TQ_TBf TQr_TBf sQ_TBf RQ_TBf HEQ_TBf HCK_TBf HTQ_TBf HTQr_TBf QCHK_TBf QCHKr_TBf Xf2_TBf XM2_TBf XR2_TBf XEX2_TBf sX2_TBf run7_TBf
           NX7_TBf RUN7_TBf L7_TBf run7r_TBf NX7r_TBf RUN7r_TBf L7r_TBf AXE2_TBf WXR2_TBf DXR2_TBf NXR2_TBf EQR2_TBf ENT2_TBf SID2_TBf HCSTF Edr_nf_TBf XMd_TBf XKd_TBf KEPTd_TBf RESTd_TBf XEXd_TBf
           AXEd_TBf OBJSd_TBf EQKd_TBf RCLSd_TBf RCIVd_TBf RCELLd_TBf RWRd_TBf RSHPd_TBf ECd_TBf FBCd_TBf).
Qed.
Theorem ef0_drain_TBf : edrain_stmt_TBf Edr_TBf.
Proof.
  rewrite Edr_eq_TBf.
  exact (ef0_drain QBf CST XGL HCST HXGL HCSTQ Cd_TBf TQ_TBf TQr_TBf sQ_TBf RQ_TBf HEQ_TBf HCK_TBf HTQ_TBf HTQr_TBf QCHK_TBf QCHKr_TBf Xf2_TBf XM2_TBf XR2_TBf XEX2_TBf sX2_TBf run7_TBf
           NX7_TBf RUN7_TBf L7_TBf run7r_TBf NX7r_TBf RUN7r_TBf L7r_TBf AXE2_TBf WXR2_TBf DXR2_TBf NXR2_TBf EQR2_TBf ENT2_TBf SID2_TBf HCSTF Edr_nf_TBf XMd_TBf XKd_TBf KEPTd_TBf RESTd_TBf XEXd_TBf
           AXEd_TBf OBJSd_TBf EQKd_TBf RCLSd_TBf RCIVd_TBf RCELLd_TBf RWRd_TBf RSHPd_TBf ECd_TBf FBCd_TBf).
Qed.
End QTBf.
End F0T_qTBf.

