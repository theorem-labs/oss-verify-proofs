(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain ah.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf SegQ3M_glue.

(* [comment removed for export] *)
Module F0A_qL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_qL1A"; "Cd_L1A"; "XMd_L1A"; "RQ_L1A"; "XR2_L1A"; "sQ_L1A"; "RESTd_L1A"; "TQ_L1A"; "TQr_L1A"; "XKd_L1A"; "XM2_L1A"; "KEPTd_L1A"; "Xf2_L1A"; "run7_L1A"; "run7r_L1A"; "nkd_L1A"; "sX2_L1A"; "Edr_nf_L1A"; "XEX2_L1A"; "XEXd_L1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L1A : axst := Eval vm_compute in Edr_L1A.
Lemma Edr_eq_L1A : Edr_L1A = Edr_nf_L1A. Proof. vm_cast_no_check (eq_refl Edr_nf_L1A). Qed.

Definition XEXd_L1A : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L1A))].
Definition XMd_L1A : axst := Eval vm_compute in (axf Edr_nf_L1A XEXd_L1A).
Lemma AXEd_L1A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L1A)). Qed.
Definition nkd_L1A : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L1A) + 1 + 2)%nat.
Definition KEPTd_L1A : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L1A : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L1A : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L1A : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L1A : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L1A : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L1A : rcivb RESTd_L1A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L1A : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L1A : rwrb RESTd_L1A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L1A : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L1A : axst := Eval vm_compute in (ax_with_facts XKd_L1A (ss_facts (ax_S XKd_L1A) ++ [F_cne])).
Lemma ECd_L1A : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L1A). Qed.
Lemma FBCd_L1A : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L1A : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L1A) (ax_S PreQ3)).
Definition RQ_L1A : list sobj := Eval vm_compute in (optR (entails_frA Cd_L1A PreQ3 sQ_L1A)).
Lemma HEQ_L1A : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L1A)). Qed.
Lemma HCK_L1A : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L1A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L1A PreQ3 PostQ3 Cd_L1A RQ_L1A) (ss_facts (ax_S Cd_L1A))).
Lemma HTQ_L1A : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L1A). Qed.
Lemma QCHK_L1A : ltac2:(tb__ "0|0|
S0S7S61U1S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L1A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L1A PreQ3 PostQ3r Cd_L1A RQ_L1A) (ss_facts (ax_S Cd_L1A))).
Lemma HTQr_L1A : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L1A). Qed.
Lemma QCHKr_L1A : ltac2:(tb__ "0|0|
S0S7S61U1S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L1A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L1A).
Lemma RUN7_L1A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L1A). Qed.
Definition Xf2_L1A : axst := Eval vm_compute in (leaf 0 run7_L1A).
Lemma L7_L1A : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L1A)]. Qed.
Lemma NX7_L1A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L1A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L1A).
Lemma RUN7r_L1A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L1A). Qed.
Lemma L7r_L1A : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L1A)]. Qed.
Lemma NX7r_L1A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L1A : list axform := Eval vm_compute in (XEX_of Xf2_L1A).
Definition XM2_L1A : axst := Eval vm_compute in (axf Xf2_L1A XEX2_L1A).
Lemma AXE2_L1A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L1A)). Qed.
Definition XR2_L1A : axst := Eval vm_compute in (XR_of XM2_L1A).
Definition sX2_L1A : wsub := Eval vm_compute in (sX_of XR2_L1A (Wcan 1) UStopLe).
Lemma WXR2_L1A : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L1A : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L1A : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L1A))). Qed.
Lemma EQR2_L1A : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L1A). Qed.
Lemma ENT2_L1A : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU1A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L1A : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL1A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L1A (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U1M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L1A (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U1M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L1A : drain_stmt_L1A Edr_L1A.
Proof.
  rewrite Edr_eq_L1A.
  exact (f0_drain 1%nat QA CST XGL HCST HXGL HCSTQ Cd_L1A TQ_L1A TQr_L1A sQ_L1A RQ_L1A HEQ_L1A HCK_L1A HTQ_L1A HTQr_L1A QCHK_L1A QCHKr_L1A Xf2_L1A XM2_L1A XR2_L1A XEX2_L1A sX2_L1A run7_L1A
           NX7_L1A RUN7_L1A L7_L1A run7r_L1A NX7r_L1A RUN7r_L1A L7r_L1A AXE2_L1A WXR2_L1A DXR2_L1A NXR2_L1A EQR2_L1A ENT2_L1A SID2_L1A HCSTF Edr_nf_L1A XMd_L1A XKd_L1A KEPTd_L1A RESTd_L1A XEXd_L1A
           AXEd_L1A OBJSd_L1A EQKd_L1A RCLSd_L1A RCIVd_L1A RCELLd_L1A RWRd_L1A RSHPd_L1A ECd_L1A FBCd_L1A).
Qed.
Theorem ef0_drain_L1A : edrain_stmt_L1A Edr_L1A.
Proof.
  rewrite Edr_eq_L1A.
  exact (ef0_drain 1%nat QA CST XGL HCST HXGL HCSTQ Cd_L1A TQ_L1A TQr_L1A sQ_L1A RQ_L1A HEQ_L1A HCK_L1A HTQ_L1A HTQr_L1A QCHK_L1A QCHKr_L1A Xf2_L1A XM2_L1A XR2_L1A XEX2_L1A sX2_L1A run7_L1A
           NX7_L1A RUN7_L1A L7_L1A run7r_L1A NX7r_L1A RUN7r_L1A L7r_L1A AXE2_L1A WXR2_L1A DXR2_L1A NXR2_L1A EQR2_L1A ENT2_L1A SID2_L1A HCSTF Edr_nf_L1A XMd_L1A XKd_L1A KEPTd_L1A RESTd_L1A XEXd_L1A
           AXEd_L1A OBJSd_L1A EQKd_L1A RCLSd_L1A RCIVd_L1A RCELLd_L1A RWRd_L1A RSHPd_L1A ECd_L1A FBCd_L1A).
Qed.
End QL1A.
End F0A_qL1A.

(* [comment removed for export] *)
Module F0A_qL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_qL1Be"; "Cd_L1Be"; "XMd_L1Be"; "RQ_L1Be"; "XR2_L1Be"; "sQ_L1Be"; "RESTd_L1Be"; "TQ_L1Be"; "TQr_L1Be"; "XKd_L1Be"; "XM2_L1Be"; "KEPTd_L1Be"; "Xf2_L1Be"; "run7_L1Be"; "run7r_L1Be"; "nkd_L1Be"; "sX2_L1Be"; "Edr_nf_L1Be"; "XEX2_L1Be"; "XEXd_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L1Be : axst := Eval vm_compute in Edr_L1Be.
Lemma Edr_eq_L1Be : Edr_L1Be = Edr_nf_L1Be. Proof. vm_cast_no_check (eq_refl Edr_nf_L1Be). Qed.

Definition XEXd_L1Be : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L1Be))].
Definition XMd_L1Be : axst := Eval vm_compute in (axf Edr_nf_L1Be XEXd_L1Be).
Lemma AXEd_L1Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L1Be)). Qed.
Definition nkd_L1Be : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L1Be) + 1 + 2)%nat.
Definition KEPTd_L1Be : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L1Be : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L1Be : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L1Be : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L1Be : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L1Be : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L1Be : rcivb RESTd_L1Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L1Be : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L1Be : rwrb RESTd_L1Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L1Be : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L1Be : axst := Eval vm_compute in (ax_with_facts XKd_L1Be (ss_facts (ax_S XKd_L1Be) ++ [F_cne])).
Lemma ECd_L1Be : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L1Be). Qed.
Lemma FBCd_L1Be : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L1Be : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L1Be) (ax_S PreQ3)).
Definition RQ_L1Be : list sobj := Eval vm_compute in (optR (entails_frA Cd_L1Be PreQ3 sQ_L1Be)).
Lemma HEQ_L1Be : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L1Be)). Qed.
Lemma HCK_L1Be : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L1Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L1Be PreQ3 PostQ3 Cd_L1Be RQ_L1Be) (ss_facts (ax_S Cd_L1Be))).
Lemma HTQ_L1Be : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L1Be). Qed.
Lemma QCHK_L1Be : ltac2:(tb__ "0|0|
S0S7S61U1S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L1Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L1Be PreQ3 PostQ3r Cd_L1Be RQ_L1Be) (ss_facts (ax_S Cd_L1Be))).
Lemma HTQr_L1Be : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L1Be). Qed.
Lemma QCHKr_L1Be : ltac2:(tb__ "0|0|
S0S7S61U1S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L1Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L1Be).
Lemma RUN7_L1Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L1Be). Qed.
Definition Xf2_L1Be : axst := Eval vm_compute in (leaf 0 run7_L1Be).
Lemma L7_L1Be : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L1Be)]. Qed.
Lemma NX7_L1Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L1Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L1Be).
Lemma RUN7r_L1Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L1Be). Qed.
Lemma L7r_L1Be : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L1Be)]. Qed.
Lemma NX7r_L1Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L1Be : list axform := Eval vm_compute in (XEX_of Xf2_L1Be).
Definition XM2_L1Be : axst := Eval vm_compute in (axf Xf2_L1Be XEX2_L1Be).
Lemma AXE2_L1Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L1Be)). Qed.
Definition XR2_L1Be : axst := Eval vm_compute in (XR_of XM2_L1Be).
Definition sX2_L1Be : wsub := Eval vm_compute in (sX_of XR2_L1Be (Wcan 1) UStopLe).
Lemma WXR2_L1Be : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L1Be : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L1Be : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L1Be))). Qed.
Lemma EQR2_L1Be : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L1Be). Qed.
Lemma ENT2_L1Be : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU1A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L1Be : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL1Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L1Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U1M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L1Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U1M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L1Be : drain_stmt_L1Be Edr_L1Be.
Proof.
  rewrite Edr_eq_L1Be.
  exact (f0_drain 1%nat QBe CST XGL HCST HXGL HCSTQ Cd_L1Be TQ_L1Be TQr_L1Be sQ_L1Be RQ_L1Be HEQ_L1Be HCK_L1Be HTQ_L1Be HTQr_L1Be QCHK_L1Be QCHKr_L1Be Xf2_L1Be XM2_L1Be XR2_L1Be XEX2_L1Be sX2_L1Be run7_L1Be
           NX7_L1Be RUN7_L1Be L7_L1Be run7r_L1Be NX7r_L1Be RUN7r_L1Be L7r_L1Be AXE2_L1Be WXR2_L1Be DXR2_L1Be NXR2_L1Be EQR2_L1Be ENT2_L1Be SID2_L1Be HCSTF Edr_nf_L1Be XMd_L1Be XKd_L1Be KEPTd_L1Be RESTd_L1Be XEXd_L1Be
           AXEd_L1Be OBJSd_L1Be EQKd_L1Be RCLSd_L1Be RCIVd_L1Be RCELLd_L1Be RWRd_L1Be RSHPd_L1Be ECd_L1Be FBCd_L1Be).
Qed.
Theorem ef0_drain_L1Be : edrain_stmt_L1Be Edr_L1Be.
Proof.
  rewrite Edr_eq_L1Be.
  exact (ef0_drain 1%nat QBe CST XGL HCST HXGL HCSTQ Cd_L1Be TQ_L1Be TQr_L1Be sQ_L1Be RQ_L1Be HEQ_L1Be HCK_L1Be HTQ_L1Be HTQr_L1Be QCHK_L1Be QCHKr_L1Be Xf2_L1Be XM2_L1Be XR2_L1Be XEX2_L1Be sX2_L1Be run7_L1Be
           NX7_L1Be RUN7_L1Be L7_L1Be run7r_L1Be NX7r_L1Be RUN7r_L1Be L7r_L1Be AXE2_L1Be WXR2_L1Be DXR2_L1Be NXR2_L1Be EQR2_L1Be ENT2_L1Be SID2_L1Be HCSTF Edr_nf_L1Be XMd_L1Be XKd_L1Be KEPTd_L1Be RESTd_L1Be XEXd_L1Be
           AXEd_L1Be OBJSd_L1Be EQKd_L1Be RCLSd_L1Be RCIVd_L1Be RCELLd_L1Be RWRd_L1Be RSHPd_L1Be ECd_L1Be FBCd_L1Be).
Qed.
End QL1Be.
End F0A_qL1Be.

(* [comment removed for export] *)
Module SegQ3_sum.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "and"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "ok_frameA"; "liftKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "qbounded"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "HRECE_e"; "HRECE_n"; "HREC_e"; "HREC_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQ3_sum"; "rec_sum"; "rec_sumE"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Import ListNotations.
Open Scope Z_scope.

Definition rec_sum (ok : world -> Prop) (Kc : KcA) : Prop := ltac2:(tb__ "0|4|
S9S13S3S1cQ40A1A1S1S0S3S8A1M0ScR3A1S5S8A1M1A3A1S0S4SaR4A1S6A3S1aR5A1S1bSdR6A1S15A2S14S7S18R6R5S19S10VKc;A1M2R7A2A5S11S2S1S0G0SbR8A1G1A3M3A1S24G2Vok;R9R8R7R2A6F_;G3S23G2Vok;R9R8R7R2A6F_;A2TQ;F_;F_;F_;F_;Ftp;Frho;FA;").
Definition rec_sumE (Kc : KcA) : Prop := ltac2:(tb__ "0|4|
S9S13S3S1cQ40A1A1S1S0S3S8A1M0ScR3A1S5S8A1M1A3A1S0S4SaR4A1S6A3S1aR5A1S1bSdR6A1S15A2S14S7S18R6R5S19S10VKc;A1M2R7A2A5S11S2S1S0G0SbR8A1G1A3M3A1S22G2R9R8R7R2A5F_;G3S21G2R9R8R7R2A5F_;A2TQ;F_;F_;F_;F_;Ftp;Frho;FA;").

Lemma K0_ok_frame : ltac2:(tb__ "0|0|
S12OF_;S3S1eA1S1dOF_;F_;S9SeS7R3SfR2A1A3SeS7R4S10R3R2A2A3F_;FA;FKc;Fok;").
Proof. intros ok Kc A H rho tp tr ms md msv' (_ & HK & _). exact (H rho tp tr ms md msv' HK). Qed.

Theorem drain_sum_of_rec : ltac2:(tb__ "0|0|
S12OF_;S16S17R1A1SeS7R3SfR2A1A3S25R4R3A2S1fR5R4A2F_;F_;F_;FKc;Fok;").
Proof.
  intros ok Kc HKc Hok HR A rho tp HT HCI HQB HBD. destruct (HR A rho tp HT HCI HQB HBD) as [Hn He].
  exact (transfer_sound (K0 Kc) ok (K0_laws Kc HKc) (fun A0 => K0_ok_frame ok Kc A0 Hok) A rho tp _ HT HCI HQB (LQPA_PostsQ3 (K0 Kc) A rho tp) Hn He).
Qed.
Theorem drain_sumE_of_rec : ltac2:(tb__ "0|0|
S16S17R1A1S26R2A1S20R3A1F_;F_;FKc;").
Proof.
  intros Kc HKc HR A rho tp HT HCI HQB HBD. destruct (HR A rho tp HT HCI HQB HBD) as [Hn He].
  exact (transfer_complete (K0 Kc) (K0_laws Kc HKc) A rho tp _ HT HCI HQB (LQPA_PostsQ3 (K0 Kc) A rho tp) Hn He).
Qed.
End SegQ3_sum.

(* [comment removed for export] *)
Module F0A_qL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_qL1Bf"; "Cd_L1Bf"; "XMd_L1Bf"; "RQ_L1Bf"; "XR2_L1Bf"; "sQ_L1Bf"; "RESTd_L1Bf"; "TQ_L1Bf"; "TQr_L1Bf"; "XKd_L1Bf"; "XM2_L1Bf"; "KEPTd_L1Bf"; "Xf2_L1Bf"; "run7_L1Bf"; "run7r_L1Bf"; "nkd_L1Bf"; "sX2_L1Bf"; "Edr_nf_L1Bf"; "XEX2_L1Bf"; "XEXd_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L1Bf : axst := Eval vm_compute in Edr_L1Bf.
Lemma Edr_eq_L1Bf : Edr_L1Bf = Edr_nf_L1Bf. Proof. vm_cast_no_check (eq_refl Edr_nf_L1Bf). Qed.

Definition XEXd_L1Bf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L1Bf))].
Definition XMd_L1Bf : axst := Eval vm_compute in (axf Edr_nf_L1Bf XEXd_L1Bf).
Lemma AXEd_L1Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L1Bf)). Qed.
Definition nkd_L1Bf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L1Bf) + 1 + 2)%nat.
Definition KEPTd_L1Bf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L1Bf : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L1Bf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L1Bf : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L1Bf : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L1Bf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L1Bf : rcivb RESTd_L1Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L1Bf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L1Bf : rwrb RESTd_L1Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L1Bf : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L1Bf : axst := Eval vm_compute in (ax_with_facts XKd_L1Bf (ss_facts (ax_S XKd_L1Bf) ++ [F_cne])).
Lemma ECd_L1Bf : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L1Bf). Qed.
Lemma FBCd_L1Bf : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L1Bf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L1Bf) (ax_S PreQ3)).
Definition RQ_L1Bf : list sobj := Eval vm_compute in (optR (entails_frA Cd_L1Bf PreQ3 sQ_L1Bf)).
Lemma HEQ_L1Bf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L1Bf)). Qed.
Lemma HCK_L1Bf : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L1Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L1Bf PreQ3 PostQ3 Cd_L1Bf RQ_L1Bf) (ss_facts (ax_S Cd_L1Bf))).
Lemma HTQ_L1Bf : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L1Bf). Qed.
Lemma QCHK_L1Bf : ltac2:(tb__ "0|0|
S0S7S61U1S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L1Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L1Bf PreQ3 PostQ3r Cd_L1Bf RQ_L1Bf) (ss_facts (ax_S Cd_L1Bf))).
Lemma HTQr_L1Bf : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L1Bf). Qed.
Lemma QCHKr_L1Bf : ltac2:(tb__ "0|0|
S0S7S61U1S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L1Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L1Bf).
Lemma RUN7_L1Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L1Bf). Qed.
Definition Xf2_L1Bf : axst := Eval vm_compute in (leaf 0 run7_L1Bf).
Lemma L7_L1Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L1Bf)]. Qed.
Lemma NX7_L1Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L1Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L1Bf).
Lemma RUN7r_L1Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L1Bf). Qed.
Lemma L7r_L1Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L1Bf)]. Qed.
Lemma NX7r_L1Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L1Bf : list axform := Eval vm_compute in (XEX_of Xf2_L1Bf).
Definition XM2_L1Bf : axst := Eval vm_compute in (axf Xf2_L1Bf XEX2_L1Bf).
Lemma AXE2_L1Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L1Bf)). Qed.
Definition XR2_L1Bf : axst := Eval vm_compute in (XR_of XM2_L1Bf).
Definition sX2_L1Bf : wsub := Eval vm_compute in (sX_of XR2_L1Bf (Wcan 1) UStopLe).
Lemma WXR2_L1Bf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L1Bf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L1Bf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L1Bf))). Qed.
Lemma EQR2_L1Bf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L1Bf). Qed.
Lemma ENT2_L1Bf : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU1A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L1Bf : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL1Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L1Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U1M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L1Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U1M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L1Bf : drain_stmt_L1Bf Edr_L1Bf.
Proof.
  rewrite Edr_eq_L1Bf.
  exact (f0_drain 1%nat QBf CST XGL HCST HXGL HCSTQ Cd_L1Bf TQ_L1Bf TQr_L1Bf sQ_L1Bf RQ_L1Bf HEQ_L1Bf HCK_L1Bf HTQ_L1Bf HTQr_L1Bf QCHK_L1Bf QCHKr_L1Bf Xf2_L1Bf XM2_L1Bf XR2_L1Bf XEX2_L1Bf sX2_L1Bf run7_L1Bf
           NX7_L1Bf RUN7_L1Bf L7_L1Bf run7r_L1Bf NX7r_L1Bf RUN7r_L1Bf L7r_L1Bf AXE2_L1Bf WXR2_L1Bf DXR2_L1Bf NXR2_L1Bf EQR2_L1Bf ENT2_L1Bf SID2_L1Bf HCSTF Edr_nf_L1Bf XMd_L1Bf XKd_L1Bf KEPTd_L1Bf RESTd_L1Bf XEXd_L1Bf
           AXEd_L1Bf OBJSd_L1Bf EQKd_L1Bf RCLSd_L1Bf RCIVd_L1Bf RCELLd_L1Bf RWRd_L1Bf RSHPd_L1Bf ECd_L1Bf FBCd_L1Bf).
Qed.
Theorem ef0_drain_L1Bf : edrain_stmt_L1Bf Edr_L1Bf.
Proof.
  rewrite Edr_eq_L1Bf.
  exact (ef0_drain 1%nat QBf CST XGL HCST HXGL HCSTQ Cd_L1Bf TQ_L1Bf TQr_L1Bf sQ_L1Bf RQ_L1Bf HEQ_L1Bf HCK_L1Bf HTQ_L1Bf HTQr_L1Bf QCHK_L1Bf QCHKr_L1Bf Xf2_L1Bf XM2_L1Bf XR2_L1Bf XEX2_L1Bf sX2_L1Bf run7_L1Bf
           NX7_L1Bf RUN7_L1Bf L7_L1Bf run7r_L1Bf NX7r_L1Bf RUN7r_L1Bf L7r_L1Bf AXE2_L1Bf WXR2_L1Bf DXR2_L1Bf NXR2_L1Bf EQR2_L1Bf ENT2_L1Bf SID2_L1Bf HCSTF Edr_nf_L1Bf XMd_L1Bf XKd_L1Bf KEPTd_L1Bf RESTd_L1Bf XEXd_L1Bf
           AXEd_L1Bf OBJSd_L1Bf EQKd_L1Bf RCLSd_L1Bf RCIVd_L1Bf RCELLd_L1Bf RWRd_L1Bf RSHPd_L1Bf ECd_L1Bf FBCd_L1Bf).
Qed.
End QL1Bf.
End F0A_qL1Bf.

(* [comment removed for export] *)
Module F0A_q2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_q2Bf"; "Cd_2Bf"; "XMd_2Bf"; "RQ_2Bf"; "XR2_2Bf"; "sQ_2Bf"; "RESTd_2Bf"; "TQ_2Bf"; "TQr_2Bf"; "XKd_2Bf"; "XM2_2Bf"; "KEPTd_2Bf"; "Xf2_2Bf"; "run7_2Bf"; "run7r_2Bf"; "nkd_2Bf"; "sX2_2Bf"; "Edr_nf_2Bf"; "XEX2_2Bf"; "XEXd_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs";
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_2Bf : axst := Eval vm_compute in Edr_2Bf.
Lemma Edr_eq_2Bf : Edr_2Bf = Edr_nf_2Bf. Proof. vm_cast_no_check (eq_refl Edr_nf_2Bf). Qed.

Definition XEXd_2Bf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_2Bf))].
Definition XMd_2Bf : axst := Eval vm_compute in (axf Edr_nf_2Bf XEXd_2Bf).
Lemma AXEd_2Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_2Bf)). Qed.
Definition nkd_2Bf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_2Bf) + 2 + 2)%nat.
Definition KEPTd_2Bf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_2Bf : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_2Bf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_2Bf : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_2Bf : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_2Bf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_2Bf : rcivb RESTd_2Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_2Bf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_2Bf : rwrb RESTd_2Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_2Bf : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_2Bf : axst := Eval vm_compute in (ax_with_facts XKd_2Bf (ss_facts (ax_S XKd_2Bf) ++ [F_cne])).
Lemma ECd_2Bf : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_2Bf). Qed.
Lemma FBCd_2Bf : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_2Bf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_2Bf) (ax_S PreQ3)).
Definition RQ_2Bf : list sobj := Eval vm_compute in (optR (entails_frA Cd_2Bf PreQ3 sQ_2Bf)).
Lemma HEQ_2Bf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_2Bf)). Qed.
Lemma HCK_2Bf : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_2Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_2Bf PreQ3 PostQ3 Cd_2Bf RQ_2Bf) (ss_facts (ax_S Cd_2Bf))).
Lemma HTQ_2Bf : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_2Bf). Qed.
Lemma QCHK_2Bf : ltac2:(tb__ "0|0|
S0S7S61U2S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_2Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_2Bf PreQ3 PostQ3r Cd_2Bf RQ_2Bf) (ss_facts (ax_S Cd_2Bf))).
Lemma HTQr_2Bf : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_2Bf). Qed.
Lemma QCHKr_2Bf : ltac2:(tb__ "0|0|
S0S7S61U2S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_2Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_2Bf).
Lemma RUN7_2Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_2Bf). Qed.
Definition Xf2_2Bf : axst := Eval vm_compute in (leaf 0 run7_2Bf).
Lemma L7_2Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_2Bf)]. Qed.
Lemma NX7_2Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_2Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_2Bf).
Lemma RUN7r_2Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_2Bf). Qed.
Lemma L7r_2Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_2Bf)]. Qed.
Lemma NX7r_2Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_2Bf : list axform := Eval vm_compute in (XEX_of Xf2_2Bf).
Definition XM2_2Bf : axst := Eval vm_compute in (axf Xf2_2Bf XEX2_2Bf).
Lemma AXE2_2Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_2Bf)). Qed.
Definition XR2_2Bf : axst := Eval vm_compute in (XR_of XM2_2Bf).
Definition sX2_2Bf : wsub := Eval vm_compute in (sX_of XR2_2Bf (Wcan 2) UStopLe).
Lemma WXR2_2Bf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_2Bf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_2Bf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_2Bf))). Qed.
Lemma EQR2_2Bf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_2Bf). Qed.
Lemma ENT2_2Bf : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU2A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_2Bf : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section Q2Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_2Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U2M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_2Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U2M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_2Bf : drain_stmt_2Bf Edr_2Bf.
Proof.
  rewrite Edr_eq_2Bf.
  exact (f0_drain 2%nat QBf CST XGL HCST HXGL HCSTQ Cd_2Bf TQ_2Bf TQr_2Bf sQ_2Bf RQ_2Bf HEQ_2Bf HCK_2Bf HTQ_2Bf HTQr_2Bf QCHK_2Bf QCHKr_2Bf Xf2_2Bf XM2_2Bf XR2_2Bf XEX2_2Bf sX2_2Bf run7_2Bf
           NX7_2Bf RUN7_2Bf L7_2Bf run7r_2Bf NX7r_2Bf RUN7r_2Bf L7r_2Bf AXE2_2Bf WXR2_2Bf DXR2_2Bf NXR2_2Bf EQR2_2Bf ENT2_2Bf SID2_2Bf HCSTF Edr_nf_2Bf XMd_2Bf XKd_2Bf KEPTd_2Bf RESTd_2Bf XEXd_2Bf
           AXEd_2Bf OBJSd_2Bf EQKd_2Bf RCLSd_2Bf RCIVd_2Bf RCELLd_2Bf RWRd_2Bf RSHPd_2Bf ECd_2Bf FBCd_2Bf).
Qed.
Theorem ef0_drain_2Bf : edrain_stmt_2Bf Edr_2Bf.
Proof.
  rewrite Edr_eq_2Bf.
  exact (ef0_drain 2%nat QBf CST XGL HCST HXGL HCSTQ Cd_2Bf TQ_2Bf TQr_2Bf sQ_2Bf RQ_2Bf HEQ_2Bf HCK_2Bf HTQ_2Bf HTQr_2Bf QCHK_2Bf QCHKr_2Bf Xf2_2Bf XM2_2Bf XR2_2Bf XEX2_2Bf sX2_2Bf run7_2Bf
           NX7_2Bf RUN7_2Bf L7_2Bf run7r_2Bf NX7r_2Bf RUN7r_2Bf L7r_2Bf AXE2_2Bf WXR2_2Bf DXR2_2Bf NXR2_2Bf EQR2_2Bf ENT2_2Bf SID2_2Bf HCSTF Edr_nf_2Bf XMd_2Bf XKd_2Bf KEPTd_2Bf RESTd_2Bf XEXd_2Bf
           AXEd_2Bf OBJSd_2Bf EQKd_2Bf RCLSd_2Bf RCIVd_2Bf RCELLd_2Bf RWRd_2Bf RSHPd_2Bf ECd_2Bf FBCd_2Bf).
Qed.
End Q2Bf.
End F0A_q2Bf.

(* [comment removed for export] *)
Module SegQCF_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "bool"; "nil"; "pair"; "prod"; "list"; "true"; "app"; "option"; "length"; "Some"; "false"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_facts"; "ss_next"; "SLit"; "SVar"; "valuation"; "ss_lenient"; "sprop_below"; "ss_objs"; "SMd"; "SPAlign"; "SPUle"; "cell"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQCF_states"; "C1"; "T1f"; "PreD"; "S0F"; "sDF"; "RF"; "sF"; "PostD"; "T1of"; "runF1"; "runF2"; "DQCb"; "L1"; "L2"; "TsF1"; "TsF2"; "VSF"; "DQC0"; "FFF"; "OBJF"; "O_szF"; "S0Fof"; "XCF"; "pcbF"; "permF"; "permG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "entsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "obj_subst"; "sprop_subst_opt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "AXUnbase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "NPRE"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "DH_ENT"; "O_dstD"; "F_clsD"; "F_fast"; "F_ghD"; "O_chkD"; "O_cntD"; "O_mcD"; "dst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "clsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states"; "QCRET"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "F_grow"; "O_stG"; "RTG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM"; "MC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "addf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "cbC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "addos"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition bump (X : axst) (nx : positive) : axst := ltac2:(tb__ "0|0|
S28VX;A1S26S2bVX;S20S23R1A1S24R1A1S22R1A1S21R1A1S25R1A1S1bR1A1S14R1A1Vnx;S19R1A1A9A2TS;").
Definition NXF : positive := 260%positive.
Definition DQC0 : axst := dropl DQCs.
Definition DQCb : axst := bump DQC0 NXF.
Lemma DQCb_ent : ltac2:(tb__ "0|0|
SfS2S49S3dS37S77A3S7A3"). Proof. vmr. Qed.

Definition pcbF : sv := ltac2:(tb__ "0|0|
S56S79S1cS6eS66S16Z50A1A3A2").
Definition sDF : wsub := ltac2:(tb__ "0|1|
S0S5SdS13A2M0S4SdS13P9eS66A4S0G0S4SdS13PaaS17Pe7A1A4S0G0S4SdS13Pe6S17Pd1A1A4S3G0A1A3A3A3").
Definition O_szF : sobj := ltac2:(tb__ "0|3|
S71S43Z8M0Z10S0S5S5SeS1A2M1S13A2M2S4G1S13S4SeS1G0U8A4S17Pc9A1A4S3G2A1A3A4").
Definition OBJF (g : bool) : list sobj := ltac2:(tb__ "0|2|
S8S11S76S8S11S0S11S4aS30S75A2S0S11S4aS30S62Z1M0A1A2S0S11S4aS30S64G0A1A2S0S11S4aS30S63Z2A1A2S0S11S40S0S11S72S3S11A1M1A3A3A3A3A3A3S2S6S11A1Lg;Vg;G1S0S11S4aS30S5eG0S3S1fA1A2A2G1A3X2x2A3A3").
Definition FFF (g : bool) : list sprop := ltac2:(tb__ "0|2|
S8S12S6dS12S12S12S9S12A1S12Lx;S4bS30R1A2S12R1Lh;R1X9x2Lf;S8S12S5fS8S12S61S0S12S2S12Lg;Vg;S74Z1M0A1S60G0A1X2x2S3S12A1M1A3A3A3A4S0S12S1dP97ZcA2S0S12S1eS16Z10000000000A1S17PaA1A2G1A3A3A3").
Definition S0Fof (g : bool) : axst := ltac2:(tb__ "0|0|
S78S7bS37S3fVg;A1A2S3eVg;A1A2").
Definition S0F_f : axst := Eval vm_compute in (S0Fof false).
Definition S0F_g : axst := Eval vm_compute in (S0Fof true).
Definition S0F (g : bool) : axst := if g then S0F_g else S0F_f.
Lemma S0F_eq : ltac2:(tb__ "0|0|
S2SfS27S41R1A1S2fR1A1A3Fg;"). Proof. intros [|]; vmr. Qed.

Definition runF1 (g : bool) : list leafA := ltac2:(tb__ "0|0|
S54U12cS0SeS5dS3SeA1A3S2fVg;A1A3").
Lemma runF1_eq : ltac2:(tb__ "0|0|
S2SfS6S29A1S54U12cS0SeS5dS3SeA1A3S2fR1A1A3S35R1A1A3Fg;"). Proof. intros g. unfold runF1. reflexivity. Qed.
Definition L1_f : axst := Eval vm_compute in (leaf 0 (runF1 false)).
Definition L1_g : axst := Eval vm_compute in (leaf 0 (runF1 true)).
Definition L1 (g : bool) : axst := if g then L1_g else L1_f.
Definition VSF : list positive := ltac2:(tb__ "0|0|
S0SdPa0S0SdPa1S0SdPa2S0SdPa3S0SdPa4S0SdPa5S0SdPa6S0SdPb8S0SdPb9S0SdPbaS0SdPbbS0SdPd0S0SdPc9S0SdPd1S0SdPddS0SdPdeS0SdPdfS0SdPe0S0SdPe1S0SdPe7S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition TsF1 (g : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S0S5S27S46A2M0S4S27S46S38Vg;A1S67S3cA1A4S3G0A1A3").
Lemma chkF1 : ltac2:(tb__ "0|0|
S2SfS2S47S15S28S2fR1A1A1A1S35R1A1S3aR1A1A3S7A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Definition permF : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U7S0S1U8S0S1U9S0S1UaS0S1U14S0S1U18S0S1U19S0S1U1aS0S1U1cS0S1U1dS0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U6S0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U15S0S1U16S0S1U17S0S1U1bS3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition permG : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U16S0S1U17S0S1U18S0S1U19S0S1U1aS0S1U1cS0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U6S0S1U1bS3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition XCF (g : bool) : list axform := ltac2:(tb__ "0|2|
S0S4eS50U0M0S16N30M1A1A2S0S4eS51G0G1A2S0S4eS4fS2S6S1A1Lg;Vg;S45S44X2x2A1S3S4eA1A3A3A3").
Definition C1_f : axst := Eval vm_compute in (match apply_axforms L1_f (XCF false) with Some Y => Y | None => L1_f end).
Definition C1_g : axst := Eval vm_compute in (match apply_axforms L1_g (XCF true) with Some Y => Y | None => L1_g end).
Definition C1 (g : bool) : axst := if g then C1_g else C1_f.
Lemma C1_eq : ltac2:(tb__ "0|0|
S2SfS9S27A1S52S38R1A1S42R1A1A2SbS27S2cR1A1A2A3Fg;"). Proof. intros [|]; vmr. Qed.
Definition PreD (g : bool) : axst := if g then Pre_dh_g 1 else Pre_dh_f 1.
Definition PostD (g : bool) : axst := if g then L_dh_g 1 else L_dh_f 1.

Definition sF (g : bool) : wsub := ltac2:(tb__ "0|0|
S0S5SdS13A2S4SdS13P94S16Z2000A1A4S6fP1S28S2cVg;A1A1S28S2eVg;A1A1A3A3").
Definition RF (g : bool) : list sobj := ltac2:(tb__ "0|0|
S7aS5aS2cVg;A1S2eVg;A1S32Vg;A1A3A1").
Lemma HeF : ltac2:(tb__ "0|1|
S2SfS9S6S11A1M0A1S5aS2cR1A1S2eR1A1S32R1A1A3SbG0S31R1A1A2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HchkF : ltac2:(tb__ "0|0|
S2SfS2S5bS2cR1A1S2eR1A1S32R1A1S31R1A1S0S27S33R1A1S3S27A1A3A5S7A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Definition T1of (g : bool) : axst := ltac2:(tb__ "0|0|
S5cS32Vg;A1S2eVg;A1S33Vg;A1S2cVg;A1S31Vg;A1A5").
Definition T1fof (g : bool) : axst := ltac2:(tb__ "0|0|
S59S34Vg;A1S14S28S2cVg;A1A1A1A2").
Definition T1f_f : axst := Eval vm_compute in (T1fof false).
Definition T1f_g : axst := Eval vm_compute in (T1fof true).
Definition T1f (g : bool) : axst := if g then T1f_g else T1f_f.
Lemma T1f_eq : ltac2:(tb__ "0|0|
S2SfS27S59S34R1A1S14S28S2cR1A1A1A1A2S2dR1A1A3Fg;"). Proof. intros [|]; vmr. Qed.
Lemma FBC1 : ltac2:(tb__ "0|1|
S2SfS2S6aS12S1aS15S28S2cR1A1A1M0A1A1S14G0A1A3S7A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma FBT1 : ltac2:(tb__ "0|0|
S2SfS2S6aS12S1aS15S28S34R1A1A1A1A1S14S28S2cR1A1A1A1A3S7A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Definition runF2 (g : bool) : list leafA := ltac2:(tb__ "0|0|
S54U12cS0SeS68S3SeA1A3S2dVg;A1A3").
Lemma runF2_eq : ltac2:(tb__ "0|0|
S2SfS6S29A1S54U12cS0SeS68S3SeA1A3S2dR1A1A3S36R1A1A3Fg;"). Proof. intros g. unfold runF2. reflexivity. Qed.
Definition L2_f : axst := Eval vm_compute in (leaf 0 (runF2 false)).
Definition L2_g : axst := Eval vm_compute in (leaf 0 (runF2 true)).
Definition L2 (g : bool) : axst := if g then L2_g else L2_f.
Definition TsF2 (g : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S0S5S27S46A2M0S4S27S46S39Vg;A1S67S3cA1A4S3G0A1A3").
Lemma chkF2 : ltac2:(tb__ "0|0|
S2SfS2S47S15S28S2dR1A1A1A1S36R1A1S3bR1A1A3S7A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Lemma RF_cov : ltac2:(tb__ "0|1|
S2SfS2S73S14S28S2dR1A1A1M0A1S31R1A1S1bG0A1A3S7A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma newF : ltac2:(tb__ "0|3|
S2SfS6S11A1M0S70S28S2eR1A1A1S28S33R1A1A1A2S2G0Lg;R1S0S11S4aS3S5SdS13A2A1S5eZ1M1S65G1A1A2A2S3S11A1M2A3G2X2x2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxF : ltac2:(tb__ "0|2|
S10S2S10SfS2S19S28S2fR1A1A1M0A1ScA3S6bS55S15G0A1A2A2Fg;S2S10SfS2S19S28S2dR1A1A1M1A1ScA3S6bS55S15G1A1A2A2Fg;A2").
Proof. split; intros [|]; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]). Qed.
Lemma shapesF : ltac2:(tb__ "0|7|
S2SfS5S5S5S5S1S1A2M0S1A2M1S6S5S13S13A2M2A1M3A2M4G3A2S4G4G3S4G1G3S4G0S1S4S1S1SaS29S35R1A1A2SaS29S36R1A1A2A4SaS11S31R1A1A2A4S2aS2cR1A1A1A4S2aS39R1A1A1A4S4G4G3S4G1G3S4G0S1S4S1S1U1M5G5A4S2S1Lg;R1U7U13X2x2A4S3G2A1M6A4G6A4A3Fg;").
Proof. intros [|]; vmr. Qed.
Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_F1 : ltac2:(tb__ "0|0|
S2S4dS18S6S6cQ40A1A1S58VQ;VX;R3A3S27S46S18S69S5S27S46A2S4S27S46R3R2A4S3aR8A1A3S48R3R7R2A3S57VQ;VX;S4cS53R9R5R3R7A5A3F_;F_;Frho';FM;FT;S57VQ;VX;S4cS53R5S2fR6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fg;").
Proof. intros g J rho tp HJ HC. exact (tr_piece X 300%nat _ (S0F g) (runF1 g) (TsF1 g) (runF1_eq g) (chkF1 g) (proj1 (proj1 nxF g)) (proj2 (proj1 nxF g)) J rho tp HJ HC). Qed.
Theorem seg_F2 : ltac2:(tb__ "0|0|
S2S4dS18S6S6cQ40A1A1S58VQ;VX;R3A3S27S46S18S69S5S27S46A2S4S27S46R3R2A4S3bR8A1A3S48R3R7R2A3S57VQ;VX;S4cS53R9R5R3R7A5A3F_;F_;Frho';FM;FT;S57VQ;VX;S4cS53R5S2dR6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fg;").
Proof. intros g J rho tp HJ HC. exact (tr_piece X 300%nat _ (T1f g) (runF2 g) (TsF2 g) (runF2_eq g) (chkF2 g) (proj1 (proj2 nxF g)) (proj2 (proj2 nxF g)) J rho tp HJ HC). Qed.
End TR.
End SegQCF_states.

