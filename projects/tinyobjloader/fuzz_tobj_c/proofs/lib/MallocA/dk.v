(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dh df dd.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.

(* [comment removed for export] *)
Module F0A_m1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A"; "q_1A"; "Ebg_1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "Edr_1A"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "Xf_1A"; "exits1_1A"; "W_1A"; "st_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A"; "PMID_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require de.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ck.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d1.F0A_xi1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ck.F0A_d1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_1A : ltac2:(tb__ "0|0|
SbS15S1eS5aS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_1A : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6cS12S6S2S1U1A1M4S0A3A1S5aG4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S6fA1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_1A : ltac2:(tb__ "0|0|
SbS15S1eS5cS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_1A : ltac2:(tb__ "0|0|
SbS15S1eS5dS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_1A__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaUbb8S57S59U1S0A2A4").
Lemma Certi_1A : ltac2:(tb__ "0|1|
SbS15S3dSaUbb8S57S48S59U1M0S0A2S14S10S58S1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 1 UStopLe) [MIDx (Wcan 1) UStopLe] Certi_1A__runs); [unfold Certi_1A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_1A : ltac2:(tb__ "0|2|
SbS15S3eSaUbb8S57S48S5bU1M0S0A2S14S3bS3cS58S1G0A1S0A2Z0M1S21G1A1A3S16S3bA1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 1 UStopLe) [mkVNA (MIDx (Wcan 1) UStopLe) 0 (SLit 0)] Certi_1A__runs); [unfold Certi_1A__runs; reflexivity | vmr]. Qed.

Definition PMID_1A : axst := ltac2:(tb__ "0|0|
S64S13S2fS30S24A4").
Definition Cert1m_1A__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaS5fS14S9S5eS16S9A1A3S14S10S3fS16S10A1A3A4").
Lemma Cert1m_1A : ltac2:(tb__ "0|0|
SbS15S3dSaS5fS14S9S5eS16S9A1A3S48S14S10S3fS16S10A1A3S2eA6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_1A] exits1_1A Cert1m_1A__runs); [unfold Cert1m_1A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_1A : ltac2:(tb__ "0|2|
SbS15S3eSaS5fS14S9S5eS16S9A1A3S48S14S3bS3cS3fZ1S21Z0M0A1M1A3S16S3bA1A3S6bS10S3bS10S3cR1G0G1A3LE;S2eA4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_1A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_1A) Cert1m_1A__runs); [unfold Cert1m_1A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_1A : ltac2:(tb__ "0|0|
SbS15S1eS65S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_1A : ltac2:(tb__ "0|0|
SbS15S1eS66S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_1A : ltac2:(tb__ "0|0|
SbS15S1eS67S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_1A : ltac2:(tb__ "0|2|
SbS19S10A1S6eS68S13S1U1M0A1M1S0S24A4S72G0S24A2A2S1bS10S64S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M1A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4eU1S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_1A : ltac2:(tb__ "0|1|
S9OF_;S54OF_;S4fS4S1dS1dS17S51Q40A1A1S53S5R5A1S47Vsegs;R8S46R6A1A3S4bR6R5A2S4cU1M0S0RbRaR9R8R6S26S2aR4AaS4cG0S0RcRbRaR9R7S27S2bR5AaS4cG0S0RdRcRbRaR8S28S2cR6AaS49ReRdRcRbR9S25R7A7S49RfReRdRcRaS29R8A7S49R10RfReRdRbS2dR9A7S1dS56Vsegs;R11S45Vsegs;VJFi;S13R10RfRdA4S3fR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_1A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_1A C3_1A Ems_1A C4_1A TM0_1A run4_1A RM_1A D3_1A W3_1A EQ3_1A NX3b_1A RUN4_1A L4_1A D4_1A W4_1A EQ4_1A
             HeM_1A HchkM_1A HTM_1A FBM_1A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_1A.
    apply (f0_s5 1%nat st q_1A false TM_1A Eq_1A EQ_1A TQ0_1A run5_1A RQ_1A NX5_1A RUN5_1A L5_1A AXQ_1A HeQ_1A HchkQ_1A HTQ_1A FBQ_1A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_1A.
    apply (f0_s6 1%nat st false TQ_1A Edr_1A Xf_1A run6_1A NX6_1A RUN6_1A L6_1A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true PMID_1A exits1_1A Cert1m_1A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_1A_1 C2_1A_1 EfD_1A_1 ED_1A_1 run2_1A_1 D2_1A_1 W2_1A_1 NX2_1A_1 EQ2_1A_1 RUN2_1A_1 L2_1A_1 AXD_1A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1A_1 TDr_1A_1 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_1 ENTD_1A_1 RUN3_1A L3_1A NX3_1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1A_2 C2_1A_2 EfD_1A_2 ED_1A_2 run2_1A_2 D2_1A_2 W2_1A_2 NX2_1A_2 EQ2_1A_2 RUN2_1A_2 L2_1A_2 AXD_1A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1A_2 TDr_1A_2 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_2 ENTD_1A_2 RUN3_1A L3_1A NX3_1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1A_3 C2_1A_3 EfD_1A_3 ED_1A_3 run2_1A_3 D2_1A_3 W2_1A_3 NX2_1A_3 EQ2_1A_3 RUN2_1A_3 L2_1A_3 AXD_1A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1A_3 TDr_1A_3 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_3 ENTD_1A_3 RUN3_1A L3_1A NX3_1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_1A : ltac2:(tb__ "0|1|
S9OF_;S4fS4S1dS1dS17S51Q40A1A1S54OF_;S5R5A1S4bR5R4A2S4dU1M0S0R9R8R7R5S26S2aR3A9S4dG0S0RaR9R8R6S27S2bR4A9S4dG0S0RbRaR9R7S28S2cR5A9S4aRcRbRaR8S25R6A6S4aRdRcRbR9S29R7A6S4aReRdRcRaS2dR8A6S1dS55Vsegs;S45Vsegs;VJFi;S13RfReRcA4S3fR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_1A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_1A C3_1A Ems_1A C4_1A TM0_1A run4_1A RM_1A D3_1A W3_1A EQ3_1A NX3b_1A RUN4_1A L4_1A D4_1A W4_1A EQ4_1A
             HeM_1A HchkM_1A HTM_1A FBM_1A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_1A.
    apply (ef0_s5 1%nat st q_1A false TM_1A Eq_1A EQ_1A TQ0_1A run5_1A RQ_1A NX5_1A RUN5_1A L5_1A AXQ_1A HeQ_1A HchkQ_1A HTQ_1A FBQ_1A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_1A.
    apply (ef0_s6 1%nat st false TQ_1A Edr_1A Xf_1A run6_1A NX6_1A RUN6_1A L6_1A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true PMID_1A exits1_1A (eq_refl : (GW <=? ss_next (ax_S PMID_1A))%positive = true) ECert1m_1A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_1A_1 C2_1A_1 EfD_1A_1 ED_1A_1 run2_1A_1 D2_1A_1 W2_1A_1 NX2_1A_1 EQ2_1A_1 RUN2_1A_1 L2_1A_1 AXD_1A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1A_1 TDr_1A_1 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_1 ENTD_1A_1 RUN3_1A L3_1A NX3_1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1A_2 C2_1A_2 EfD_1A_2 ED_1A_2 run2_1A_2 D2_1A_2 W2_1A_2 NX2_1A_2 EQ2_1A_2 RUN2_1A_2 L2_1A_2 AXD_1A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1A_2 TDr_1A_2 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_2 ENTD_1A_2 RUN3_1A L3_1A NX3_1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1A_3 C2_1A_3 EfD_1A_3 ED_1A_3 run2_1A_3 D2_1A_3 W2_1A_3 NX2_1A_3 EQ2_1A_3 RUN2_1A_3 L2_1A_3 AXD_1A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1A_3 TDr_1A_3 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_3 ENTD_1A_3 RUN3_1A L3_1A NX3_1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S40VCST;R1A2SfS40S73R2A2ScS41S39R2A2S42R2S3aA2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S40VCST;R1A2SdS75R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S40VCST;R1A2SdS74R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S40VCST;R1A2ScSdScS41S39R2A2S42R2S3aA2A2A1SdScS41Z180e88R2A2S42R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_hi_ia0_1A : ltac2:(tb__ "0|7|
S54OF_;S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S14S1aS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S16G1A1M5A3A5S53S5R6A1S47SaR9S46R7A1A3S6dSaRaS46R8A1A3S41S69S43R6Z10A2A2SbS15S50RbA1S1cA3S36S24RcA2S1dS9S35S63R10S33R10ReRcRbR2R1A6R3A3S62S37R11A1R4RdRcR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R13A1R6RfReR5R4A6A2S49S61VCST;VXGL;S37R14A1M6A3R15G6R13S33G6R7R10RfR6R5A6S25S32SaS44R7R11S14G1S18S10S31G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S70RfRdA2S56SaR10S45SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 Wai_1A Dai_1A Wbi_1A Wci_1A Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts true (Wcan 1) UStopLe q_1A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe q_1A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 1 UStopLe q_1A Wbm_1A Wcm_1A Wdm_1A Fb_1A XIm_1A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_1A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_1A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_1A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_1A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_1A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_1A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_1A : ltac2:(tb__ "0|7|
S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S14S1aS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S16G1A1M5A3A5S53S5R6A1S41S69S43R4Z10A2A2SbS15S50R9A1S1cA3S36S24RaA2S1dS9S35S63ReS33ReRcRaR9R2R1A6R3A3S62S37RfA1R4RbRaR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R11A1R6RdRcR5R4A6A2S4aS61VCST;VXGL;S37R12A1M6A3G6R11S33G6R7ReRdR6R5A6S25S32SaS44R7RfS14G1S18S10S31G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S71RbA1S55SaS45SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 Wai_1A Dai_1A Wbi_1A Wci_1A ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts true (Wcan 1) UStopLe q_1A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe q_1A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 1 UStopLe q_1A Wbm_1A Wcm_1A Wdm_1A Fb_1A XIm_1A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_1A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_1A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_1A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_1A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_1A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_1A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M1A.
End F0A_m1A.

(* [comment removed for export] *)
Module F0A_mL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A"; "q_L2A"; "Ebg_L2A"; "ED_L2A_1"; "ED_L2A_2"; "ED_L2A_3"; "ED_L2A_4"; "Edr_L2A"; "TD_L2A_1"; "TD_L2A_2"; "TD_L2A_3"; "TD_L2A_4"; "Xf_L2A"; "exits1_L2A"; "W_L2A"; "st_L2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_mL2A"; "PMID_L2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require db.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require df.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require au.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.db.F0A_qL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d7.F0A_xiL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cn.F0A_dL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.F0A_aL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L2A : ltac2:(tb__ "0|0|
SbS14S1eS5cS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L2A : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6eS12S6S2S1U2A1M4S0A3A1S5cG4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S71A1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L2A : ltac2:(tb__ "0|0|
SbS14S1eS5eS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L2A : ltac2:(tb__ "0|0|
SbS14S1eS5fS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L2A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaUbb8S59S5bU2S0A2A4").
Lemma Certi_L2A : ltac2:(tb__ "0|1|
SbS14S3fSaUbb8S59S4aS5bU2M0S0A2S13S10S5aS1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 2 UStopLe) [MIDx (Wcan 2) UStopLe] Certi_L2A__runs); [unfold Certi_L2A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L2A : ltac2:(tb__ "0|2|
SbS14S40SaUbb8S59S4aS5dU2M0S0A2S13S3dS3eS5aS1G0A1S0A2Z0M1S21G1A1A3S15S3dA1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 2 UStopLe) [mkVNA (MIDx (Wcan 2) UStopLe) 0 (SLit 0)] Certi_L2A__runs); [unfold Certi_L2A__runs; reflexivity | vmr]. Qed.

Definition PMID_L2A : axst := ltac2:(tb__ "0|0|
S66S19S31S32S24A4").
Definition Cert1m_L2A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaS61S13S9S60S15S9A1A3S13S10S41S15S10A1A3A4").
Lemma Cert1m_L2A : ltac2:(tb__ "0|0|
SbS14S3fSaS61S13S9S60S15S9A1A3S4aS13S10S41S15S10A1A3S30A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L2A] exits1_L2A Cert1m_L2A__runs); [unfold Cert1m_L2A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L2A : ltac2:(tb__ "0|2|
SbS14S40SaS61S13S9S60S15S9A1A3S4aS13S3dS3eS41Z1S21Z0M0A1M1A3S15S3dA1A3S6dS10S3dS10S3eR1G0G1A3LE;S30A4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L2A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L2A) Cert1m_L2A__runs); [unfold Cert1m_L2A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L2A : ltac2:(tb__ "0|0|
SbS14S1eS67S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L2A : ltac2:(tb__ "0|0|
SbS14S1eS68S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L2A : ltac2:(tb__ "0|0|
SbS14S1eS69S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L2A : ltac2:(tb__ "0|2|
SbS1aS10A1S70S6aS19S1U2M0A1M1S0S24A4S74G0S24A2A2S1cS10S66S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML2A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S50U2S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L2A : ltac2:(tb__ "0|1|
S9OF_;S56OF_;S51S4S1dS1dS17S53Q40A1A1S55S5R5A1S49Vsegs;R8S48R6A1A3S4fR6R5A2S4dU2M0S0RbRaR9R8R6S26S2bR4AaS4dG0S0RcRbRaR9R7S27S2cR5AaS4dG0S0RdRcRbRaR8S28S2dR6AaS4dG0S0ReRdRcRbR9S29S2eR7AaS4bRfReRdRcRaS25R8A7S4bR10RfReRdRbS2aR9A7S4bR11R10RfReRcS2fRaA7S1dS58Vsegs;R12S47Vsegs;VJFi;S16R11R10ReA4S41R1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L2A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_L2A C3_L2A Ems_L2A C4_L2A TM0_L2A run4_L2A RM_L2A D3_L2A W3_L2A EQ3_L2A NX3b_L2A RUN4_L2A L4_L2A D4_L2A W4_L2A EQ4_L2A
             HeM_L2A HchkM_L2A HTM_L2A FBM_L2A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L2A.
    apply (f0_s5 2%nat st q_L2A false TM_L2A Eq_L2A EQ_L2A TQ0_L2A run5_L2A RQ_L2A NX5_L2A RUN5_L2A L5_L2A AXQ_L2A HeQ_L2A HchkQ_L2A HTQ_L2A FBQ_L2A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L2A.
    apply (f0_s6 2%nat st false TQ_L2A Edr_L2A Xf_L2A run6_L2A NX6_L2A RUN6_L2A L6_L2A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true PMID_L2A exits1_L2A Cert1m_L2A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_L2A_1 C2_L2A_1 EfD_L2A_1 ED_L2A_1 run2_L2A_1 D2_L2A_1 W2_L2A_1 NX2_L2A_1 EQ2_L2A_1 RUN2_L2A_1 L2_L2A_1 AXD_L2A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_1 TDr_L2A_1 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_1 ENTD_L2A_1 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2A_2 C2_L2A_2 EfD_L2A_2 ED_L2A_2 run2_L2A_2 D2_L2A_2 W2_L2A_2 NX2_L2A_2 EQ2_L2A_2 RUN2_L2A_2 L2_L2A_2 AXD_L2A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_2 TDr_L2A_2 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_2 ENTD_L2A_2 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2A_3 C2_L2A_3 EfD_L2A_3 ED_L2A_3 run2_L2A_3 D2_L2A_3 W2_L2A_3 NX2_L2A_3 EQ2_L2A_3 RUN2_L2A_3 L2_L2A_3 AXD_L2A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_3 TDr_L2A_3 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_3 ENTD_L2A_3 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2A_4 C2_L2A_4 EfD_L2A_4 ED_L2A_4 run2_L2A_4 D2_L2A_4 W2_L2A_4 NX2_L2A_4 EQ2_L2A_4 RUN2_L2A_4 L2_L2A_4 AXD_L2A_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_4 TDr_L2A_4 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_4 ENTD_L2A_4 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L2A : ltac2:(tb__ "0|1|
S9OF_;S51S4S1dS1dS17S53Q40A1A1S56OF_;S5R5A1S4fR5R4A2S4eU2M0S0R9R8R7R5S26S2bR3A9S4eG0S0RaR9R8R6S27S2cR4A9S4eG0S0RbRaR9R7S28S2dR5A9S4eG0S0RcRbRaR8S29S2eR6A9S4cRdRcRbR9S25R7A6S4cReRdRcRaS2aR8A6S4cRfReRdRbS2fR9A6S1dS57Vsegs;S47Vsegs;VJFi;S16R10RfRdA4S41R1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L2A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_L2A C3_L2A Ems_L2A C4_L2A TM0_L2A run4_L2A RM_L2A D3_L2A W3_L2A EQ3_L2A NX3b_L2A RUN4_L2A L4_L2A D4_L2A W4_L2A EQ4_L2A
             HeM_L2A HchkM_L2A HTM_L2A FBM_L2A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L2A.
    apply (ef0_s5 2%nat st q_L2A false TM_L2A Eq_L2A EQ_L2A TQ0_L2A run5_L2A RQ_L2A NX5_L2A RUN5_L2A L5_L2A AXQ_L2A HeQ_L2A HchkQ_L2A HTQ_L2A FBQ_L2A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L2A.
    apply (ef0_s6 2%nat st false TQ_L2A Edr_L2A Xf_L2A run6_L2A NX6_L2A RUN6_L2A L6_L2A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true PMID_L2A exits1_L2A (eq_refl : (GW <=? ss_next (ax_S PMID_L2A))%positive = true) ECert1m_L2A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_L2A_1 C2_L2A_1 EfD_L2A_1 ED_L2A_1 run2_L2A_1 D2_L2A_1 W2_L2A_1 NX2_L2A_1 EQ2_L2A_1 RUN2_L2A_1 L2_L2A_1 AXD_L2A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_1 TDr_L2A_1 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_1 ENTD_L2A_1 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2A_2 C2_L2A_2 EfD_L2A_2 ED_L2A_2 run2_L2A_2 D2_L2A_2 W2_L2A_2 NX2_L2A_2 EQ2_L2A_2 RUN2_L2A_2 L2_L2A_2 AXD_L2A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_2 TDr_L2A_2 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_2 ENTD_L2A_2 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2A_3 C2_L2A_3 EfD_L2A_3 ED_L2A_3 run2_L2A_3 D2_L2A_3 W2_L2A_3 NX2_L2A_3 EQ2_L2A_3 RUN2_L2A_3 L2_L2A_3 AXD_L2A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_3 TDr_L2A_3 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_3 ENTD_L2A_3 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2A_4 C2_L2A_4 EfD_L2A_4 ED_L2A_4 run2_L2A_4 D2_L2A_4 W2_L2A_4 NX2_L2A_4 EQ2_L2A_4 RUN2_L2A_4 L2_L2A_4 AXD_L2A_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_4 TDr_L2A_4 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_4 ENTD_L2A_4 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SfS42S75R2A2ScS43S3bR2A2S44R2S3cA2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SdS77R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SdS76R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S42VCST;R1A2ScSdScS43S3bR2A2S44R2S3cA2A2A1SdScS43Z180e88R2A2S44R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_2A : ltac2:(tb__ "0|7|
S56OF_;S51S4S1dS17S53Q40M0A1A1S54G0S1fR2PcA2A2S9S54G0S1fR3PdA2A2S9S34SaS46R4R3S13S1bS10S33A2M1S18S10S33S8S2S1U2A1M2S0A3M3S3S3aSaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S55S5R6A1S49SaR9S48R7A1A3S6fSaRaS48R8A1A3S43S45R6R5A2S6bA2SbS14S52RbA1S19A3S38S24RcA2S1dS9S37S65R10S35R10ReRcRbR2R1A6R3A3S64S39R11A1R4RdRcR3R2A6SbS9S36R3A1S6cA3S4fR6S35S39R13A1R6RfReR5R4A6A2S4bS63VCST;VXGL;S39R14A1M6A3R15G6R13S35G6R7R10RfR6R5A6S25S34SaS46R7R11S13G1S18S10S33G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S72RfRdA2S58SaR10S47SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 Wai_L2A Dai_L2A Wbi_L2A Wci_L2A Certi_L2A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 2) UStopLe q_L2A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe q_L2A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 2 UStopLe q_L2A Wbm_L2A Wcm_L2A Wdm_L2A Fb_L2A XIm_L2A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L2A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L2A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2A_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L2A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L2A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_2A : ltac2:(tb__ "0|7|
S51S4S1dS17S53Q40M0A1A1S54G0S1fR2PcA2A2S9S54G0S1fR3PdA2A2S9S34SaS46R4R3S13S1bS10S33A2M1S18S10S33S8S2S1U2A1M2S0A3M3S3S3aSaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S55S5R6A1S43S45R4R3A2S6bA2SbS14S52R9A1S19A3S38S24RaA2S1dS9S37S65ReS35ReRcRaR9R2R1A6R3A3S64S39RfA1R4RbRaR3R2A6SbS9S36R3A1S6cA3S4fR6S35S39R11A1R6RdRcR5R4A6A2S4cS63VCST;VXGL;S39R12A1M6A3G6R11S35G6R7ReRdR6R5A6S25S34SaS46R7RfS13G1S18S10S33G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S73RbA1S57SaS47SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 Wai_L2A Dai_L2A Wbi_L2A Wci_L2A ECerti_L2A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 2) UStopLe q_L2A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe q_L2A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 2 UStopLe q_L2A Wbm_L2A Wcm_L2A Wdm_L2A Fb_L2A XIm_L2A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L2A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L2A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2A_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L2A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L2A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML2A.
End F0A_mL2A.

(* [comment removed for export] *)
Module F0A_m2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf"; "q_2Bf"; "Ebg_2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "Edr_2Bf"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "Xf_2Bf"; "exits1_2Bf"; "W_2Bf"; "st_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m2Bf"; "PMID_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_q2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d3.F0A_xi2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cn.F0A_d2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_a2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_2Bf : ltac2:(tb__ "0|0|
SbS15S1eS5cS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_2Bf : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6eS12S6S2S1U2A1M4S0A3A1S5cG4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S71A1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_2Bf : ltac2:(tb__ "0|0|
SbS15S1eS5eS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_2Bf : ltac2:(tb__ "0|0|
SbS15S1eS5fS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_2Bf__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaUbb8S59S5bU2S0A2A4").
Lemma Certi_2Bf : ltac2:(tb__ "0|1|
SbS15S3fSaUbb8S59S4aS5bU2M0S0A2S14S10S5aS1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 2 UStopLe) [MIDx (Wcan 2) UStopLe] Certi_2Bf__runs); [unfold Certi_2Bf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_2Bf : ltac2:(tb__ "0|2|
SbS15S40SaUbb8S59S4aS5dU2M0S0A2S14S3dS3eS5aS1G0A1S0A2Z0M1S21G1A1A3S16S3dA1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 2 UStopLe) [mkVNA (MIDx (Wcan 2) UStopLe) 0 (SLit 0)] Certi_2Bf__runs); [unfold Certi_2Bf__runs; reflexivity | vmr]. Qed.

Definition PMID_2Bf : axst := ltac2:(tb__ "0|0|
S66S13S31S32S24A4").
Definition Cert1m_2Bf__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaS61S14S9S60S16S9A1A3S14S10S41S16S10A1A3A4").
Lemma Cert1m_2Bf : ltac2:(tb__ "0|0|
SbS15S3fSaS61S14S9S60S16S9A1A3S4aS14S10S41S16S10A1A3S30A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_2Bf] exits1_2Bf Cert1m_2Bf__runs); [unfold Cert1m_2Bf__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_2Bf : ltac2:(tb__ "0|2|
SbS15S40SaS61S14S9S60S16S9A1A3S4aS14S3dS3eS41Z1S21Z0M0A1M1A3S16S3dA1A3S6dS10S3dS10S3eR1G0G1A3LE;S30A4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_2Bf 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_2Bf) Cert1m_2Bf__runs); [unfold Cert1m_2Bf__runs; reflexivity | vmr]. Qed.

Lemma Wbm_2Bf : ltac2:(tb__ "0|0|
SbS15S1eS67S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_2Bf : ltac2:(tb__ "0|0|
SbS15S1eS68S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_2Bf : ltac2:(tb__ "0|0|
SbS15S1eS69S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_2Bf : ltac2:(tb__ "0|2|
SbS19S10A1S70S6aS13S1U2M0A1M1S0S24A4S74G0S24A2A2S1bS10S66S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M2Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S50U2S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_2Bf : ltac2:(tb__ "0|1|
S9OF_;S56OF_;S51S4S1dS1dS17S53Q40A1A1S55S5R5A1S49Vsegs;R8S48R6A1A3S4fR6R5A2S4dU2M0S0RbRaR9R8R6S26S2bR4AaS4dG0S0RcRbRaR9R7S27S2cR5AaS4dG0S0RdRcRbRaR8S28S2dR6AaS4dG0S0ReRdRcRbR9S29S2eR7AaS4bRfReRdRcRaS25R8A7S4bR10RfReRdRbS2aR9A7S4bR11R10RfReRcS2fRaA7S1dS58Vsegs;R12S47Vsegs;VJFi;S13R11R10ReA4S41R1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_2Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_2Bf C3_2Bf Ems_2Bf C4_2Bf TM0_2Bf run4_2Bf RM_2Bf D3_2Bf W3_2Bf EQ3_2Bf NX3b_2Bf RUN4_2Bf L4_2Bf D4_2Bf W4_2Bf EQ4_2Bf
             HeM_2Bf HchkM_2Bf HTM_2Bf FBM_2Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_2Bf.
    apply (f0_s5 2%nat st q_2Bf false TM_2Bf Eq_2Bf EQ_2Bf TQ0_2Bf run5_2Bf RQ_2Bf NX5_2Bf RUN5_2Bf L5_2Bf AXQ_2Bf HeQ_2Bf HchkQ_2Bf HTQ_2Bf FBQ_2Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_2Bf.
    apply (f0_s6 2%nat st false TQ_2Bf Edr_2Bf Xf_2Bf run6_2Bf NX6_2Bf RUN6_2Bf L6_2Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true PMID_2Bf exits1_2Bf Cert1m_2Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_2Bf_1 C2_2Bf_1 EfD_2Bf_1 ED_2Bf_1 run2_2Bf_1 D2_2Bf_1 W2_2Bf_1 NX2_2Bf_1 EQ2_2Bf_1 RUN2_2Bf_1 L2_2Bf_1 AXD_2Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_1 TDr_2Bf_1 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_1 ENTD_2Bf_1 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Bf_2 C2_2Bf_2 EfD_2Bf_2 ED_2Bf_2 run2_2Bf_2 D2_2Bf_2 W2_2Bf_2 NX2_2Bf_2 EQ2_2Bf_2 RUN2_2Bf_2 L2_2Bf_2 AXD_2Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_2 TDr_2Bf_2 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_2 ENTD_2Bf_2 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Bf_3 C2_2Bf_3 EfD_2Bf_3 ED_2Bf_3 run2_2Bf_3 D2_2Bf_3 W2_2Bf_3 NX2_2Bf_3 EQ2_2Bf_3 RUN2_2Bf_3 L2_2Bf_3 AXD_2Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_3 TDr_2Bf_3 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_3 ENTD_2Bf_3 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Bf_4 C2_2Bf_4 EfD_2Bf_4 ED_2Bf_4 run2_2Bf_4 D2_2Bf_4 W2_2Bf_4 NX2_2Bf_4 EQ2_2Bf_4 RUN2_2Bf_4 L2_2Bf_4 AXD_2Bf_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_4 TDr_2Bf_4 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_4 ENTD_2Bf_4 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_2Bf : ltac2:(tb__ "0|1|
S9OF_;S51S4S1dS1dS17S53Q40A1A1S56OF_;S5R5A1S4fR5R4A2S4eU2M0S0R9R8R7R5S26S2bR3A9S4eG0S0RaR9R8R6S27S2cR4A9S4eG0S0RbRaR9R7S28S2dR5A9S4eG0S0RcRbRaR8S29S2eR6A9S4cRdRcRbR9S25R7A6S4cReRdRcRaS2aR8A6S4cRfReRdRbS2fR9A6S1dS57Vsegs;S47Vsegs;VJFi;S13R10RfRdA4S41R1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_2Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_2Bf C3_2Bf Ems_2Bf C4_2Bf TM0_2Bf run4_2Bf RM_2Bf D3_2Bf W3_2Bf EQ3_2Bf NX3b_2Bf RUN4_2Bf L4_2Bf D4_2Bf W4_2Bf EQ4_2Bf
             HeM_2Bf HchkM_2Bf HTM_2Bf FBM_2Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_2Bf.
    apply (ef0_s5 2%nat st q_2Bf false TM_2Bf Eq_2Bf EQ_2Bf TQ0_2Bf run5_2Bf RQ_2Bf NX5_2Bf RUN5_2Bf L5_2Bf AXQ_2Bf HeQ_2Bf HchkQ_2Bf HTQ_2Bf FBQ_2Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_2Bf.
    apply (ef0_s6 2%nat st false TQ_2Bf Edr_2Bf Xf_2Bf run6_2Bf NX6_2Bf RUN6_2Bf L6_2Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true PMID_2Bf exits1_2Bf (eq_refl : (GW <=? ss_next (ax_S PMID_2Bf))%positive = true) ECert1m_2Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_2Bf_1 C2_2Bf_1 EfD_2Bf_1 ED_2Bf_1 run2_2Bf_1 D2_2Bf_1 W2_2Bf_1 NX2_2Bf_1 EQ2_2Bf_1 RUN2_2Bf_1 L2_2Bf_1 AXD_2Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_1 TDr_2Bf_1 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_1 ENTD_2Bf_1 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Bf_2 C2_2Bf_2 EfD_2Bf_2 ED_2Bf_2 run2_2Bf_2 D2_2Bf_2 W2_2Bf_2 NX2_2Bf_2 EQ2_2Bf_2 RUN2_2Bf_2 L2_2Bf_2 AXD_2Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_2 TDr_2Bf_2 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_2 ENTD_2Bf_2 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Bf_3 C2_2Bf_3 EfD_2Bf_3 ED_2Bf_3 run2_2Bf_3 D2_2Bf_3 W2_2Bf_3 NX2_2Bf_3 EQ2_2Bf_3 RUN2_2Bf_3 L2_2Bf_3 AXD_2Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_3 TDr_2Bf_3 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_3 ENTD_2Bf_3 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Bf_4 C2_2Bf_4 EfD_2Bf_4 ED_2Bf_4 run2_2Bf_4 D2_2Bf_4 W2_2Bf_4 NX2_2Bf_4 EQ2_2Bf_4 RUN2_2Bf_4 L2_2Bf_4 AXD_2Bf_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_4 TDr_2Bf_4 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_4 ENTD_2Bf_4 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SfS42S75R2A2ScS43S3bR2A2S44R2S3cA2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SdS77R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SdS76R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S42VCST;R1A2ScSdScS43S3bR2A2S44R2S3cA2A2A1SdScS43Z180e88R2A2S44R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_hi_ia0_2Bf : ltac2:(tb__ "0|7|
S56OF_;S51S4S1dS17S53Q40M0A1A1S54G0S1fR2PcA2A2S9S54G0S1fR3PdA2A2S9S34SaS46R4R3S14S1aS10S33A2M1S18S10S33S8S2S1U2A1M2S0A3M3S3S3aSaA1M4VCST;VXGL;R6R5A5A4S16G1A1M5A3A5S55S5R6A1S49SaR9S48R7A1A3S6fSaRaS48R8A1A3S43S6bS45R6Z10A2A2SbS15S52RbA1S1cA3S38S24RcA2S1dS9S37S65R10S35R10ReRcRbR2R1A6R3A3S64S39R11A1R4RdRcR3R2A6SbS9S36R3A1S6cA3S4fR6S35S39R13A1R6RfReR5R4A6A2S4bS63VCST;VXGL;S39R14A1M6A3R15G6R13S35G6R7R10RfR6R5A6S25S34SaS46R7R11S14G1S18S10S33G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S72RfRdA2S58SaR10S47SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 Wai_2Bf Dai_2Bf Wbi_2Bf Wci_2Bf Certi_2Bf ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts true (Wcan 2) UStopLe q_2Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe q_2Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 2 UStopLe q_2Bf Wbm_2Bf Wcm_2Bf Wdm_2Bf Fb_2Bf XIm_2Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_2Bf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_2Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2Bf_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_2Bf CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_2Bf CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_2Bf : ltac2:(tb__ "0|7|
S51S4S1dS17S53Q40M0A1A1S54G0S1fR2PcA2A2S9S54G0S1fR3PdA2A2S9S34SaS46R4R3S14S1aS10S33A2M1S18S10S33S8S2S1U2A1M2S0A3M3S3S3aSaA1M4VCST;VXGL;R6R5A5A4S16G1A1M5A3A5S55S5R6A1S43S6bS45R4Z10A2A2SbS15S52R9A1S1cA3S38S24RaA2S1dS9S37S65ReS35ReRcRaR9R2R1A6R3A3S64S39RfA1R4RbRaR3R2A6SbS9S36R3A1S6cA3S4fR6S35S39R11A1R6RdRcR5R4A6A2S4cS63VCST;VXGL;S39R12A1M6A3G6R11S35G6R7ReRdR6R5A6S25S34SaS46R7RfS14G1S18S10S33G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S73RbA1S57SaS47SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 Wai_2Bf Dai_2Bf Wbi_2Bf Wci_2Bf ECerti_2Bf A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts true (Wcan 2) UStopLe q_2Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe q_2Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 2 UStopLe q_2Bf Wbm_2Bf Wcm_2Bf Wdm_2Bf Fb_2Bf XIm_2Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_2Bf (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_2Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2Bf_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_2Bf CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_2Bf CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M2Bf.
End F0A_m2Bf.

(* [comment removed for export] *)
Module F0A_mL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be"; "q_L2Be"; "Ebg_L2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "Edr_L2Be"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "Xf_L2Be"; "exits1_L2Be"; "W_L2Be"; "st_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_mL2Be"; "PMID_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require db.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require df.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require au.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.db.F0A_qL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d8.F0A_xiL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_dL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.F0A_aL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L2Be : ltac2:(tb__ "0|0|
SbS14S1eS5cS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L2Be : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6eS12S6S2S1U2A1M4S0A3A1S5cG4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S71A1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L2Be : ltac2:(tb__ "0|0|
SbS14S1eS5eS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L2Be : ltac2:(tb__ "0|0|
SbS14S1eS5fS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L2Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaUbb8S59S5bU2S0A2A4").
Lemma Certi_L2Be : ltac2:(tb__ "0|1|
SbS14S3fSaUbb8S59S4aS5bU2M0S0A2S13S10S5aS1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 2 UStopLe) [MIDx (Wcan 2) UStopLe] Certi_L2Be__runs); [unfold Certi_L2Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L2Be : ltac2:(tb__ "0|2|
SbS14S40SaUbb8S59S4aS5dU2M0S0A2S13S3dS3eS5aS1G0A1S0A2Z0M1S21G1A1A3S15S3dA1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 2 UStopLe) [mkVNA (MIDx (Wcan 2) UStopLe) 0 (SLit 0)] Certi_L2Be__runs); [unfold Certi_L2Be__runs; reflexivity | vmr]. Qed.

Definition PMID_L2Be : axst := ltac2:(tb__ "0|0|
S66S19S31S32S24A4").
Definition Cert1m_L2Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaS61S13S9S60S15S9A1A3S13S10S41S15S10A1A3A4").
Lemma Cert1m_L2Be : ltac2:(tb__ "0|0|
SbS14S3fSaS61S13S9S60S15S9A1A3S4aS13S10S41S15S10A1A3S30A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L2Be] exits1_L2Be Cert1m_L2Be__runs); [unfold Cert1m_L2Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L2Be : ltac2:(tb__ "0|2|
SbS14S40SaS61S13S9S60S15S9A1A3S4aS13S3dS3eS41Z1S21Z0M0A1M1A3S15S3dA1A3S6dS10S3dS10S3eR1G0G1A3LE;S30A4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L2Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L2Be) Cert1m_L2Be__runs); [unfold Cert1m_L2Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L2Be : ltac2:(tb__ "0|0|
SbS14S1eS67S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L2Be : ltac2:(tb__ "0|0|
SbS14S1eS68S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L2Be : ltac2:(tb__ "0|0|
SbS14S1eS69S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L2Be : ltac2:(tb__ "0|2|
SbS1aS10A1S70S6aS19S1U2M0A1M1S0S24A4S74G0S24A2A2S1cS10S66S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML2Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S50U2S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L2Be : ltac2:(tb__ "0|1|
S9OF_;S56OF_;S51S4S1dS1dS17S53Q40A1A1S55S5R5A1S49Vsegs;R8S48R6A1A3S4fR6R5A2S4dU2M0S0RbRaR9R8R6S26S2bR4AaS4dG0S0RcRbRaR9R7S27S2cR5AaS4dG0S0RdRcRbRaR8S28S2dR6AaS4dG0S0ReRdRcRbR9S29S2eR7AaS4bRfReRdRcRaS25R8A7S4bR10RfReRdRbS2aR9A7S4bR11R10RfReRcS2fRaA7S1dS58Vsegs;R12S47Vsegs;VJFi;S16R11R10ReA4S41R1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L2Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_L2Be C3_L2Be Ems_L2Be C4_L2Be TM0_L2Be run4_L2Be RM_L2Be D3_L2Be W3_L2Be EQ3_L2Be NX3b_L2Be RUN4_L2Be L4_L2Be D4_L2Be W4_L2Be EQ4_L2Be
             HeM_L2Be HchkM_L2Be HTM_L2Be FBM_L2Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L2Be.
    apply (f0_s5 2%nat st q_L2Be false TM_L2Be Eq_L2Be EQ_L2Be TQ0_L2Be run5_L2Be RQ_L2Be NX5_L2Be RUN5_L2Be L5_L2Be AXQ_L2Be HeQ_L2Be HchkQ_L2Be HTQ_L2Be FBQ_L2Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L2Be.
    apply (f0_s6 2%nat st false TQ_L2Be Edr_L2Be Xf_L2Be run6_L2Be NX6_L2Be RUN6_L2Be L6_L2Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true PMID_L2Be exits1_L2Be Cert1m_L2Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_L2Be_1 C2_L2Be_1 EfD_L2Be_1 ED_L2Be_1 run2_L2Be_1 D2_L2Be_1 W2_L2Be_1 NX2_L2Be_1 EQ2_L2Be_1 RUN2_L2Be_1 L2_L2Be_1 AXD_L2Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_1 TDr_L2Be_1 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_1 ENTD_L2Be_1 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Be_2 C2_L2Be_2 EfD_L2Be_2 ED_L2Be_2 run2_L2Be_2 D2_L2Be_2 W2_L2Be_2 NX2_L2Be_2 EQ2_L2Be_2 RUN2_L2Be_2 L2_L2Be_2 AXD_L2Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_2 TDr_L2Be_2 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_2 ENTD_L2Be_2 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Be_3 C2_L2Be_3 EfD_L2Be_3 ED_L2Be_3 run2_L2Be_3 D2_L2Be_3 W2_L2Be_3 NX2_L2Be_3 EQ2_L2Be_3 RUN2_L2Be_3 L2_L2Be_3 AXD_L2Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_3 TDr_L2Be_3 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_3 ENTD_L2Be_3 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Be_4 C2_L2Be_4 EfD_L2Be_4 ED_L2Be_4 run2_L2Be_4 D2_L2Be_4 W2_L2Be_4 NX2_L2Be_4 EQ2_L2Be_4 RUN2_L2Be_4 L2_L2Be_4 AXD_L2Be_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_4 TDr_L2Be_4 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_4 ENTD_L2Be_4 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L2Be : ltac2:(tb__ "0|1|
S9OF_;S51S4S1dS1dS17S53Q40A1A1S56OF_;S5R5A1S4fR5R4A2S4eU2M0S0R9R8R7R5S26S2bR3A9S4eG0S0RaR9R8R6S27S2cR4A9S4eG0S0RbRaR9R7S28S2dR5A9S4eG0S0RcRbRaR8S29S2eR6A9S4cRdRcRbR9S25R7A6S4cReRdRcRaS2aR8A6S4cRfReRdRbS2fR9A6S1dS57Vsegs;S47Vsegs;VJFi;S16R10RfRdA4S41R1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L2Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_L2Be C3_L2Be Ems_L2Be C4_L2Be TM0_L2Be run4_L2Be RM_L2Be D3_L2Be W3_L2Be EQ3_L2Be NX3b_L2Be RUN4_L2Be L4_L2Be D4_L2Be W4_L2Be EQ4_L2Be
             HeM_L2Be HchkM_L2Be HTM_L2Be FBM_L2Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L2Be.
    apply (ef0_s5 2%nat st q_L2Be false TM_L2Be Eq_L2Be EQ_L2Be TQ0_L2Be run5_L2Be RQ_L2Be NX5_L2Be RUN5_L2Be L5_L2Be AXQ_L2Be HeQ_L2Be HchkQ_L2Be HTQ_L2Be FBQ_L2Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L2Be.
    apply (ef0_s6 2%nat st false TQ_L2Be Edr_L2Be Xf_L2Be run6_L2Be NX6_L2Be RUN6_L2Be L6_L2Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true PMID_L2Be exits1_L2Be (eq_refl : (GW <=? ss_next (ax_S PMID_L2Be))%positive = true) ECert1m_L2Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_L2Be_1 C2_L2Be_1 EfD_L2Be_1 ED_L2Be_1 run2_L2Be_1 D2_L2Be_1 W2_L2Be_1 NX2_L2Be_1 EQ2_L2Be_1 RUN2_L2Be_1 L2_L2Be_1 AXD_L2Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_1 TDr_L2Be_1 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_1 ENTD_L2Be_1 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Be_2 C2_L2Be_2 EfD_L2Be_2 ED_L2Be_2 run2_L2Be_2 D2_L2Be_2 W2_L2Be_2 NX2_L2Be_2 EQ2_L2Be_2 RUN2_L2Be_2 L2_L2Be_2 AXD_L2Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_2 TDr_L2Be_2 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_2 ENTD_L2Be_2 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Be_3 C2_L2Be_3 EfD_L2Be_3 ED_L2Be_3 run2_L2Be_3 D2_L2Be_3 W2_L2Be_3 NX2_L2Be_3 EQ2_L2Be_3 RUN2_L2Be_3 L2_L2Be_3 AXD_L2Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_3 TDr_L2Be_3 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_3 ENTD_L2Be_3 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Be_4 C2_L2Be_4 EfD_L2Be_4 ED_L2Be_4 run2_L2Be_4 D2_L2Be_4 W2_L2Be_4 NX2_L2Be_4 EQ2_L2Be_4 RUN2_L2Be_4 L2_L2Be_4 AXD_L2Be_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_4 TDr_L2Be_4 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_4 ENTD_L2Be_4 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SfS42S75R2A2ScS43S3bR2A2S44R2S3cA2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SdS77R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S42VCST;R1A2SdS76R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S42VCST;R1A2ScSdScS43S3bR2A2S44R2S3cA2A2A1SdScS43Z180e88R2A2S44R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_2Be : ltac2:(tb__ "0|7|
S56OF_;S51S4S1dS17S53Q40M0A1A1S54G0S1fR2PcA2A2S9S54G0S1fR3PdA2A2S9S34SaS46R4R3S13S1bS10S33A2M1S18S10S33S8S2S1U2A1M2S0A3M3S3S3aSaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S55S5R6A1S49SaR9S48R7A1A3S6fSaRaS48R8A1A3S43S45R6R5A2S6bA2SbS14S52RbA1S19A3S38S24RcA2S1dS9S37S65R10S35R10ReRcRbR2R1A6R3A3S64S39R11A1R4RdRcR3R2A6SbS9S36R3A1S6cA3S4fR6S35S39R13A1R6RfReR5R4A6A2S4bS63VCST;VXGL;S39R14A1M6A3R15G6R13S35G6R7R10RfR6R5A6S25S34SaS46R7R11S13G1S18S10S33G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S72RfRdA2S58SaR10S47SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 Wai_L2Be Dai_L2Be Wbi_L2Be Wci_L2Be Certi_L2Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 2) UStopLe q_L2Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe q_L2Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 2 UStopLe q_L2Be Wbm_L2Be Wcm_L2Be Wdm_L2Be Fb_L2Be XIm_L2Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L2Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L2Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2Be_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L2Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L2Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_2Be : ltac2:(tb__ "0|7|
S51S4S1dS17S53Q40M0A1A1S54G0S1fR2PcA2A2S9S54G0S1fR3PdA2A2S9S34SaS46R4R3S13S1bS10S33A2M1S18S10S33S8S2S1U2A1M2S0A3M3S3S3aSaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S55S5R6A1S43S45R4R3A2S6bA2SbS14S52R9A1S19A3S38S24RaA2S1dS9S37S65ReS35ReRcRaR9R2R1A6R3A3S64S39RfA1R4RbRaR3R2A6SbS9S36R3A1S6cA3S4fR6S35S39R11A1R6RdRcR5R4A6A2S4cS63VCST;VXGL;S39R12A1M6A3G6R11S35G6R7ReRdR6R5A6S25S34SaS46R7RfS13G1S18S10S33G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S73RbA1S57SaS47SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 Wai_L2Be Dai_L2Be Wbi_L2Be Wci_L2Be ECerti_L2Be A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 2) UStopLe q_L2Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe q_L2Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 2 UStopLe q_L2Be Wbm_L2Be Wcm_L2Be Wdm_L2Be Fb_L2Be XIm_L2Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L2Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L2Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2Be_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L2Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L2Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML2Be.
End F0A_mL2Be.

(* [comment removed for export] *)
Module F0A_m0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be"; "q_0Be"; "Ebg_0Be"; "ED_0Be_1"; "ED_0Be_2"; "Edr_0Be"; "TD_0Be_1"; "TD_0Be_2"; "Xf_0Be"; "exits1_0Be"; "W_0Be"; "st_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m0Be"; "PMID_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require db.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ck.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.db.F0A_q0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d1.F0A_xi0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ck.F0A_d0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_0Be : ltac2:(tb__ "0|0|
SbS15S1eS58S1U0A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_0Be : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S6dA1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_0Be : ltac2:(tb__ "0|0|
SbS15S1eS5aS1U0A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_0Be : ltac2:(tb__ "0|0|
SbS15S1eS5bS1U0A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_0Be__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_0Be : ltac2:(tb__ "0|1|
SbS15S3bSaUbb8S55S46S57U0M0S0A2S14S10S56S1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_0Be__runs); [unfold Certi_0Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_0Be : ltac2:(tb__ "0|2|
SbS15S3cSaUbb8S55S46S59U0M0S0A2S14S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S16S39A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_0Be__runs); [unfold Certi_0Be__runs; reflexivity | vmr]. Qed.

Definition PMID_0Be : axst := ltac2:(tb__ "0|0|
S62S13S2dS2eS24A4").
Definition Cert1m_0Be__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS14S9S5cS16S9A1A3S14S10S3dS16S10A1A3A4").
Lemma Cert1m_0Be : ltac2:(tb__ "0|0|
SbS15S3bSaS5dS14S9S5cS16S9A1A3S46S14S10S3dS16S10A1A3S2cA6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_0Be] exits1_0Be Cert1m_0Be__runs); [unfold Cert1m_0Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_0Be : ltac2:(tb__ "0|2|
SbS15S3cSaS5dS14S9S5cS16S9A1A3S46S14S39S3aS3dZ1S21Z0M0A1M1A3S16S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_0Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_0Be) Cert1m_0Be__runs); [unfold Cert1m_0Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_0Be : ltac2:(tb__ "0|0|
SbS15S1eS63S1U0A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_0Be : ltac2:(tb__ "0|0|
SbS15S1eS64S1U0A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_0Be : ltac2:(tb__ "0|0|
SbS15S1eS65S1U0A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_0Be : ltac2:(tb__ "0|2|
SbS19S10A1S6cS66S13S1U0M0A1M1S0S24A4S70G0S24A2A2S1bS10S62S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_0Be : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S13RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0Be C3_0Be Ems_0Be C4_0Be TM0_0Be run4_0Be RM_0Be D3_0Be W3_0Be EQ3_0Be NX3b_0Be RUN4_0Be L4_0Be D4_0Be W4_0Be EQ4_0Be
             HeM_0Be HchkM_0Be HTM_0Be FBM_0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0Be.
    apply (f0_s5 0%nat st q_0Be false TM_0Be Eq_0Be EQ_0Be TQ0_0Be run5_0Be RQ_0Be NX5_0Be RUN5_0Be L5_0Be AXQ_0Be HeQ_0Be HchkQ_0Be HTQ_0Be FBQ_0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0Be.
    apply (f0_s6 0%nat st false TQ_0Be Edr_0Be Xf_0Be run6_0Be NX6_0Be RUN6_0Be L6_0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_0Be exits1_0Be Cert1m_0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0Be_1 C2_0Be_1 EfD_0Be_1 ED_0Be_1 run2_0Be_1 D2_0Be_1 W2_0Be_1 NX2_0Be_1 EQ2_0Be_1 RUN2_0Be_1 L2_0Be_1 AXD_0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Be_1 TDr_0Be_1 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_1 ENTD_0Be_1 RUN3_0Be L3_0Be NX3_0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0Be_2 C2_0Be_2 EfD_0Be_2 ED_0Be_2 run2_0Be_2 D2_0Be_2 W2_0Be_2 NX2_0Be_2 EQ2_0Be_2 RUN2_0Be_2 L2_0Be_2 AXD_0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Be_2 TDr_0Be_2 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_2 ENTD_0Be_2 RUN3_0Be L3_0Be NX3_0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_0Be : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S13ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0Be C3_0Be Ems_0Be C4_0Be TM0_0Be run4_0Be RM_0Be D3_0Be W3_0Be EQ3_0Be NX3b_0Be RUN4_0Be L4_0Be D4_0Be W4_0Be EQ4_0Be
             HeM_0Be HchkM_0Be HTM_0Be FBM_0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0Be.
    apply (ef0_s5 0%nat st q_0Be false TM_0Be Eq_0Be EQ_0Be TQ0_0Be run5_0Be RQ_0Be NX5_0Be RUN5_0Be L5_0Be AXQ_0Be HeQ_0Be HchkQ_0Be HTQ_0Be FBQ_0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0Be.
    apply (ef0_s6 0%nat st false TQ_0Be Edr_0Be Xf_0Be run6_0Be NX6_0Be RUN6_0Be L6_0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_0Be exits1_0Be (eq_refl : (GW <=? ss_next (ax_S PMID_0Be))%positive = true) ECert1m_0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0Be_1 C2_0Be_1 EfD_0Be_1 ED_0Be_1 run2_0Be_1 D2_0Be_1 W2_0Be_1 NX2_0Be_1 EQ2_0Be_1 RUN2_0Be_1 L2_0Be_1 AXD_0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Be_1 TDr_0Be_1 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_1 ENTD_0Be_1 RUN3_0Be L3_0Be NX3_0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0Be_2 C2_0Be_2 EfD_0Be_2 ED_0Be_2 run2_0Be_2 D2_0Be_2 W2_0Be_2 NX2_0Be_2 EQ2_0Be_2 RUN2_0Be_2 L2_0Be_2 AXD_0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Be_2 TDr_0Be_2 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_2 ENTD_0Be_2 RUN3_0Be L3_0Be NX3_0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SfS3eS71R2A2ScS3fS37R2A2S40R2S38A2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS73R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS72R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ180e88R2A2S40R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_hi_ia0_0Be : ltac2:(tb__ "0|7|
S52OF_;S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S14S1aS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S16G1A1M5A3A5S51S5R6A1S45SaR9S44R7A1A3S6bSaRaS44R8A1A3S3fS67S41R6Z10A2A2SbS15S4eRbA1S1cA3S34S24RcA2S1dS9S33S61R10S31R10ReRcRbR2R1A6R3A3S60S35R11A1R4RdRcR3R2A6SbS9S32R3A1S68A3S49R6S31S35R13A1R6RfReR5R4A6A2S47S5fVCST;VXGL;S35R14A1M6A3R15G6R13S31G6R7R10RfR6R5A6S25S30SaS42R7R11S14G1S18S10S2fG3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S6eRfRdA2S54SaR10S43SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 Wai_0Be Dai_0Be Wbi_0Be Wci_0Be Certi_0Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts true (Wcan 0) UStopLe q_0Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe q_0Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 0 UStopLe q_0Be Wbm_0Be Wcm_0Be Wdm_0Be Fb_0Be XIm_0Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_0Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_0Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_0Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_0Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_0Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_0Be : ltac2:(tb__ "0|7|
S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S14S1aS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S16G1A1M5A3A5S51S5R6A1S3fS67S41R4Z10A2A2SbS15S4eR9A1S1cA3S34S24RaA2S1dS9S33S61ReS31ReRcRaR9R2R1A6R3A3S60S35RfA1R4RbRaR3R2A6SbS9S32R3A1S68A3S49R6S31S35R11A1R6RdRcR5R4A6A2S48S5fVCST;VXGL;S35R12A1M6A3G6R11S31G6R7ReRdR6R5A6S25S30SaS42R7RfS14G1S18S10S2fG3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S6fRbA1S53SaS43SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 Wai_0Be Dai_0Be Wbi_0Be Wci_0Be ECerti_0Be A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts true (Wcan 0) UStopLe q_0Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe q_0Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 0 UStopLe q_0Be Wbm_0Be Wcm_0Be Wdm_0Be Fb_0Be XIm_0Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_0Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_0Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_0Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_0Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_0Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M0Be.
End F0A_m0Be.

(* [comment removed for export] *)
Module SegQ3D_top.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "and"; "eq"; "True"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostsQ3"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_cache_inited"; "aa_q_thread"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs"; "QC_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SegQ3D_qis"; "QI_full_step"; "QI_sec_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_sum"; "PM_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.SegQ3D_top"; "q3_arms2"; "q3_arms2E"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "qbounded"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "trk"; "trC"; "trS"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.SegQ3D_rec"; "q3_arms"; "q3_armsE"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require df.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQ3_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.SegQ3D_rec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SegQ3D_qis OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition q3_arms2 (ok : world -> Prop) (Kc : KcA) : Prop := ltac2:(tb__ "0|6|
S11S16S8S25Q40A1A1M0S4S2S8S10A1M1S13R3A1SaS10A1A3A1S2S9S12R4A1SbA3S20R5A1S24S14R6A1S18A2S23Vok;S5S0S6R6R5S7S19VKc;A1M2R7A2A5M3A2S21G3A1S1G1S1cG2R9R8S5S0S6R8R7S7G2R9A2A5M4R2R1G0S3L_;M5A7Frest;S1G1S1bG2R9R8G4R2R1G5A7Frest;S1G1S1aG2R9R8G4R2R1G5A7Frest;S1dG2R8R7R6S5S0S6R7R6S7G2R8A2A5R1A6A2A2A2TX;F_;F_;F_;F_;Ftp;Frho;FA;").
Definition q3_arms2E (Kc : KcA) : Prop := ltac2:(tb__ "0|6|
S11S16S8S25Q40A1A1M0S4S2S8S10A1M1S13R3A1SaS10A1A3A1S2S9S12R4A1SbA3S20R5A1S24S14R6A1S18A2S22S5S0S6R6R5S7S19VKc;A1M2R7A2A5M3A1S21G3A1S1G1S1cG2R9R8S5S0S6R8R7S7G2R9A2A5M4R2R1G0S3L_;M5A7Frest;S1G1S1bG2R9R8G4R2R1G5A7Frest;S1G1S1aG2R9R8G4R2R1G5A7Frest;S1dG2R8R7R6S5S0S6R7R6S7G2R8A2A5R1A6A2A2A2TX;F_;F_;F_;F_;Ftp;Frho;FA;").

Theorem q3_arms_of_arms2 : ltac2:(tb__ "0|0|
S15OF_;SeSfR1A1SdS0R3ScR2A1A3S17S0R4ScR3A1A3S1eR5R4A2S28R6R5A2F_;F_;F_;F_;FKc;Fok;").
Proof.
  intros ok Kc HKc Hok Hokp HA A rho tp HT HCI HQB HBD. destruct (HA A rho tp HT HCI HQB HBD) as (HQIS & HQIF & HQCF & HPM). cbv zeta in HQIS, HQIF, HQCF, HPM |- *.
  pose proof (K0_laws Kc HKc) as HL. pose proof (fun A0 => K0_ok_frame ok Kc A0 Hok) as HOKK.
  set (X := trS ok (LQPA segsA NPRE rho tp (PostsQ3 (K0 Kc) A))) in *.
  assert (HJD : forall A1 tmp rest, JOK X (JRD (K0 Kc) A rho A1 tmp rest)) by (intros; split; [apply JRD_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRD_stable; exact HL]]).
  assert (HJI : forall A1 a n0 nd its tmp rest, JOK X (JRI (K0 Kc) A rho A1 a n0 nd its tmp rest)) by (intros; split; [apply JRI_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRI_stable; exact HL]]).
  split; [|split; [|exact HPM]].
  - intros rest. exact (QI_step_of_arms (K0 Kc) HL (K0_secband Kc) A rho X HJI rest _ (HQIS rest) (HQIF rest)).
  - intros rest. exact (QC_step_of_full (K0 Kc) HL A rho X HJD HJI rest _ (HQCF rest)).
Qed.
Theorem q3_armsE_of_arms2 : ltac2:(tb__ "0|0|
SeSfR1A1S1fR2A1S29R3A1F_;F_;FKc;").
Proof.
  intros Kc HKc HA A rho tp HT HCI HQB HBD. destruct (HA A rho tp HT HCI HQB HBD) as (HQIS & HQIF & HQCF & HPM). cbv zeta in HQIS, HQIF, HQCF, HPM |- *.
  pose proof (K0_laws Kc HKc) as HL.
  set (X := trC (LQPA segsA NPRE rho tp (PostsQ3 (K0 Kc) A))) in *.
  assert (HJD : forall A1 tmp rest, JOK X (JRD (K0 Kc) A rho A1 tmp rest)) by (intros; apply JRD_stable; exact HL).
  assert (HJI : forall A1 a n0 nd its tmp rest, JOK X (JRI (K0 Kc) A rho A1 a n0 nd its tmp rest)) by (intros; apply JRI_stable; exact HL).
  split; [|split; [|exact HPM]].
  - intros rest. exact (QI_step_of_arms (K0 Kc) HL (K0_secband Kc) A rho X HJI rest _ (HQIS rest) (HQIF rest)).
  - intros rest. exact (QC_step_of_full (K0 Kc) HL A rho X HJD HJI rest _ (HQCF rest)).
Qed.

Corollary drain_sum_of_arms2 : ltac2:(tb__ "0|0|
S15OF_;SeSfR1A1SdS0R3ScR2A1A3S17S0R4ScR3A1A3S1eR5R4A2S26R6R5A2F_;F_;F_;F_;FKc;Fok;").
Proof. intros ok Kc HKc Hok Hokp HA. exact (drain_sum_of_arms ok Kc HKc Hok Hokp (q3_arms_of_arms2 ok Kc HKc Hok Hokp HA)). Qed.
Corollary drain_sumE_of_arms2 : ltac2:(tb__ "0|0|
SeSfR1A1S1fR2A1S27R3A1F_;F_;FKc;").
Proof. intros Kc HKc HA. exact (drain_sumE_of_arms Kc HKc (q3_armsE_of_arms2 Kc HKc HA)). Qed.
End SegQ3D_top.

