(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ll li lf.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt jo lm.

(* [comment removed for export] *)
Module F0A_mL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf"; "q_L1Bf"; "Ebg_L1Bf"; "ED_L1Bf_1"; "ED_L1Bf_2"; "ED_L1Bf_3"; "Edr_L1Bf"; "TD_L1Bf_1"; "TD_L1Bf_2"; "TD_L1Bf_3"; "Xf_L1Bf"; "exits1_L1Bf"; "W_L1Bf"; "st_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_mL1Bf"; "PMID_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iz.F0A_iL1Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ll.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.F0A_qL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lb.F0A_xiL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_dL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ll.F0A_aL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iz.F0A_iL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L1Bf : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L1Bf : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6cS12S6S2S1U1A1M4S0A3A1S5aG4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6fA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L1Bf : ltac2:(tb__ "0|0|
SbS14S1eS5cS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L1Bf : ltac2:(tb__ "0|0|
SbS14S1eS5dS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L1Bf__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaUbb8S57S59U1S0A2A4").
Lemma Certi_L1Bf : ltac2:(tb__ "0|1|
SbS14S3dSaUbb8S57S48S59U1M0S0A2S13S10S58S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 1 UStopLe) [MIDx (Wcan 1) UStopLe] Certi_L1Bf__runs); [unfold Certi_L1Bf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L1Bf : ltac2:(tb__ "0|2|
SbS14S3eSaUbb8S57S48S5bU1M0S0A2S13S3bS3cS58S1G0A1S0A2Z0M1S21G1A1A3S15S3bA1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 1 UStopLe) [mkVNA (MIDx (Wcan 1) UStopLe) 0 (SLit 0)] Certi_L1Bf__runs); [unfold Certi_L1Bf__runs; reflexivity | vmr]. Qed.

Definition PMID_L1Bf : axst := ltac2:(tb__ "0|0|
S64S19S2fS30S24A4").
Definition Cert1m_L1Bf__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaS5fS13S9S5eS15S9A1A3S13S10S3fS15S10A1A3A4").
Lemma Cert1m_L1Bf : ltac2:(tb__ "0|0|
SbS14S3dSaS5fS13S9S5eS15S9A1A3S48S13S10S3fS15S10A1A3S2eA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L1Bf] exits1_L1Bf Cert1m_L1Bf__runs); [unfold Cert1m_L1Bf__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L1Bf : ltac2:(tb__ "0|2|
SbS14S3eSaS5fS13S9S5eS15S9A1A3S48S13S3bS3cS3fZ1S21Z0M0A1M1A3S15S3bA1A3S6bS10S3bS10S3cR1G0G1A3LE;S2eA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L1Bf 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1Bf) Cert1m_L1Bf__runs); [unfold Cert1m_L1Bf__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L1Bf : ltac2:(tb__ "0|0|
SbS14S1eS65S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L1Bf : ltac2:(tb__ "0|0|
SbS14S1eS66S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L1Bf : ltac2:(tb__ "0|0|
SbS14S1eS67S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L1Bf : ltac2:(tb__ "0|2|
SbS1aS10A1S6eS68S19S1U1M0A1M1S0S24A4S72G0S24A2A2S1cS10S64S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML1Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4eU1S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L1Bf : ltac2:(tb__ "0|1|
S9OF_;S54OF_;S4fS4S1dS1dS17S51Q40A1A1S53S5R5A1S47Vsegs;R8S46R6A1A3S4bR6R5A2S4cU1M0S0RbRaR9R8R6S26S2aR4AaS4cG0S0RcRbRaR9R7S27S2bR5AaS4cG0S0RdRcRbRaR8S28S2cR6AaS49ReRdRcRbR9S25R7A7S49RfReRdRcRaS29R8A7S49R10RfReRdRbS2dR9A7S1dS56Vsegs;R11S45Vsegs;VJFi;S16R10RfRdA4S3fR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1Bf C3_L1Bf Ems_L1Bf C4_L1Bf TM0_L1Bf run4_L1Bf RM_L1Bf D3_L1Bf W3_L1Bf EQ3_L1Bf NX3b_L1Bf RUN4_L1Bf L4_L1Bf D4_L1Bf W4_L1Bf EQ4_L1Bf
             HeM_L1Bf HchkM_L1Bf HTM_L1Bf FBM_L1Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1Bf.
    apply (f0_s5 1%nat st q_L1Bf false TM_L1Bf Eq_L1Bf EQ_L1Bf TQ0_L1Bf run5_L1Bf RQ_L1Bf NX5_L1Bf RUN5_L1Bf L5_L1Bf AXQ_L1Bf HeQ_L1Bf HchkQ_L1Bf HTQ_L1Bf FBQ_L1Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1Bf.
    apply (f0_s6 1%nat st false TQ_L1Bf Edr_L1Bf Xf_L1Bf run6_L1Bf NX6_L1Bf RUN6_L1Bf L6_L1Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true PMID_L1Bf exits1_L1Bf Cert1m_L1Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1Bf_1 C2_L1Bf_1 EfD_L1Bf_1 ED_L1Bf_1 run2_L1Bf_1 D2_L1Bf_1 W2_L1Bf_1 NX2_L1Bf_1 EQ2_L1Bf_1 RUN2_L1Bf_1 L2_L1Bf_1 AXD_L1Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Bf_1 TDr_L1Bf_1 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_1 ENTD_L1Bf_1 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Bf_2 C2_L1Bf_2 EfD_L1Bf_2 ED_L1Bf_2 run2_L1Bf_2 D2_L1Bf_2 W2_L1Bf_2 NX2_L1Bf_2 EQ2_L1Bf_2 RUN2_L1Bf_2 L2_L1Bf_2 AXD_L1Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Bf_2 TDr_L1Bf_2 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_2 ENTD_L1Bf_2 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Bf_3 C2_L1Bf_3 EfD_L1Bf_3 ED_L1Bf_3 run2_L1Bf_3 D2_L1Bf_3 W2_L1Bf_3 NX2_L1Bf_3 EQ2_L1Bf_3 RUN2_L1Bf_3 L2_L1Bf_3 AXD_L1Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Bf_3 TDr_L1Bf_3 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_3 ENTD_L1Bf_3 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L1Bf : ltac2:(tb__ "0|1|
S9OF_;S4fS4S1dS1dS17S51Q40A1A1S54OF_;S5R5A1S4bR5R4A2S4dU1M0S0R9R8R7R5S26S2aR3A9S4dG0S0RaR9R8R6S27S2bR4A9S4dG0S0RbRaR9R7S28S2cR5A9S4aRcRbRaR8S25R6A6S4aRdRcRbR9S29R7A6S4aReRdRcRaS2dR8A6S1dS55Vsegs;S45Vsegs;VJFi;S16RfReRcA4S3fR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1Bf C3_L1Bf Ems_L1Bf C4_L1Bf TM0_L1Bf run4_L1Bf RM_L1Bf D3_L1Bf W3_L1Bf EQ3_L1Bf NX3b_L1Bf RUN4_L1Bf L4_L1Bf D4_L1Bf W4_L1Bf EQ4_L1Bf
             HeM_L1Bf HchkM_L1Bf HTM_L1Bf FBM_L1Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1Bf.
    apply (ef0_s5 1%nat st q_L1Bf false TM_L1Bf Eq_L1Bf EQ_L1Bf TQ0_L1Bf run5_L1Bf RQ_L1Bf NX5_L1Bf RUN5_L1Bf L5_L1Bf AXQ_L1Bf HeQ_L1Bf HchkQ_L1Bf HTQ_L1Bf FBQ_L1Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1Bf.
    apply (ef0_s6 1%nat st false TQ_L1Bf Edr_L1Bf Xf_L1Bf run6_L1Bf NX6_L1Bf RUN6_L1Bf L6_L1Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true PMID_L1Bf exits1_L1Bf (eq_refl : (GW <=? ss_next (ax_S PMID_L1Bf))%positive = true) ECert1m_L1Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1Bf_1 C2_L1Bf_1 EfD_L1Bf_1 ED_L1Bf_1 run2_L1Bf_1 D2_L1Bf_1 W2_L1Bf_1 NX2_L1Bf_1 EQ2_L1Bf_1 RUN2_L1Bf_1 L2_L1Bf_1 AXD_L1Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Bf_1 TDr_L1Bf_1 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_1 ENTD_L1Bf_1 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Bf_2 C2_L1Bf_2 EfD_L1Bf_2 ED_L1Bf_2 run2_L1Bf_2 D2_L1Bf_2 W2_L1Bf_2 NX2_L1Bf_2 EQ2_L1Bf_2 RUN2_L1Bf_2 L2_L1Bf_2 AXD_L1Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Bf_2 TDr_L1Bf_2 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_2 ENTD_L1Bf_2 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Bf_3 C2_L1Bf_3 EfD_L1Bf_3 ED_L1Bf_3 run2_L1Bf_3 D2_L1Bf_3 W2_L1Bf_3 NX2_L1Bf_3 EQ2_L1Bf_3 RUN2_L1Bf_3 L2_L1Bf_3 AXD_L1Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Bf_3 TDr_L1Bf_3 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_3 ENTD_L1Bf_3 RUN3_L1Bf L3_L1Bf NX3_L1Bf
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
S9S40VCST;R1A2ScSdScS41S39R2A2S42R2S3aA2A2A1SdScS41Z17db48R2A2S42R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_1Bf : ltac2:(tb__ "0|7|
S54OF_;S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S13S1bS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S53S5R6A1S47SaR9S46R7A1A3S6dSaRaS46R8A1A3S41S43R6R5A2S69A2SbS14S50RbA1S19A3S36S24RcA2S1dS9S35S63R10S33R10ReRcRbR2R1A6R3A3S62S37R11A1R4RdRcR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R13A1R6RfReR5R4A6A2S49S61VCST;VXGL;S37R14A1M6A3R15G6R13S33G6R7R10RfR6R5A6S25S32SaS44R7R11S13G1S18S10S31G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S70RfRdA2S56SaR10S45SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 Wai_L1Bf Dai_L1Bf Wbi_L1Bf Wci_L1Bf Certi_L1Bf ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts false (Wcan 1) UStopLe q_L1Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe q_L1Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 1 UStopLe q_L1Bf Wbm_L1Bf Wcm_L1Bf Wdm_L1Bf Fb_L1Bf XIm_L1Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L1Bf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L1Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L1Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L1Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L1Bf CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L1Bf CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_1Bf : ltac2:(tb__ "0|7|
S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S13S1bS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S53S5R6A1S41S43R4R3A2S69A2SbS14S50R9A1S19A3S36S24RaA2S1dS9S35S63ReS33ReRcRaR9R2R1A6R3A3S62S37RfA1R4RbRaR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R11A1R6RdRcR5R4A6A2S4aS61VCST;VXGL;S37R12A1M6A3G6R11S33G6R7ReRdR6R5A6S25S32SaS44R7RfS13G1S18S10S31G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S71RbA1S55SaS45SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 Wai_L1Bf Dai_L1Bf Wbi_L1Bf Wci_L1Bf ECerti_L1Bf A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts false (Wcan 1) UStopLe q_L1Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe q_L1Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 1 UStopLe q_L1Bf Wbm_L1Bf Wcm_L1Bf Wdm_L1Bf Fb_L1Bf XIm_L1Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L1Bf (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L1Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L1Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L1Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L1Bf CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L1Bf CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML1Bf.
End F0A_mL1Bf.

(* [comment removed for export] *)
Module F0A_mL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be"; "q_L1Be"; "Ebg_L1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "Edr_L1Be"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "Xf_L1Be"; "exits1_L1Be"; "W_L1Be"; "st_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_mL1Be"; "PMID_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require li.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.F0A_qL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lb.F0A_xiL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_dL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.li.F0A_aL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L1Be : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L1Be : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6cS12S6S2S1U1A1M4S0A3A1S5aG4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6fA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L1Be : ltac2:(tb__ "0|0|
SbS14S1eS5cS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L1Be : ltac2:(tb__ "0|0|
SbS14S1eS5dS1U1A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L1Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaUbb8S57S59U1S0A2A4").
Lemma Certi_L1Be : ltac2:(tb__ "0|1|
SbS14S3dSaUbb8S57S48S59U1M0S0A2S13S10S58S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 1 UStopLe) [MIDx (Wcan 1) UStopLe] Certi_L1Be__runs); [unfold Certi_L1Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L1Be : ltac2:(tb__ "0|2|
SbS14S3eSaUbb8S57S48S5bU1M0S0A2S13S3bS3cS58S1G0A1S0A2Z0M1S21G1A1A3S15S3bA1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 1 UStopLe) [mkVNA (MIDx (Wcan 1) UStopLe) 0 (SLit 0)] Certi_L1Be__runs); [unfold Certi_L1Be__runs; reflexivity | vmr]. Qed.

Definition PMID_L1Be : axst := ltac2:(tb__ "0|0|
S64S19S2fS30S24A4").
Definition Cert1m_L1Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaS5fS13S9S5eS15S9A1A3S13S10S3fS15S10A1A3A4").
Lemma Cert1m_L1Be : ltac2:(tb__ "0|0|
SbS14S3dSaS5fS13S9S5eS15S9A1A3S48S13S10S3fS15S10A1A3S2eA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L1Be] exits1_L1Be Cert1m_L1Be__runs); [unfold Cert1m_L1Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L1Be : ltac2:(tb__ "0|2|
SbS14S3eSaS5fS13S9S5eS15S9A1A3S48S13S3bS3cS3fZ1S21Z0M0A1M1A3S15S3bA1A3S6bS10S3bS10S3cR1G0G1A3LE;S2eA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L1Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1Be) Cert1m_L1Be__runs); [unfold Cert1m_L1Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L1Be : ltac2:(tb__ "0|0|
SbS14S1eS65S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L1Be : ltac2:(tb__ "0|0|
SbS14S1eS66S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L1Be : ltac2:(tb__ "0|0|
SbS14S1eS67S1U1A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L1Be : ltac2:(tb__ "0|2|
SbS1aS10A1S6eS68S19S1U1M0A1M1S0S24A4S72G0S24A2A2S1cS10S64S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML1Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4eU1S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L1Be : ltac2:(tb__ "0|1|
S9OF_;S54OF_;S4fS4S1dS1dS17S51Q40A1A1S53S5R5A1S47Vsegs;R8S46R6A1A3S4bR6R5A2S4cU1M0S0RbRaR9R8R6S26S2aR4AaS4cG0S0RcRbRaR9R7S27S2bR5AaS4cG0S0RdRcRbRaR8S28S2cR6AaS49ReRdRcRbR9S25R7A7S49RfReRdRcRaS29R8A7S49R10RfReRdRbS2dR9A7S1dS56Vsegs;R11S45Vsegs;VJFi;S16R10RfRdA4S3fR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1Be C3_L1Be Ems_L1Be C4_L1Be TM0_L1Be run4_L1Be RM_L1Be D3_L1Be W3_L1Be EQ3_L1Be NX3b_L1Be RUN4_L1Be L4_L1Be D4_L1Be W4_L1Be EQ4_L1Be
             HeM_L1Be HchkM_L1Be HTM_L1Be FBM_L1Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1Be.
    apply (f0_s5 1%nat st q_L1Be false TM_L1Be Eq_L1Be EQ_L1Be TQ0_L1Be run5_L1Be RQ_L1Be NX5_L1Be RUN5_L1Be L5_L1Be AXQ_L1Be HeQ_L1Be HchkQ_L1Be HTQ_L1Be FBQ_L1Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1Be.
    apply (f0_s6 1%nat st false TQ_L1Be Edr_L1Be Xf_L1Be run6_L1Be NX6_L1Be RUN6_L1Be L6_L1Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true PMID_L1Be exits1_L1Be Cert1m_L1Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1Be_1 C2_L1Be_1 EfD_L1Be_1 ED_L1Be_1 run2_L1Be_1 D2_L1Be_1 W2_L1Be_1 NX2_L1Be_1 EQ2_L1Be_1 RUN2_L1Be_1 L2_L1Be_1 AXD_L1Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_1 TDr_L1Be_1 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_1 ENTD_L1Be_1 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Be_2 C2_L1Be_2 EfD_L1Be_2 ED_L1Be_2 run2_L1Be_2 D2_L1Be_2 W2_L1Be_2 NX2_L1Be_2 EQ2_L1Be_2 RUN2_L1Be_2 L2_L1Be_2 AXD_L1Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_2 TDr_L1Be_2 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_2 ENTD_L1Be_2 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Be_3 C2_L1Be_3 EfD_L1Be_3 ED_L1Be_3 run2_L1Be_3 D2_L1Be_3 W2_L1Be_3 NX2_L1Be_3 EQ2_L1Be_3 RUN2_L1Be_3 L2_L1Be_3 AXD_L1Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_3 TDr_L1Be_3 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_3 ENTD_L1Be_3 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L1Be : ltac2:(tb__ "0|1|
S9OF_;S4fS4S1dS1dS17S51Q40A1A1S54OF_;S5R5A1S4bR5R4A2S4dU1M0S0R9R8R7R5S26S2aR3A9S4dG0S0RaR9R8R6S27S2bR4A9S4dG0S0RbRaR9R7S28S2cR5A9S4aRcRbRaR8S25R6A6S4aRdRcRbR9S29R7A6S4aReRdRcRaS2dR8A6S1dS55Vsegs;S45Vsegs;VJFi;S16RfReRcA4S3fR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1Be C3_L1Be Ems_L1Be C4_L1Be TM0_L1Be run4_L1Be RM_L1Be D3_L1Be W3_L1Be EQ3_L1Be NX3b_L1Be RUN4_L1Be L4_L1Be D4_L1Be W4_L1Be EQ4_L1Be
             HeM_L1Be HchkM_L1Be HTM_L1Be FBM_L1Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1Be.
    apply (ef0_s5 1%nat st q_L1Be false TM_L1Be Eq_L1Be EQ_L1Be TQ0_L1Be run5_L1Be RQ_L1Be NX5_L1Be RUN5_L1Be L5_L1Be AXQ_L1Be HeQ_L1Be HchkQ_L1Be HTQ_L1Be FBQ_L1Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1Be.
    apply (ef0_s6 1%nat st false TQ_L1Be Edr_L1Be Xf_L1Be run6_L1Be NX6_L1Be RUN6_L1Be L6_L1Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true PMID_L1Be exits1_L1Be (eq_refl : (GW <=? ss_next (ax_S PMID_L1Be))%positive = true) ECert1m_L1Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1Be_1 C2_L1Be_1 EfD_L1Be_1 ED_L1Be_1 run2_L1Be_1 D2_L1Be_1 W2_L1Be_1 NX2_L1Be_1 EQ2_L1Be_1 RUN2_L1Be_1 L2_L1Be_1 AXD_L1Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_1 TDr_L1Be_1 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_1 ENTD_L1Be_1 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Be_2 C2_L1Be_2 EfD_L1Be_2 ED_L1Be_2 run2_L1Be_2 D2_L1Be_2 W2_L1Be_2 NX2_L1Be_2 EQ2_L1Be_2 RUN2_L1Be_2 L2_L1Be_2 AXD_L1Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_2 TDr_L1Be_2 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_2 ENTD_L1Be_2 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Be_3 C2_L1Be_3 EfD_L1Be_3 ED_L1Be_3 run2_L1Be_3 D2_L1Be_3 W2_L1Be_3 NX2_L1Be_3 EQ2_L1Be_3 RUN2_L1Be_3 L2_L1Be_3 AXD_L1Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_3 TDr_L1Be_3 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_3 ENTD_L1Be_3 RUN3_L1Be L3_L1Be NX3_L1Be
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
S9S40VCST;R1A2ScSdScS41S39R2A2S42R2S3aA2A2A1SdScS41Z17db48R2A2S42R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_1Be : ltac2:(tb__ "0|7|
S54OF_;S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S13S1bS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S53S5R6A1S47SaR9S46R7A1A3S6dSaRaS46R8A1A3S41S43R6R5A2S69A2SbS14S50RbA1S19A3S36S24RcA2S1dS9S35S63R10S33R10ReRcRbR2R1A6R3A3S62S37R11A1R4RdRcR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R13A1R6RfReR5R4A6A2S49S61VCST;VXGL;S37R14A1M6A3R15G6R13S33G6R7R10RfR6R5A6S25S32SaS44R7R11S13G1S18S10S31G3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S70RfRdA2S56SaR10S45SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 Wai_L1Be Dai_L1Be Wbi_L1Be Wci_L1Be Certi_L1Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts false (Wcan 1) UStopLe q_L1Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe q_L1Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 1 UStopLe q_L1Be Wbm_L1Be Wcm_L1Be Wdm_L1Be Fb_L1Be XIm_L1Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L1Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L1Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L1Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L1Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L1Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L1Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_1Be : ltac2:(tb__ "0|7|
S4fS4S1dS17S51Q40M0A1A1S52G0S1fR2PcA2A2S9S52G0S1fR3PdA2A2S9S32SaS44R4R3S13S1bS10S31A2M1S18S10S31S8S2S1U1A1M2S0A3M3S3S38SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S53S5R6A1S41S43R4R3A2S69A2SbS14S50R9A1S19A3S36S24RaA2S1dS9S35S63ReS33ReRcRaR9R2R1A6R3A3S62S37RfA1R4RbRaR3R2A6SbS9S34R3A1S6aA3S4bR6S33S37R11A1R6RdRcR5R4A6A2S4aS61VCST;VXGL;S37R12A1M6A3G6R11S33G6R7ReRdR6R5A6S25S32SaS44R7RfS13G1S18S10S31G3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S71RbA1S55SaS45SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 Wai_L1Be Dai_L1Be Wbi_L1Be Wci_L1Be ECerti_L1Be A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts false (Wcan 1) UStopLe q_L1Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe q_L1Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 1 UStopLe q_L1Be Wbm_L1Be Wcm_L1Be Wdm_L1Be Fb_L1Be XIm_L1Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L1Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L1Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L1Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L1Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L1Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L1Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML1Be.
End F0A_mL1Be.

(* [comment removed for export] *)
Module F0A_m2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "q_2A"; "Ebg_2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "Edr_2A"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "Xf_2A"; "exits1_2A"; "W_2A"; "st_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A"; "PMID_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_q2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_xi2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_d2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0A_a2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_2A : ltac2:(tb__ "0|0|
SbS15S1eS5cS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_2A : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6eS12S6S2S1U2A1M4S0A3A1S5cG4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S71A1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_2A : ltac2:(tb__ "0|0|
SbS15S1eS5eS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_2A : ltac2:(tb__ "0|0|
SbS15S1eS5fS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_2A__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaUbb8S59S5bU2S0A2A4").
Lemma Certi_2A : ltac2:(tb__ "0|1|
SbS15S3fSaUbb8S59S4aS5bU2M0S0A2S14S10S5aS1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 2 UStopLe) [MIDx (Wcan 2) UStopLe] Certi_2A__runs); [unfold Certi_2A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_2A : ltac2:(tb__ "0|2|
SbS15S40SaUbb8S59S4aS5dU2M0S0A2S14S3dS3eS5aS1G0A1S0A2Z0M1S21G1A1A3S16S3dA1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 2 UStopLe) [mkVNA (MIDx (Wcan 2) UStopLe) 0 (SLit 0)] Certi_2A__runs); [unfold Certi_2A__runs; reflexivity | vmr]. Qed.

Definition PMID_2A : axst := ltac2:(tb__ "0|0|
S66S13S31S32S24A4").
Definition Cert1m_2A__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaS61S14S9S60S16S9A1A3S14S10S41S16S10A1A3A4").
Lemma Cert1m_2A : ltac2:(tb__ "0|0|
SbS15S3fSaS61S14S9S60S16S9A1A3S4aS14S10S41S16S10A1A3S30A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_2A] exits1_2A Cert1m_2A__runs); [unfold Cert1m_2A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_2A : ltac2:(tb__ "0|2|
SbS15S40SaS61S14S9S60S16S9A1A3S4aS14S3dS3eS41Z1S21Z0M0A1M1A3S16S3dA1A3S6dS10S3dS10S3eR1G0G1A3LE;S30A4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_2A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_2A) Cert1m_2A__runs); [unfold Cert1m_2A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_2A : ltac2:(tb__ "0|0|
SbS15S1eS67S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_2A : ltac2:(tb__ "0|0|
SbS15S1eS68S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_2A : ltac2:(tb__ "0|0|
SbS15S1eS69S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_2A : ltac2:(tb__ "0|2|
SbS19S10A1S70S6aS13S1U2M0A1M1S0S24A4S74G0S24A2A2S1bS10S66S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M2A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S50U2S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_2A : ltac2:(tb__ "0|1|
S9OF_;S56OF_;S51S4S1dS1dS17S53Q40A1A1S55S5R5A1S49Vsegs;R8S48R6A1A3S4fR6R5A2S4dU2M0S0RbRaR9R8R6S26S2bR4AaS4dG0S0RcRbRaR9R7S27S2cR5AaS4dG0S0RdRcRbRaR8S28S2dR6AaS4dG0S0ReRdRcRbR9S29S2eR7AaS4bRfReRdRcRaS25R8A7S4bR10RfReRdRbS2aR9A7S4bR11R10RfReRcS2fRaA7S1dS58Vsegs;R12S47Vsegs;VJFi;S13R11R10ReA4S41R1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_2A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_2A C3_2A Ems_2A C4_2A TM0_2A run4_2A RM_2A D3_2A W3_2A EQ3_2A NX3b_2A RUN4_2A L4_2A D4_2A W4_2A EQ4_2A
             HeM_2A HchkM_2A HTM_2A FBM_2A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_2A.
    apply (f0_s5 2%nat st q_2A false TM_2A Eq_2A EQ_2A TQ0_2A run5_2A RQ_2A NX5_2A RUN5_2A L5_2A AXQ_2A HeQ_2A HchkQ_2A HTQ_2A FBQ_2A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_2A.
    apply (f0_s6 2%nat st false TQ_2A Edr_2A Xf_2A run6_2A NX6_2A RUN6_2A L6_2A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true PMID_2A exits1_2A Cert1m_2A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_2A_1 C2_2A_1 EfD_2A_1 ED_2A_1 run2_2A_1 D2_2A_1 W2_2A_1 NX2_2A_1 EQ2_2A_1 RUN2_2A_1 L2_2A_1 AXD_2A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_1 TDr_2A_1 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_1 ENTD_2A_1 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2A_2 C2_2A_2 EfD_2A_2 ED_2A_2 run2_2A_2 D2_2A_2 W2_2A_2 NX2_2A_2 EQ2_2A_2 RUN2_2A_2 L2_2A_2 AXD_2A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_2 TDr_2A_2 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_2 ENTD_2A_2 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2A_3 C2_2A_3 EfD_2A_3 ED_2A_3 run2_2A_3 D2_2A_3 W2_2A_3 NX2_2A_3 EQ2_2A_3 RUN2_2A_3 L2_2A_3 AXD_2A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_3 TDr_2A_3 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_3 ENTD_2A_3 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2A_4 C2_2A_4 EfD_2A_4 ED_2A_4 run2_2A_4 D2_2A_4 W2_2A_4 NX2_2A_4 EQ2_2A_4 RUN2_2A_4 L2_2A_4 AXD_2A_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_4 TDr_2A_4 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_4 ENTD_2A_4 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_2A : ltac2:(tb__ "0|1|
S9OF_;S51S4S1dS1dS17S53Q40A1A1S56OF_;S5R5A1S4fR5R4A2S4eU2M0S0R9R8R7R5S26S2bR3A9S4eG0S0RaR9R8R6S27S2cR4A9S4eG0S0RbRaR9R7S28S2dR5A9S4eG0S0RcRbRaR8S29S2eR6A9S4cRdRcRbR9S25R7A6S4cReRdRcRaS2aR8A6S4cRfReRdRbS2fR9A6S1dS57Vsegs;S47Vsegs;VJFi;S13R10RfRdA4S41R1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_2A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_2A C3_2A Ems_2A C4_2A TM0_2A run4_2A RM_2A D3_2A W3_2A EQ3_2A NX3b_2A RUN4_2A L4_2A D4_2A W4_2A EQ4_2A
             HeM_2A HchkM_2A HTM_2A FBM_2A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_2A.
    apply (ef0_s5 2%nat st q_2A false TM_2A Eq_2A EQ_2A TQ0_2A run5_2A RQ_2A NX5_2A RUN5_2A L5_2A AXQ_2A HeQ_2A HchkQ_2A HTQ_2A FBQ_2A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_2A.
    apply (ef0_s6 2%nat st false TQ_2A Edr_2A Xf_2A run6_2A NX6_2A RUN6_2A L6_2A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true PMID_2A exits1_2A (eq_refl : (GW <=? ss_next (ax_S PMID_2A))%positive = true) ECert1m_2A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_2A_1 C2_2A_1 EfD_2A_1 ED_2A_1 run2_2A_1 D2_2A_1 W2_2A_1 NX2_2A_1 EQ2_2A_1 RUN2_2A_1 L2_2A_1 AXD_2A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_1 TDr_2A_1 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_1 ENTD_2A_1 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2A_2 C2_2A_2 EfD_2A_2 ED_2A_2 run2_2A_2 D2_2A_2 W2_2A_2 NX2_2A_2 EQ2_2A_2 RUN2_2A_2 L2_2A_2 AXD_2A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_2 TDr_2A_2 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_2 ENTD_2A_2 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2A_3 C2_2A_3 EfD_2A_3 ED_2A_3 run2_2A_3 D2_2A_3 W2_2A_3 NX2_2A_3 EQ2_2A_3 RUN2_2A_3 L2_2A_3 AXD_2A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_3 TDr_2A_3 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_3 ENTD_2A_3 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2A_4 C2_2A_4 EfD_2A_4 ED_2A_4 run2_2A_4 D2_2A_4 W2_2A_4 NX2_2A_4 EQ2_2A_4 RUN2_2A_4 L2_2A_4 AXD_2A_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_4 TDr_2A_4 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_4 ENTD_2A_4 RUN3_2A L3_2A NX3_2A
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
S9S42VCST;R1A2ScSdScS43S3bR2A2S44R2S3cA2A2A1SdScS43Z17db48R2A2S44R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_hi_ia0_2A : ltac2:(tb__ "0|7|
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
  apply (fi_prefix 2 Wai_2A Dai_2A Wbi_2A Wci_2A Certi_2A ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts true (Wcan 2) UStopLe q_2A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe q_2A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 2 UStopLe q_2A Wbm_2A Wcm_2A Wdm_2A Fb_2A XIm_2A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_2A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_2A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2A_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_2A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_2A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_2A : ltac2:(tb__ "0|7|
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
  apply (efi_prefix 2 Wai_2A Dai_2A Wbi_2A Wci_2A ECerti_2A A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts true (Wcan 2) UStopLe q_2A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe q_2A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 2 UStopLe q_2A Wbm_2A Wcm_2A Wdm_2A Fb_2A XIm_2A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_2A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_2A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2A_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2A_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_2A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_2A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M2A.
End F0A_m2A.

(* [comment removed for export] *)
Module SegQCF_glue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "pair"; "nat"; "cons"; "bool"; "prod"; "nil"; "list"; "app"; "true"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "sprop"; "SLit"; "sobj"; "SAlu"; "SPUle"; "SPAlign"; "SVar"; "ss_objs"; "valuation"; "eval"; "rm"; "holds"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "le"; "pow"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "clsB"; "DQCs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_cache"; "qbatch"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "AA"; "aa_cache_inited"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "class_state"; "mkQB"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue"; "N_F"; "T_entF"; "DQCsb"; "ZD_F"; "BSF"; "dstF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states"; "pcbF"; "FFF"; "S0F"; "OBJF"; "VSF"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vNF"; "vMFA"; "vAU"; "vMU"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "region_info"; "Size"; "PG"; "free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue.CarveF"; "zbF"; "zhiF"; "ZUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "zloS"; "ZD_fixS"; "ZD_rtiS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "QP"; "@Stdlib.Lists.List"; "In"; "Forall2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "F_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "F_grow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM"; "MC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "DQI0"; "N_rti"; "carve_okq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "dobj"; "dspec"; "forallb2"; "keepN"; "same_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue.EntryF"; "ENVF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "mkST"; "s_C"; "s_Cd"; "s_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "entsM"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DQCsb : axst := bump DQCs NXF.
Lemma DQCsb_ent : ltac2:(tb__ "0|0|
ScS5S81S2aS42S71A3SaA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dstF : sv := ltac2:(tb__ "0|0|
S16S4eS16S4eS66S16S4eS16S4fS29S14Z20A1A3S14Ze0000000A1A3A3S16S4fS51S14Z2A1A3A3").
Definition N_F (g : bool) : list carve_spec := ltac2:(tb__ "0|16|
S9S2bS73S9S6S6S6S11S0A2M0S0A2M1S8S6S6S0S3A2M2S11A2M3A1M4A2M5S4G5S2G1G4S2G0S0S2S11S0S14Z0M6A1M7Z17db60M8A4Z17db68A4S4G3S2G2S11S2S0S3G8U8M9A4S14S58A1A4S7G3A1MaA3A4S4G5S2G1G4S2G0S0S2S11S0G7Z17fcecMbA4Z17fcedA4S4G3S2G2S11S2S0S3GbU1McA4G7A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0G7Z17fc78MdA4Z17fc80A4S4G3S2G2S11S2S0S3GdG9A4G7A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0S6cZad0A4Zc60A4S4G3S2G2S11S2S0S3Zae0G9A4S19Pd1A1A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0S46Z14MeA4Z18MfA4S4G3S2G2S11S2S0S3GeU4M10A4S19Pe7A1A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0S46Z4M11A4Z8M12A4S4G3S2G2S11S2S0S3G11G10A4S14Z2A1M13A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0S46G6A4G11A4S4G3S2G2S11S2S0S3G6G10A4G13A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0S46G12A4Z10M14A4S4G3S2G2S11S2S0S3G12G9A4S19Pc9A1A4GaA3A4S4G5S2G1G4S2G0S0S2S11S0S55G6A4Z80A4S4G3S2G2S11S2S0S3G6G9A4G7A4S4G3S2G2S11S2S0S3G14G9A4S51A4S4G3S2G2S11S2S0S3GfG9A4S52A4S4G3S2G2S11S2S0S3Z20G9A4S53A4S4G3S2G2S11S2S0S3Z28G9A4G7A4S4G3S2G2S11S2S0S3Z30G9A4S54A4S4G3S2G2S11S2S0S3Z38G9A4G7A4S4G3S2G2S11S2S0S3Z44GcA4G7A4GaA3A3A3A3A3A3A3A3A4S7G5A1M15A3A3A3A3A3A3A3A3A3S5S8G5A1Lg;Vg;G15S4G5S2G1G4S2G0S0S2S11S0S45G6A4G11A4GaA4G15A3X5x2A3A3").
Lemma N_F_objs : ltac2:(tb__ "0|0|
S5ScS8S15A1S4cS2bS15S2cS40R1A1A4S49R1A1A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition BSF : list positive := ltac2:(tb__ "0|0|
S4S1Pc9S4S1Pd1S4S1PddS4S1PdeS4S1PdfS4S1Pe0S4S1Pe1S4S1Pe7S7S1A1A3A3A3A3A3A3A3A3").
Definition ZD_F (g : bool) : list zdesc := ltac2:(tb__ "0|7|
S9S63S5fS9S6S6S3S0A2M0S0A2M1S4G1S2G0S0S2S3S0U0M2Z17db60A4Z17db68A4S4G1S2G0S0S2S3S0G2Z17fcecA4Z17fcedA4S4G1S2G0S0S2S3S0G2Z17fc78A4Z17fc80A4S4G1S2G0S0S2S3S0U1M3Zad0A4Zc60A4S4G1S2G0S0S2S3S0G3Z864A4Z868A4S4G1S2G0S0S2S3S0G3Z854M4A4Z858M5A4S4G1S2G0S0S2S3S0G3Z850A4G4A4S4G1S2G0S0S2S3S0G3G5A4Z860A4S4G1S2G0S0S2S3S0UbZc00A4Zc80A4S7G1A1M6A3A3A3A3A3A3A3A3A3S5S8G1A1Lg;Vg;G6S4G1S2G0S0S2S3S0UcZ0A4Z20000000A4G6A3X5x2A3A3").
Definition T_entF (g : bool) : strans := ltac2:(tb__ "0|0|
S7dS42U1S40Vg;A1S44S47Vg;A1S48Vg;A1S7aS4aA1S5eS43Vg;A1A9").
Lemma T_entF_ok : ltac2:(tb__ "0|0|
S5ScS5S80S41R1A1A1SaA3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma DQCsb_objs : ltac2:(tb__ "0|a|
ScS8S15A1S1aS50S7eS41SaA1A1M0A1A1S9S15S78G0U1A2S4cS76S15S75S4S6S6S6S6S11S0A2M1S0A2M2S8S6S6S0S3A2M3S11A2M4A1M5A2M6S0A2M7S2G6S0S2G2G5S2G1S0S2S11S0S14Z0M8A1Zeaa78M9A4Zeaa80A4S4G4S2G3S11S2S0S3G9U8A4S66A4S7G4A1A3A4G8A4S7G7A1A3A4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQCsb_ref : ltac2:(tb__ "0|0|
ScS5S77S15S15S79S1aS50S7fS41SaA1A1A1A1S1aS50S72A1A1A5SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FFF_eq : ltac2:(tb__ "0|2|
S5ScS8S13A1S47R1A1S9S13S4S13S17S14Z1M0A1S29A2S4S13S17S29S14Z1eA1A2S4S13S18Pe1Z7A2S4S13S18P9bZ10A2S4S13S17S51S14Z8000000A1A2S4S13S18PdeZ12A2S4S13S17S52S14Z20000000A1A2S4S13S5S13Lg;R1S6eG0A1S6dG0A1X5x2S7S13A1M1A3A3A3A3A3A3A3A3S4S13S18P97ZcA2S4S13S17S14Z10000000000A1S19PaA1A2G1A3A3A3A3Fg;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section CarveF.
Variables (Kc : KcA) (A : AA) (r : valuation) (tp : list word) (tr : list event) (md : Model).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HK : ltac2:(tb__ "0|0|
S65VKc;VA;Vr;Vtp;Vtr;Vmd;A6").
Hypothesis HCI : aa_cache_inited A = true.
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := cls_of A 24.
Let m : bview := ltac2:(tb__ "0|0|
S28S2dS1dVr;A1A2").
Hypothesis HFULL : ltac2:(tb__ "0|0|
ScS0S22SbS0S2fVcs;A1A2A1Z2A3").
Variable st : Z.
Hypothesis Hst : 0 <= st < 2 ^ 64.
Hypothesis Cst : ltac2:(tb__ "0|0|
S26Vm;S27S21VT;Zae0A2U8Vst;A3A2").
Hypothesis EC : ltac2:(tb__ "0|1|
ScS20Q40M0A1S1cVr;S29A2S1fG0Z18A2A3").
Hypothesis EV : ltac2:(tb__ "0|3|
SdScS20Q40M0A1M1S12Vr;Pc9A2S1fG0S57Z18M2A1A2A3SdScG1S12Vr;Pd1A2S1fG0Vst;A2A3SdScG1S12Vr;PddA2S1fG0S22SbS0S32Vcs;A1A2A1A2A3SdScG1S12Vr;PdeA2S1fG0S33Vcs;A1A2A3SdScG1S12Vr;PdfA2S1fG0S31Vcs;A1A2A3SdScG1S12Vr;Pe0A2S1fG0S34Vcs;A1A2A3SdScG1S12Vr;Pe1A2S1fG0S56VSB;G2A2A2A3ScG1S12Vr;Pe7A2S1fG0S4dS0U1S2fVcs;A1Z0A4A2A3A2A2A2A2A2A2A2").

Lemma ri_zero_cells : ltac2:(tb__ "0|3|
SdS26Vm;S27S21S56VSB;Z18A2M0Z28A2U8M1Z0M2A3A2SdS26Vm;S27S21G0Z38A2G1G2A3A2S26Vm;S27S21G0Z44A2U1G2A3A2A2A2").
Proof.
  destruct HK as (HA & _). pose proof HA as (HG & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & R3 & _).
  destruct R3 as (_ & _ & _ & P4). pose proof (P4 24 ltac:(lia)) as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & C5 & _ & C7 & C8 & _). unfold RI_allocated_meta, RI_mapped_meta, RI_exhausted in *. fold G SB in C5, C7, C8.
  pose proof kSpaceSize_val as KSV.
  assert (ZRI : forall z, region_info SB 24 <= z < region_info SB 24 + kRegionInfoStride -> maskv (fs_footb G) m z = m z).
  { intros z Hz. apply (MS A m HG). fold G SB. unfold region_info, kRegionInfoStride in Hz. rewrite KSV in *. lia. }
  split; [|split]; (eapply (cell_tr A m); [|eassumption]); intros k Hk; apply ZRI; cbn [c_addr c_w] in *; unfold kRegionInfoStride; lia.
Qed.

Lemma carve_F : ltac2:(tb__ "0|0|
S5ScS5S2eZ18Vcs;A2R1A3S4bS2bS74Vr;A1S40R2A1A3F_;Fg;").
Proof using All.
  intros g HGR. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG HRTC _ HST _ HCLS _ _ _ _ _ _]. fold G in HG, HRIG, HRTC, HST, HCLS.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T SB in E151, E155, E156, HST.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. fold cs in CV.
  pose proof (cv_count _ _ _ _ _ CV) as C_cnt. pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz.
  pose proof (cv_ri_mutex _ _ _ _ _ CV) as R0. pose proof (cv_ri_nfreed _ _ _ _ _ CV) as R16. pose proof (cv_ri_mfa _ _ _ _ _ CV) as R24. pose proof (cv_ri_au _ _ _ _ _ CV) as R32.
  pose proof (cv_ri_mu _ _ _ _ _ CV) as R48. pose proof (cv_ri_present _ _ _ _ _ CV) as PRI. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3). pose proof (cv_fa_present _ _ _ _ _ CV) as PFA.
  destruct ri_zero_cells as (R40 & R56 & R68).
  assert (Hx : exists x, nth_error (cs_cache cs) 1 = Some x /\ x = nth 1 (cs_cache cs) 0).
  { destruct (cs_cache cs) as [|x0 [|x1 l1]] eqn:EL; cbn [length] in HFULL; try lia. exists x1. split; reflexivity. }
  destruct Hx as (x1 & Hx1 & Ex1). pose proof (cv_chunks _ _ _ _ _ CV 1%nat x1 Hx1) as C_chk.
  unfold pc_entry, RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_mapped_user in *. fold G T SB in C_cnt, C_max, C_sz, C_chk, R0, R16, R24, R32, R48, PRI, PFA.
  rewrite HFULL in C_cnt. change (max_count 24) with 2 in C_max. change (Size 24) with 8192 in *.
  destruct EV as (E201 & E209 & E221 & E222 & E223 & E224 & E225 & E231).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & S16 & TG). fold G T SB in T0, T1, S1, S2, S16.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). fold G T in TI. unfold IMG_LO, IMG_HI in TI, CI. unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. unfold kFreeArraySize, kFreeArrayMapSize in *.
  assert (HR : cells_ok (view segsA (rm r)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  assert (TBLK : forall lo hi, T <= lo -> hi <= T + 4096 -> (hi <= 0x10000 \/ 0x643000 <= lo)) by (intros lo hi B1 B2; clear -TI B1 B2; lia).
  assert (EvT : bv_unsigned (eval r vT) = T) by (unfold vT; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity).
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : bv_unsigned (eval r pcbF) = T + 2128).
  { unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval r (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (RIv : region_info SB 24 = SB + 2 ^ 37 + 3072) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (ERI : bv_unsigned (eval r vRI) = region_info SB 24) by (unfold vRI; cbn [eval]; rewrite E225, u64_lit by lia; reflexivity).
  assert (FAv : free_array SB 24 = SB + 24 * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  unfold N_F. apply Forall_app. split; [|apply Forall_app; split].
  -
    clear C_cnt C_max C_sz C_chk R0 R16 R24 R32 R48 PRI PFA R40 R56 R68 Cst EcbC Epcb ERI. unfold SB, T, G in *.
    unfold N_rti, vSB, vRIS, vCTX, vT. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta; cbn [eval]; rewrite ?E152, ?u64_lit by lia.
    all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
    all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    all: split.
    all: try match goal with
         | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
         | |- forall off, _ -> wok_of _ _ _ = true /\ _ => intros off Hoff; wr_any2 HR ltac:(clear -CI; lia)
         end.
    all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E155, ?E156; civ_any2 HR.
  - repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta.
    all: rewrite ?EvT, ?Epcb, ?ERI; cbn [eval]; rewrite ?u64_lit by lia.
    all: unfold PG in *.
    all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
    all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    all: split.
    all: try match goal with
         | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
         end.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
    + intros off Hoff. apply (wr_present (rm r) (T + 2768) (T + 3168) (T + off) HST); [lia | lia | lia | apply TBLK; lia].
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      intros j Hj. apply (civ_cell r (rm r) T 2784 8 st (SVar 209)); [exact Cst | cbn [eval]; exact E209 | lia | lia | exact Hj].
    + intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_chk); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      intros j Hj. apply (civ_cell r (rm r) (T + 2128) 20 4 x1 (SVar 231)); [replace (T + 2128 + 20) with (T + 208 + 80 * 24 + 16 + 4 * Z.of_nat 1) by lia; exact C_chk | cbn [eval]; rewrite E231, Ex1; reflexivity | lia | lia | exact Hj].
    + intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_max); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      intros j Hj. apply (civ_cell r (rm r) (T + 2128) 4 4 2 (SLit 2)); [replace (T + 2128 + 4) with (T + 208 + 80 * 24 + 4) by lia; exact C_max | reflexivity | lia | lia | exact Hj].
    + intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_cnt); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      intros j Hj. apply (civ_cell r (rm r) (T + 2128) 0 4 2 (SLit 2)); [replace (T + 2128 + 0) with (T + 208 + 80 * 24) by lia; exact C_cnt | reflexivity | lia | lia | exact Hj].
    + intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_sz); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      intros j Hj. apply (civ_cell r (rm r) (T + 2128) 8 8 8192 (SVar 201)); [replace (T + 2128 + 8) with (T + 208 + 80 * 24 + 8) by lia; exact C_sz | cbn [eval]; exact E201 | lia | lia | exact Hj].
    + intros off Hoff. apply (wr_present (rm r) (region_info SB 24) (region_info SB 24 + 128) (region_info SB 24 + off) PRI); [lia | lia | lia | right; lia].
    + unfold cells_in_view, vNF, vMFA, vAU, vMU. repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
      * apply (civ_cell r (rm r) (region_info SB 24) 0 8 0 (SLit 0)); [exact R0 | reflexivity | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 16 8 (Z.of_nat (length (cs_free_array cs))) (SVar 221)); [exact R16 | cbn [eval]; exact E221 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 24 8 (cs_mapped_free_array cs) (SVar 222)); [exact R24 | cbn [eval]; exact E222 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 32 8 (cs_allocated_user cs) (SVar 223)); [exact R32 | cbn [eval]; exact E223 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 40 8 0 (SLit 0)); [exact R40 | reflexivity | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 48 8 (cs_mapped_user cs) (SVar 224)); [exact R48 | cbn [eval]; exact E224 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 56 8 0 (SLit 0)); [exact R56 | reflexivity | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB 24) 68 1 0 (SLit 0)); [exact R68 | reflexivity | lia | lia | exact Hj].
  - destruct g; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
    unfold drain_grows in HGR. apply Z.ltb_ge in HGR. change (kchunks 24) with 1 in HGR.
    assert (Edst : bv_unsigned (eval r dstF) = free_array SB 24 + 4 * Z.of_nat (length (cs_free_array cs))).
    { unfold dstF. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite EC, E155, E221, !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
      unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (24 * 2 ^ 32 + 3758096384))) by lia.
      rewrite (Z.mod_small (Z.of_nat (length (cs_free_array cs)) * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    unfold carve_okq. lazy beta iota zeta. rewrite Edst. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; apply Forall_nil|]. split; [|unfold cells_in_view; apply Forall_nil].
    intros off Hoff. apply (wr_present (rm r) _ _ (free_array SB 24 + 4 * Z.of_nat (length (cs_free_array cs)) + off) PFA); [lia | lia | lia | right; lia].
Qed.

Definition zbF (z : nat) : Z := ltac2:(tb__ "0|1|
S3S0Lz;Vz;Z0S3S3S0Ln;R1VT;S3S3S0Ln0;R1S3aVG;A1S3S3S0Ln1;R1S3fVG;A1S3S3S0Ln2;R1S59VSB;Z18A2M0S3S3S0Ln3;R1G0S3S3S0Ln4;R1G0S3S3S0Ln5;R1G0S3S3S0Ln6;R1G0S3S3S0Ln7;R1G0S3S3S0Ln8;R1G0S3S3S0Ln9;R1S21VSB;S24Z2Z25A2A2S3G0Ln10;X3x2Ln9;X3x2Ln8;X3x2Ln7;X3x2Ln6;X3x2Ln5;X3x2Ln4;X3x2Ln3;X3x2Ln2;X3x2Ln1;X3x2Ln0;X3x2Ln;X3x2").
Definition zhiF (z : nat) : Z := match z with 0%nat => 0x643000 | 1%nat => 4096 | 2%nat => 4096 | 3%nat => 2 ^ 64 | 11%nat => 4096 | _ => 536870912 end.
Definition ZUF : list nat := ltac2:(tb__ "0|0|
S4S3U0S4S3U1S4S3U2S4S3U3S4S3UbS4S3UcS7S3A1A3A3A3A3A3A3").
Lemma zsepF : ltac2:(tb__ "0|3|
S3S3S69S3R2S5cA3M0G0SfScS3R4R3A3A1S10S23S21S5aR5A1M1S5bR5A1A2S21S5aR4A1M2S5dR4A1A2A2S23S21G2S5bR4A1A2S21G1S5dR5A1A2A2A2F_;F_;F_;Fz';Fz;").
Proof using HKc HK.
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ HSEP3 _ _]. fold G in HG, HSEP3.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & _ & TG). fold G T SB in T0, T1, S1, S2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). fold G T in TI. pose proof (geom_seps _ HG) as (_ & _ & _ & _ & Q5 & _). fold G T in Q5.
  destruct HSEP3 as (P1 & P2 & _). fold G T SB in P1, P2.
  unfold IMG_LO, IMG_HI, HIGH_SHADOW_END in *. rewrite kSpaceSize_val in *.
  assert (FAv : free_array SB 24 = SB + 24 * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  intros z z' Hz Hz' NE. unfold ZUF in *. cbn [In] in Hz, Hz'.
  destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; destruct Hz' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try (exfalso; apply NE; reflexivity); unfold zbF, zhiF, zloS; rewrite ?FAv; lia.
Qed.

Lemma inz_F : ltac2:(tb__ "0|0|
S5ScS5S2eZ18Vcs;A2R1A3S6aS15S63S64Vr;S5aS5dS5bS5cA5S4cS2bS15S2cS40R2A1A4S43R2A1A5F_;Fg;").
Proof using All.
  intros g HGR. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG _ _ _ _ HCLS _ _ _ _ _ _]. fold G in HG, HRIG, HCLS.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T SB in E151, E155, E156.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. fold cs in CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  destruct EV as (E201 & E209 & E221 & E222 & E223 & E224 & E225 & E231).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & S16 & TG). fold G T SB in T0, T1, S1, S2, S16.
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2. pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. unfold kFreeArraySize, kFreeArrayMapSize in *.
  assert (EvT : bv_unsigned (eval r vT) = T) by (unfold vT; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity).
  assert (EvC : bv_unsigned (eval r vCTX) = ag_ctx G) by (unfold vCTX; cbn [eval]; rewrite E152, u64_lit by lia; reflexivity).
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : bv_unsigned (eval r pcbF) = T + 2128).
  { unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval r (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (RIv : region_info SB 24 = SB + 2 ^ 37 + 3072) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (ERI : bv_unsigned (eval r vRI) = SB + 2 ^ 37 + 3072) by (unfold vRI; cbn [eval]; rewrite E225, RIv, u64_lit by lia; reflexivity).
  assert (FAv : free_array SB 24 = SB + 24 * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (Edst : bv_unsigned (eval r dstF) = free_array SB 24 + 4 * Z.of_nat (length (cs_free_array cs))).
  { unfold dstF. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite EC, E155, E221, !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
    unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (24 * 2 ^ 32 + 3758096384))) by lia.
    rewrite (Z.mod_small (Z.of_nat (length (cs_free_array cs)) * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
  assert (DST : g = false -> 4 * Z.of_nat (length (cs_free_array cs)) + 4 <= 536870912).
  { intros ->. unfold drain_grows in HGR. apply Z.ltb_ge in HGR. change (kchunks 24) with 1 in HGR. lia. }
  unfold N_F, ZD_F, N_rti, ZD_rtiS. destruct g; cbn [map app]; repeat apply Forall2_cons; try apply Forall2_nil;
    unfold in_zone, carve_obj, carved; rewrite obj_range_mk by lia; rewrite ?EvT, ?EvC, ?Epcb, ?ERI, ?Edst; cbn [eval fst snd]; rewrite ?u64_lit by lia;
    (split; [unfold ZUF; cbn; tauto|]); unfold zloS, zhiF, zbF, PG; (split; [lia|]); (split; [lia|]); right; first [lia | (specialize (DST eq_refl); lia)].
Qed.

Lemma facts_F : ltac2:(tb__ "0|1|
S5ScS5S2eZ18Vcs;A2R1A3S70VA;Vr;A2S4bS13S1eVr;A1M0S6fS7bA1A3S4bS13G0S47R4A1A3F_;F_;F_;Fg;").
Proof using All.
  intros g HGR HTOP HFp. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG _ _ _ _ HCLS _ _ _ _ _ _]. fold G in HG, HRIG, HCLS.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T SB in E151, E155, E156.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. fold cs in CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  destruct EV as (E201 & E209 & E221 & E222 & E223 & E224 & E225 & E231).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & TP & _ & _ & _ & _ & S1 & S2 & S16 & TG). fold G T SB in T0, T1, TP, S1, S2, S16.
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2. pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. unfold kFreeArraySize, kFreeArrayMapSize, PG in *.
  destruct (stk_facts A r HTOP HFp) as (HD & HT2 & HSP). cbv zeta in HD, HT2, HSP.
  assert (RIv : region_info SB 24 = SB + 2 ^ 37 + 3072) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (E4 : eval r (SAlu ALU_SLL (SAlu ALU_ADD vNF (SLit 1)) (SLit 2)) = Z_to_bv 64 (4 * (Z.of_nat (length (cs_free_array cs)) + 1))).
  { apply bv_eq. rewrite U_sll_lit. change (2 mod 64) with 2. change (SAlu ALU_ADD vNF (SLit 1)) with (add vNF (SLit 1)).
    rewrite (ev_add_lit r vNF (Z.of_nat (length (cs_free_array cs))) 1 ltac:(unfold vNF; cbn [eval]; exact E221) ltac:(lia) ltac:(lia) ltac:(lia)). rewrite !u64_lit by lia. unfold M64v. rewrite Z.mod_small by lia. lia. }
  rewrite FFF_eq. apply Forall_app. split.
  - unfold drain_grows in HGR. change (kchunks 24) with 1 in HGR.
    repeat apply Forall_cons; try apply Forall_nil.
    + cbn [holds]. rewrite EC. change (eval r (SLit 1)) with (Z_to_bv 64 1). rewrite !u64_lit by lia. lia.
    + cbn [holds]. rewrite EC. change (eval r (SLit 30)) with (Z_to_bv 64 30). rewrite !u64_lit by lia. lia.
    + cbn [holds]. split; [lia|]. rewrite E225, RIv, u64_lit by lia. change (2 ^ 7) with 128. lia.
    + cbn [holds]. split; [lia|]. rewrite E155, u64_lit by lia. exact S16.
    + cbn [holds]. unfold vNF. cbn [eval]. rewrite E221, !u64_lit by lia. lia.
    + cbn [holds]. split; [lia|]. rewrite E222, u64_lit by lia. change (2 ^ 18) with 262144. exact FB1.
    + cbn [holds]. unfold vMFA. cbn [eval]. rewrite E222, !u64_lit by lia. lia.
    + destruct g; unfold F_grow, F_fast; cbn [holds branch_taken]; unfold bv_ltu; rewrite E4; unfold vMFA; cbn [eval]; rewrite E222, !u64_lit by lia.
      * exact HGR.
      * intros X0. rewrite X0 in HGR. discriminate HGR.
  - repeat apply Forall_cons; try apply Forall_nil.
    + cbn [holds]. split; [lia|]. rewrite E151, u64_lit by lia. change (2 ^ 12) with 4096. exact TP.
    + cbn [holds eval]. rewrite u64_lit by lia. unfold G in TG. clear - HT2 HD TG. lia.
Qed.
End CarveF.

Section EntryF.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Definition ENVF (A : AA) (r : valuation) : Prop := ltac2:(tb__ "0|5|
S60VA;Z18M0A2S3dSdScS20Q40M1A1M2S1cVr;S29A2S1fG1G0A2A3SeS0S0SdSdS23Z0M3R1A2S25R1S24Z2Z40A2A2A2SdS26S28S2dS1dVr;A1A2S27S21S3cS37VA;A1M4A1Zae0A2U8R1A3A2SdScG2S12Vr;Pc9A2S1fG1S57G0A1A2A3SdScG2S12Vr;Pd1A2S1fG1R1A2A3SdScG2S12Vr;PddA2S1fG1S22SbS0S32R2A1A2A1A2A3SdScG2S12Vr;PdeA2S1fG1S33R2A1A2A3SdScG2S12Vr;PdfA2S1fG1S31R2A1A2A3SdScG2S12Vr;Pe0A2S1fG1S34R2A1A2A3SdScG2S12Vr;Pe1A2S1fG1S56S3bG4A1G0A2A2A3ScG2S12Vr;Pe7A2S1fG1S4dS0U1S2fR2A1G3A4A2A3A2A2A2A2A2A2A2A2A2Lst;A2A2Tcs;").

Lemma qcf_entry : ltac2:(tb__ "0|7|
S5S35S0S0S0S3S8S30A1M0G0S1bS8S20Q40M1A1M2A1S6bScG0S39RaA1S7S30A1A3ScS5S36RbA1SaA3S0S61RdR1A2S61VA0;R2A2F_;Fz;S68VA0;RdA2ScG0S38ReA1S4S30S3eRdS7S6S0S0A2A1M3RcA3S9S30R9R8A3A3A3ScS0S22SbS0S2fS60RfZ18M4A2A1A2A1Z2A3ScS5S2eG4S60R10G4A2A2R11A3S62S2dS67S65VKc;A1M5VA0;Vrho0;R11R10ReRdG3RcRbAaS2aRaR9R8A6ScG2S12RbPa6M6A2S1fG1R11A2A3SeS1bS1bSdS62S2dS67G5VA0;Vrho0;R14R13R11R10G3RfReAaS48R15A1R1RcRbA6SdS7cR14R1A2S1S69S1R1S4S1G6S4S1Pb8S4S1Pb9S4S1PbaS4S1PbbS4S1Pd0S7S1A1A3A3A3A3A3A3A3ScG2S12R3R2A2S12RfR2A2A3F_;Fv;A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp [tr [ms md]] HTH HCI HQW (ESB & _) HGL HFULL HGR H E166.
  assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL. set (J := JRI (K0 Kc) A0 rho0 A a n0 nd [] tmp' rest).
  pose proof (JRI_stable (K0 Kc) HL A0 rho0 A a n0 nd [] tmp' rest) as HSTB.

  destruct (entM_SPA J DQCs DQCsb MC rho tp _ DQCsb_ent HSTB H) as (H1 & AG1 & V1 & RM1). set (rho1 := rho_sub rho (infer_sub NPRE (ax_S DQCs) (ax_S DQCsb))) in *.
  assert (VV1 : forall v, In v [166; 184; 185; 186; 187; 208]%positive -> rw rho1 v = rw rho v).
  { intros v Hv. rewrite (V1 v (SVar v)); [reflexivity|]. unfold MC, idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  destruct (proj2 H1) as (HK1 & HCB1 & HRM1 & HFRM1). cbn [w_tr w_cfg cfg_model fst snd] in HK1, HCB1, HRM1, HFRM1.
  destruct (kq_facts segsA (K0 Kc) HL A rho1 tp _ _ HK1) as [HG HRIG HRTC _ HST _ _ HQPU _ _ _ HKTOP _].
  destruct HRIG as (E151 & E152 & E155 & E156).
  pose proof (benv_of_K (K0 Kc) HL A HCI rho1 tp tr md HK1) as BE. destruct BE as [_ _ HQP HAU _ _ _].
  destruct (batch_slot A HQP HAU HG (mkQB a [] s) ltac:(rewrite (qall_A1 A HTH), HGL; left; reflexivity)) as (y & Ey & Y0 & _ & Y1 & _). cbn [qb_addr] in Ey. rewrite kUserSpaceSize_val in Y1.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  assert (PST : present (view segsA (rm rho1)) (ag_thread (aa_geom A) + 2784) (ag_thread (aa_geom A) + 2784 + 8)) by (intros z Hz; apply HST; lia).
  destruct (present_cell8q _ _ PST) as (st & Hst & C_st).
  set (cs := cls_of A 24) in *.
  set (vals := [Z_to_bv 64 (Size 24); Z_to_bv 64 st; Z_to_bv 64 (Z.of_nat (length (cs_free_array cs))); Z_to_bv 64 (cs_mapped_free_array cs);
                Z_to_bv 64 (cs_allocated_user cs); Z_to_bv 64 (cs_mapped_user cs); Z_to_bv 64 (region_info (ag_spacebeg (aa_geom A)) 24); Z_to_bv 64 (nth 1 (cs_cache cs) 0)]).
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (s_C (T_entF g)) rho1 tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).

  assert (ROC : Forall (ro_cond A0 rho1) [(SLit 0, 0xeaa78, 0xeaa80, [(0xeaa78, 8%nat, vSB)], 0)]).
  { apply Forall_cons; [|apply Forall_nil]. apply (ro_cond_intro A0 (mkSC 0 0 0)); try reflexivity; try lia.
    - unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. lia.
    - intros z Hz. split; [right; left; unfold qrtc_zone; lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia].
    - repeat apply Forall_cons; try apply Forall_nil. exists (ag_spacebeg (aa_geom A)). split; [unfold vSB; cbn [eval]; exact E155|].
      unfold rtc_inv, rtc_cells in HRTC. exact (cells_ok_nth _ _ 3 _ HRTC eq_refl). }
  assert (HOBJ : ss_objs (ax_S (s_C (T_entF g))) = keepN (s_C (T_entF g)) (s_k (T_entF g)) ++ map dobj [(SLit 0, 0xeaa78, 0xeaa80, [(0xeaa78, 8%nat, vSB)], 0)]) by (destruct g; exact DQCsb_objs).
  assert (NDB : List.NoDup (map fst (combine BSF vals))) by (unfold BSF, vals; cbn; repeat constructor; cbn; intuition discriminate).
  set (rho3 := rho_absorb rho1 (map dobj [(SLit 0, 0xeaa78, 0xeaa80, [(0xeaa78, 8%nat, vSB)], 0)]) (vms md tp ms)) in *.
  set (rho4 := rho_sets rho3 (combine (s_bs (T_entF g)) vals)).
  assert (OT : forall v, ~ In v BSF -> rw rho4 v = rw rho1 v).
  { intros v Hv. unfold rho4. rewrite rho_sets_other; [reflexivity|]. intros X0. apply Hv. unfold T_entF in X0. cbn [s_bs] in X0. unfold BSF, vals in *. cbn in X0 |- *. exact X0. }
  assert (GET : forall v x, In (v, x) (combine BSF vals) -> rw rho4 v = x) by (intros v x Hin; unfold rho4, T_entF; cbn [s_bs]; exact (rho_sets_get _ rho3 v x NDB Hin)).

  destruct (s_step (K0 Kc) HL A0 rho0 (zbF A) zloS zhiF ZUF (zsepF Kc A rho1 tp tr md HKc HK1) (T_entF g) J [(SLit 0, 0xeaa78, 0xeaa80, [(0xeaa78, 8%nat, vSB)], 0)] vals A rho1 tp tr ms md
              (T_entF_ok g) HSTB HQW HOBJ eq_refl HT HK1 HFRM1 ROC) as (rho5 & H5 & V5 & RM5 & AG5 & EV5).
  { intros HK3 HF3 EV3. fold rho3 in HK3, HF3, EV3. fold rho3. fold rho4.
    assert (HK4 : K0 Kc A rho4 tp tr md).
    { apply (kq_stable segsA (K0 Kc) HL A rho3 rho4 tp tr md md); [|apply mat_equiv_refl | exact HK3]. split; [|split].
      - intros v Hv. symmetry. unfold rho4. rewrite rho_sets_other; [reflexivity|]. intros X0. unfold T_entF in X0. cbn [s_bs] in X0. unfold BSF, vals, QNPRE in *. cbn in X0. lia.
      - intros l0. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). reflexivity.
      - intros x. unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). reflexivity. }
    assert (ERM4 : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets).
    assert (EC4 : eval rho4 clsB = Z_to_bv 64 24).
    { apply (clsB_val rho4 (ag_spacebeg (aa_geom A)) a y); try lia; rewrite OT by (unfold BSF; cbn; intuition discriminate); [rewrite (VV1 166%positive ltac:(cbn; tauto)); exact E166 | exact E155]. }
    assert (EV4 : rw rho4 201%positive = Z_to_bv 64 (Size 24) /\ rw rho4 209%positive = Z_to_bv 64 st
      /\ rw rho4 221%positive = Z_to_bv 64 (Z.of_nat (length (cs_free_array cs))) /\ rw rho4 222%positive = Z_to_bv 64 (cs_mapped_free_array cs)
      /\ rw rho4 223%positive = Z_to_bv 64 (cs_allocated_user cs) /\ rw rho4 224%positive = Z_to_bv 64 (cs_mapped_user cs)
      /\ rw rho4 225%positive = Z_to_bv 64 (region_info (ag_spacebeg (aa_geom A)) 24) /\ rw rho4 231%positive = Z_to_bv 64 (nth 1 (cs_cache cs) 0)).
    { repeat split; apply GET; unfold BSF, vals; cbn; tauto. }
    assert (C_st4 : cell_ok (view segsA (rm rho4)) (mkACell (ag_thread (aa_geom A) + 2784) 8 st)) by (rewrite ERM4, EV3; exact C_st).
    assert (HTOP4 : top_high A rho4) by (unfold top_high in *; rewrite !OT by (unfold BSF, V_DEPTH; cbn; intuition discriminate); exact HKTOP).
    pose proof (D_pre_facts DQCs _ eq_refl rho1 (SPA_facts_hold segsA _ rho1 DQCsb tp _ H1)) as HFpre1.
    assert (HFpre4 : Forall (holds rho4) (pre_facts DEPTH_R)).
    { apply Forall_forall. intros f0 Hf0. apply (holds_agree_vals NPRE rho1 rho4 f0); [| exact (proj1 (forallb_forall _ _) pre_facts_below f0 Hf0) | exact (proj1 (Forall_forall _ _) HFpre1 f0 Hf0)].
      split; [intros v Hv; symmetry; apply OT; unfold BSF, NPRE in *; cbn; lia | intros l0; unfold rho4; rewrite (proj1 (rho_sets_rl_rm _ rho3)); reflexivity]. }
    split; [split; [exact HK3 | split; [rewrite EV3; exact HCB1 | split; [rewrite EV3; exact HRM1 | exact HF3]]]|].
    split; [exact (carve_F Kc A rho4 tp tr md HKc HK4 HCI HFULL st Hst C_st4 EC4 EV4 g HGR)|].
    split; [exact (inz_F Kc A rho4 tp tr md HKc HK4 HCI HFULL st Hst C_st4 EC4 EV4 g HGR)|].
    split.
    - apply (in_zone_same rho4 _ _ _ _ _ (ss_objs (ax_S DQI0)) ZD_fixS ltac:(destruct g; exact DQCsb_ref)).
      apply (in_zone_ext_list rho4 (zbS (ag_thread (aa_geom A)) (ag_ctx (aa_geom A)) (topG (aa_geom A)) 0) zloS (zhiS 0) ZUS).
      + exact (inz_fixS A (0, 0) 0%nat (mkSC 0 0 0) rho4 HTOP4 HFpre4).
      + unfold ZD_fixS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [unfold ZUF; cbn; tauto | split; [reflexivity | split; reflexivity]]).
    - intros _. exact (facts_F Kc A rho4 tp tr md HKc HK4 HCI HFULL st Hst C_st4 EC4 EV4 g HGR HTOP4 HFpre4). }
  exists rho5. split; [exact H5|].
  assert (VV5 : forall v, In v VSF -> rw rho5 v = rw rho4 v).
  { intros v Hv. rewrite (V5 v (SVar v)); [reflexivity|]. unfold T_entF. cbn [s_M]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  assert (K5 : forall v, In v [166; 184; 185; 186; 187; 208]%positive -> rw rho5 v = rw rho v).
  { intros v Hv. rewrite VV5 by (unfold VSF; cbn in Hv |- *; tauto). rewrite OT by (unfold BSF; cbn in Hv |- *; intuition (subst; discriminate)). exact (VV1 v Hv). }
  split; [|exact K5].
  assert (ERM5 : view segsA (rm rho5) = view segsA (rm rho1)) by (rewrite RM5; exact EV5).
  unfold ENVF. cbv zeta. fold cs. split.
  - apply (clsB_val rho5 (ag_spacebeg (aa_geom A)) a y); try lia; [rewrite (K5 166%positive ltac:(cbn; tauto)); exact E166|].
    rewrite <- (proj1 AG5 155%positive ltac:(unfold NPRE; lia)). rewrite OT by (unfold BSF; cbn; intuition discriminate). exact E155.
  - exists st. split; [exact Hst|]. split; [rewrite ERM5; exact C_st|].
    repeat split; (rewrite VV5 by (unfold VSF; cbn; tauto)); apply GET; unfold BSF, vals; cbn; tauto.
Qed.
End EntryF.
End SegQCF_glue.

(* [comment removed for export] *)
Module F0A_m0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A"; "q_0A"; "Ebg_0A"; "ED_0A_1"; "ED_0A_2"; "Edr_0A"; "TD_0A_1"; "TD_0A_2"; "Xf_0A"; "exits1_0A"; "W_0A"; "st_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A"; "PMID_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.F0A_i0A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l6.F0A_xi0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_d0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lm.F0A_a0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.F0A_i0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_0A : ltac2:(tb__ "0|0|
SbS15S1eS58S1U0A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_0A : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S6dA1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_0A : ltac2:(tb__ "0|0|
SbS15S1eS5aS1U0A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_0A : ltac2:(tb__ "0|0|
SbS15S1eS5bS1U0A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_0A__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_0A : ltac2:(tb__ "0|1|
SbS15S3bSaUbb8S55S46S57U0M0S0A2S14S10S56S1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_0A__runs); [unfold Certi_0A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_0A : ltac2:(tb__ "0|2|
SbS15S3cSaUbb8S55S46S59U0M0S0A2S14S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S16S39A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_0A__runs); [unfold Certi_0A__runs; reflexivity | vmr]. Qed.

Definition PMID_0A : axst := ltac2:(tb__ "0|0|
S62S13S2dS2eS24A4").
Definition Cert1m_0A__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS14S9S5cS16S9A1A3S14S10S3dS16S10A1A3A4").
Lemma Cert1m_0A : ltac2:(tb__ "0|0|
SbS15S3bSaS5dS14S9S5cS16S9A1A3S46S14S10S3dS16S10A1A3S2cA6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_0A] exits1_0A Cert1m_0A__runs); [unfold Cert1m_0A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_0A : ltac2:(tb__ "0|2|
SbS15S3cSaS5dS14S9S5cS16S9A1A3S46S14S39S3aS3dZ1S21Z0M0A1M1A3S16S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_0A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_0A) Cert1m_0A__runs); [unfold Cert1m_0A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_0A : ltac2:(tb__ "0|0|
SbS15S1eS63S1U0A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_0A : ltac2:(tb__ "0|0|
SbS15S1eS64S1U0A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_0A : ltac2:(tb__ "0|0|
SbS15S1eS65S1U0A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_0A : ltac2:(tb__ "0|2|
SbS19S10A1S6cS66S13S1U0M0A1M1S0S24A4S70G0S24A2A2S1bS10S62S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_0A : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S13RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0A C3_0A Ems_0A C4_0A TM0_0A run4_0A RM_0A D3_0A W3_0A EQ3_0A NX3b_0A RUN4_0A L4_0A D4_0A W4_0A EQ4_0A
             HeM_0A HchkM_0A HTM_0A FBM_0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0A.
    apply (f0_s5 0%nat st q_0A false TM_0A Eq_0A EQ_0A TQ0_0A run5_0A RQ_0A NX5_0A RUN5_0A L5_0A AXQ_0A HeQ_0A HchkQ_0A HTQ_0A FBQ_0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0A.
    apply (f0_s6 0%nat st false TQ_0A Edr_0A Xf_0A run6_0A NX6_0A RUN6_0A L6_0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_0A exits1_0A Cert1m_0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0A_1 C2_0A_1 EfD_0A_1 ED_0A_1 run2_0A_1 D2_0A_1 W2_0A_1 NX2_0A_1 EQ2_0A_1 RUN2_0A_1 L2_0A_1 AXD_0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0A_1 TDr_0A_1 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_1 ENTD_0A_1 RUN3_0A L3_0A NX3_0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0A_2 C2_0A_2 EfD_0A_2 ED_0A_2 run2_0A_2 D2_0A_2 W2_0A_2 NX2_0A_2 EQ2_0A_2 RUN2_0A_2 L2_0A_2 AXD_0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0A_2 TDr_0A_2 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_2 ENTD_0A_2 RUN3_0A L3_0A NX3_0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_0A : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S13ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0A C3_0A Ems_0A C4_0A TM0_0A run4_0A RM_0A D3_0A W3_0A EQ3_0A NX3b_0A RUN4_0A L4_0A D4_0A W4_0A EQ4_0A
             HeM_0A HchkM_0A HTM_0A FBM_0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0A.
    apply (ef0_s5 0%nat st q_0A false TM_0A Eq_0A EQ_0A TQ0_0A run5_0A RQ_0A NX5_0A RUN5_0A L5_0A AXQ_0A HeQ_0A HchkQ_0A HTQ_0A FBQ_0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0A.
    apply (ef0_s6 0%nat st false TQ_0A Edr_0A Xf_0A run6_0A NX6_0A RUN6_0A L6_0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_0A exits1_0A (eq_refl : (GW <=? ss_next (ax_S PMID_0A))%positive = true) ECert1m_0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0A_1 C2_0A_1 EfD_0A_1 ED_0A_1 run2_0A_1 D2_0A_1 W2_0A_1 NX2_0A_1 EQ2_0A_1 RUN2_0A_1 L2_0A_1 AXD_0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0A_1 TDr_0A_1 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_1 ENTD_0A_1 RUN3_0A L3_0A NX3_0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0A_2 C2_0A_2 EfD_0A_2 ED_0A_2 run2_0A_2 D2_0A_2 W2_0A_2 NX2_0A_2 EQ2_0A_2 RUN2_0A_2 L2_0A_2 AXD_0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0A_2 TDr_0A_2 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_2 ENTD_0A_2 RUN3_0A L3_0A NX3_0A
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
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ17db48R2A2S40R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_hi_ia0_0A : ltac2:(tb__ "0|7|
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
  apply (fi_prefix 0 Wai_0A Dai_0A Wbi_0A Wci_0A Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts true (Wcan 0) UStopLe q_0A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe q_0A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 0 UStopLe q_0A Wbm_0A Wcm_0A Wdm_0A Fb_0A XIm_0A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_0A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_0A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_0A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_0A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_0A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_0A : ltac2:(tb__ "0|7|
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
  apply (efi_prefix 0 Wai_0A Dai_0A Wbi_0A Wci_0A ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts true (Wcan 0) UStopLe q_0A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe q_0A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 0 UStopLe q_0A Wbm_0A Wcm_0A Wdm_0A Fb_0A XIm_0A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_0A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_0A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_0A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_0A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_0A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M0A.
End F0A_m0A.

(* [comment removed for export] *)
Module F0A_m2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "q_2Be"; "Ebg_2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "Edr_2Be"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "Xf_2Be"; "exits1_2Be"; "W_2Be"; "st_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2Be"; "PMID_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_q2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_xi2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_d2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0A_a2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_2Be : ltac2:(tb__ "0|0|
SbS15S1eS5cS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_2Be : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6eS12S6S2S1U2A1M4S0A3A1S5cG4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S71A1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_2Be : ltac2:(tb__ "0|0|
SbS15S1eS5eS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_2Be : ltac2:(tb__ "0|0|
SbS15S1eS5fS1U2A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_2Be__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaUbb8S59S5bU2S0A2A4").
Lemma Certi_2Be : ltac2:(tb__ "0|1|
SbS15S3fSaUbb8S59S4aS5bU2M0S0A2S14S10S5aS1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 2 UStopLe) [MIDx (Wcan 2) UStopLe] Certi_2Be__runs); [unfold Certi_2Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_2Be : ltac2:(tb__ "0|2|
SbS15S40SaUbb8S59S4aS5dU2M0S0A2S14S3dS3eS5aS1G0A1S0A2Z0M1S21G1A1A3S16S3dA1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 2 UStopLe) [mkVNA (MIDx (Wcan 2) UStopLe) 0 (SLit 0)] Certi_2Be__runs); [unfold Certi_2Be__runs; reflexivity | vmr]. Qed.

Definition PMID_2Be : axst := ltac2:(tb__ "0|0|
S66S13S31S32S24A4").
Definition Cert1m_2Be__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaS61S14S9S60S16S9A1A3S14S10S41S16S10A1A3A4").
Lemma Cert1m_2Be : ltac2:(tb__ "0|0|
SbS15S3fSaS61S14S9S60S16S9A1A3S4aS14S10S41S16S10A1A3S30A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_2Be] exits1_2Be Cert1m_2Be__runs); [unfold Cert1m_2Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_2Be : ltac2:(tb__ "0|2|
SbS15S40SaS61S14S9S60S16S9A1A3S4aS14S3dS3eS41Z1S21Z0M0A1M1A3S16S3dA1A3S6dS10S3dS10S3eR1G0G1A3LE;S30A4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_2Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_2Be) Cert1m_2Be__runs); [unfold Cert1m_2Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_2Be : ltac2:(tb__ "0|0|
SbS15S1eS67S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_2Be : ltac2:(tb__ "0|0|
SbS15S1eS68S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_2Be : ltac2:(tb__ "0|0|
SbS15S1eS69S1U2A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_2Be : ltac2:(tb__ "0|2|
SbS19S10A1S70S6aS13S1U2M0A1M1S0S24A4S74G0S24A2A2S1bS10S66S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M2Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S50U2S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_2Be : ltac2:(tb__ "0|1|
S9OF_;S56OF_;S51S4S1dS1dS17S53Q40A1A1S55S5R5A1S49Vsegs;R8S48R6A1A3S4fR6R5A2S4dU2M0S0RbRaR9R8R6S26S2bR4AaS4dG0S0RcRbRaR9R7S27S2cR5AaS4dG0S0RdRcRbRaR8S28S2dR6AaS4dG0S0ReRdRcRbR9S29S2eR7AaS4bRfReRdRcRaS25R8A7S4bR10RfReRdRbS2aR9A7S4bR11R10RfReRcS2fRaA7S1dS58Vsegs;R12S47Vsegs;VJFi;S13R11R10ReA4S41R1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_2Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_2Be C3_2Be Ems_2Be C4_2Be TM0_2Be run4_2Be RM_2Be D3_2Be W3_2Be EQ3_2Be NX3b_2Be RUN4_2Be L4_2Be D4_2Be W4_2Be EQ4_2Be
             HeM_2Be HchkM_2Be HTM_2Be FBM_2Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_2Be.
    apply (f0_s5 2%nat st q_2Be false TM_2Be Eq_2Be EQ_2Be TQ0_2Be run5_2Be RQ_2Be NX5_2Be RUN5_2Be L5_2Be AXQ_2Be HeQ_2Be HchkQ_2Be HTQ_2Be FBQ_2Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_2Be.
    apply (f0_s6 2%nat st false TQ_2Be Edr_2Be Xf_2Be run6_2Be NX6_2Be RUN6_2Be L6_2Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true PMID_2Be exits1_2Be Cert1m_2Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_2Be_1 C2_2Be_1 EfD_2Be_1 ED_2Be_1 run2_2Be_1 D2_2Be_1 W2_2Be_1 NX2_2Be_1 EQ2_2Be_1 RUN2_2Be_1 L2_2Be_1 AXD_2Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_1 TDr_2Be_1 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_1 ENTD_2Be_1 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Be_2 C2_2Be_2 EfD_2Be_2 ED_2Be_2 run2_2Be_2 D2_2Be_2 W2_2Be_2 NX2_2Be_2 EQ2_2Be_2 RUN2_2Be_2 L2_2Be_2 AXD_2Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_2 TDr_2Be_2 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_2 ENTD_2Be_2 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Be_3 C2_2Be_3 EfD_2Be_3 ED_2Be_3 run2_2Be_3 D2_2Be_3 W2_2Be_3 NX2_2Be_3 EQ2_2Be_3 RUN2_2Be_3 L2_2Be_3 AXD_2Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_3 TDr_2Be_3 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_3 ENTD_2Be_3 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Be_4 C2_2Be_4 EfD_2Be_4 ED_2Be_4 run2_2Be_4 D2_2Be_4 W2_2Be_4 NX2_2Be_4 EQ2_2Be_4 RUN2_2Be_4 L2_2Be_4 AXD_2Be_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_4 TDr_2Be_4 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_4 ENTD_2Be_4 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_2Be : ltac2:(tb__ "0|1|
S9OF_;S51S4S1dS1dS17S53Q40A1A1S56OF_;S5R5A1S4fR5R4A2S4eU2M0S0R9R8R7R5S26S2bR3A9S4eG0S0RaR9R8R6S27S2cR4A9S4eG0S0RbRaR9R7S28S2dR5A9S4eG0S0RcRbRaR8S29S2eR6A9S4cRdRcRbR9S25R7A6S4cReRdRcRaS2aR8A6S4cRfReRdRbS2fR9A6S1dS57Vsegs;S47Vsegs;VJFi;S13R10RfRdA4S41R1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_2Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_2Be C3_2Be Ems_2Be C4_2Be TM0_2Be run4_2Be RM_2Be D3_2Be W3_2Be EQ3_2Be NX3b_2Be RUN4_2Be L4_2Be D4_2Be W4_2Be EQ4_2Be
             HeM_2Be HchkM_2Be HTM_2Be FBM_2Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_2Be.
    apply (ef0_s5 2%nat st q_2Be false TM_2Be Eq_2Be EQ_2Be TQ0_2Be run5_2Be RQ_2Be NX5_2Be RUN5_2Be L5_2Be AXQ_2Be HeQ_2Be HchkQ_2Be HTQ_2Be FBQ_2Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_2Be.
    apply (ef0_s6 2%nat st false TQ_2Be Edr_2Be Xf_2Be run6_2Be NX6_2Be RUN6_2Be L6_2Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true PMID_2Be exits1_2Be (eq_refl : (GW <=? ss_next (ax_S PMID_2Be))%positive = true) ECert1m_2Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_2Be_1 C2_2Be_1 EfD_2Be_1 ED_2Be_1 run2_2Be_1 D2_2Be_1 W2_2Be_1 NX2_2Be_1 EQ2_2Be_1 RUN2_2Be_1 L2_2Be_1 AXD_2Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_1 TDr_2Be_1 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_1 ENTD_2Be_1 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Be_2 C2_2Be_2 EfD_2Be_2 ED_2Be_2 run2_2Be_2 D2_2Be_2 W2_2Be_2 NX2_2Be_2 EQ2_2Be_2 RUN2_2Be_2 L2_2Be_2 AXD_2Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_2 TDr_2Be_2 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_2 ENTD_2Be_2 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Be_3 C2_2Be_3 EfD_2Be_3 ED_2Be_3 run2_2Be_3 D2_2Be_3 W2_2Be_3 NX2_2Be_3 EQ2_2Be_3 RUN2_2Be_3 L2_2Be_3 AXD_2Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_3 TDr_2Be_3 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_3 ENTD_2Be_3 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Be_4 C2_2Be_4 EfD_2Be_4 ED_2Be_4 run2_2Be_4 D2_2Be_4 W2_2Be_4 NX2_2Be_4 EQ2_2Be_4 RUN2_2Be_4 L2_2Be_4 AXD_2Be_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_4 TDr_2Be_4 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_4 ENTD_2Be_4 RUN3_2Be L3_2Be NX3_2Be
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
S9S42VCST;R1A2ScSdScS43S3bR2A2S44R2S3cA2A2A1SdScS43Z17db48R2A2S44R2Z17db4cA2A2A1A2F_;Fa;").

Theorem free_hi_ia0_2Be : ltac2:(tb__ "0|7|
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
  apply (fi_prefix 2 Wai_2Be Dai_2Be Wbi_2Be Wci_2Be Certi_2Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts true (Wcan 2) UStopLe q_2Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe q_2Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 2 UStopLe q_2Be Wbm_2Be Wcm_2Be Wdm_2Be Fb_2Be XIm_2Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_2Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_2Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_2Be_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_2Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_2Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_2Be : ltac2:(tb__ "0|7|
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
  apply (efi_prefix 2 Wai_2Be Dai_2Be Wbi_2Be Wci_2Be ECerti_2Be A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts true (Wcan 2) UStopLe q_2Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe q_2Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 2 UStopLe q_2Be Wbm_2Be Wcm_2Be Wdm_2Be Fb_2Be XIm_2Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_2Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_2Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_2Be_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_2Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_2Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M2Be.
End F0A_m2Be.

