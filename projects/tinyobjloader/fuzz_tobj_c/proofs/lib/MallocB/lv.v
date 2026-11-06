(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ll lp.

(* [comment removed for export] *)
Module F0A_mL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be"; "q_L2Be"; "Ebg_L2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "Edr_L2Be"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "Xf_L2Be"; "exits1_L2Be"; "W_L2Be"; "st_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lv.F0A_mL2Be"; "PMID_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iz.F0A_iL2Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ld.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ll.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ld.F0A_xiL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0A_dL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ll.F0A_aL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iz.F0A_iL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.
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
S9S42VCST;R1A2ScSdScS43S3bR2A2S44R2S3cA2A2A1SdScS43Z17db48R2A2S44R2Z17db4cA2A2A1A2F_;Fa;").

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
Module F0A_mL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf"; "q_L2Bf"; "Ebg_L2Bf"; "ED_L2Bf_1"; "ED_L2Bf_2"; "ED_L2Bf_3"; "ED_L2Bf_4"; "Edr_L2Bf"; "TD_L2Bf_1"; "TD_L2Bf_2"; "TD_L2Bf_3"; "TD_L2Bf_4"; "Xf_L2Bf"; "exits1_L2Bf"; "W_L2Bf"; "st_L2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lv.F0A_mL2Bf"; "PMID_L2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iz.F0A_iL2Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ld.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ll.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ld.F0A_xiL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0A_dL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ll.F0A_aL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iz.F0A_iL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L2Bf : ltac2:(tb__ "0|0|
SbS14S1eS5cS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L2Bf : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6eS12S6S2S1U2A1M4S0A3A1S5cG4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S71A1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L2Bf : ltac2:(tb__ "0|0|
SbS14S1eS5eS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L2Bf : ltac2:(tb__ "0|0|
SbS14S1eS5fS1U2A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L2Bf__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaUbb8S59S5bU2S0A2A4").
Lemma Certi_L2Bf : ltac2:(tb__ "0|1|
SbS14S3fSaUbb8S59S4aS5bU2M0S0A2S13S10S5aS1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 2 UStopLe) [MIDx (Wcan 2) UStopLe] Certi_L2Bf__runs); [unfold Certi_L2Bf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L2Bf : ltac2:(tb__ "0|2|
SbS14S40SaUbb8S59S4aS5dU2M0S0A2S13S3dS3eS5aS1G0A1S0A2Z0M1S21G1A1A3S15S3dA1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 2 UStopLe) [mkVNA (MIDx (Wcan 2) UStopLe) 0 (SLit 0)] Certi_L2Bf__runs); [unfold Certi_L2Bf__runs; reflexivity | vmr]. Qed.

Definition PMID_L2Bf : axst := ltac2:(tb__ "0|0|
S66S19S31S32S24A4").
Definition Cert1m_L2Bf__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S62SaS61S13S9S60S15S9A1A3S13S10S41S15S10A1A3A4").
Lemma Cert1m_L2Bf : ltac2:(tb__ "0|0|
SbS14S3fSaS61S13S9S60S15S9A1A3S4aS13S10S41S15S10A1A3S30A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L2Bf] exits1_L2Bf Cert1m_L2Bf__runs); [unfold Cert1m_L2Bf__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L2Bf : ltac2:(tb__ "0|2|
SbS14S40SaS61S13S9S60S15S9A1A3S4aS13S3dS3eS41Z1S21Z0M0A1M1A3S15S3dA1A3S6dS10S3dS10S3eR1G0G1A3LE;S30A4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L2Bf 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L2Bf) Cert1m_L2Bf__runs); [unfold Cert1m_L2Bf__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L2Bf : ltac2:(tb__ "0|0|
SbS14S1eS67S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L2Bf : ltac2:(tb__ "0|0|
SbS14S1eS68S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L2Bf : ltac2:(tb__ "0|0|
SbS14S1eS69S1U2A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L2Bf : ltac2:(tb__ "0|2|
SbS1aS10A1S70S6aS19S1U2M0A1M1S0S24A4S74G0S24A2A2S1cS10S66S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML2Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S50U2S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L2Bf : ltac2:(tb__ "0|1|
S9OF_;S56OF_;S51S4S1dS1dS17S53Q40A1A1S55S5R5A1S49Vsegs;R8S48R6A1A3S4fR6R5A2S4dU2M0S0RbRaR9R8R6S26S2bR4AaS4dG0S0RcRbRaR9R7S27S2cR5AaS4dG0S0RdRcRbRaR8S28S2dR6AaS4dG0S0ReRdRcRbR9S29S2eR7AaS4bRfReRdRcRaS25R8A7S4bR10RfReRdRbS2aR9A7S4bR11R10RfReRcS2fRaA7S1dS58Vsegs;R12S47Vsegs;VJFi;S16R11R10ReA4S41R1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L2Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_L2Bf C3_L2Bf Ems_L2Bf C4_L2Bf TM0_L2Bf run4_L2Bf RM_L2Bf D3_L2Bf W3_L2Bf EQ3_L2Bf NX3b_L2Bf RUN4_L2Bf L4_L2Bf D4_L2Bf W4_L2Bf EQ4_L2Bf
             HeM_L2Bf HchkM_L2Bf HTM_L2Bf FBM_L2Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L2Bf.
    apply (f0_s5 2%nat st q_L2Bf false TM_L2Bf Eq_L2Bf EQ_L2Bf TQ0_L2Bf run5_L2Bf RQ_L2Bf NX5_L2Bf RUN5_L2Bf L5_L2Bf AXQ_L2Bf HeQ_L2Bf HchkQ_L2Bf HTQ_L2Bf FBQ_L2Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L2Bf.
    apply (f0_s6 2%nat st false TQ_L2Bf Edr_L2Bf Xf_L2Bf run6_L2Bf NX6_L2Bf RUN6_L2Bf L6_L2Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true PMID_L2Bf exits1_L2Bf Cert1m_L2Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_L2Bf_1 C2_L2Bf_1 EfD_L2Bf_1 ED_L2Bf_1 run2_L2Bf_1 D2_L2Bf_1 W2_L2Bf_1 NX2_L2Bf_1 EQ2_L2Bf_1 RUN2_L2Bf_1 L2_L2Bf_1 AXD_L2Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_1 TDr_L2Bf_1 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_1 ENTD_L2Bf_1 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Bf_2 C2_L2Bf_2 EfD_L2Bf_2 ED_L2Bf_2 run2_L2Bf_2 D2_L2Bf_2 W2_L2Bf_2 NX2_L2Bf_2 EQ2_L2Bf_2 RUN2_L2Bf_2 L2_L2Bf_2 AXD_L2Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_2 TDr_L2Bf_2 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_2 ENTD_L2Bf_2 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Bf_3 C2_L2Bf_3 EfD_L2Bf_3 ED_L2Bf_3 run2_L2Bf_3 D2_L2Bf_3 W2_L2Bf_3 NX2_L2Bf_3 EQ2_L2Bf_3 RUN2_L2Bf_3 L2_L2Bf_3 AXD_L2Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_3 TDr_L2Bf_3 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_3 ENTD_L2Bf_3 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Bf_4 C2_L2Bf_4 EfD_L2Bf_4 ED_L2Bf_4 run2_L2Bf_4 D2_L2Bf_4 W2_L2Bf_4 NX2_L2Bf_4 EQ2_L2Bf_4 RUN2_L2Bf_4 L2_L2Bf_4 AXD_L2Bf_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_4 TDr_L2Bf_4 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_4 ENTD_L2Bf_4 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L2Bf : ltac2:(tb__ "0|1|
S9OF_;S51S4S1dS1dS17S53Q40A1A1S56OF_;S5R5A1S4fR5R4A2S4eU2M0S0R9R8R7R5S26S2bR3A9S4eG0S0RaR9R8R6S27S2cR4A9S4eG0S0RbRaR9R7S28S2dR5A9S4eG0S0RcRbRaR8S29S2eR6A9S4cRdRcRbR9S25R7A6S4cReRdRcRaS2aR8A6S4cRfReRdRbS2fR9A6S1dS57Vsegs;S47Vsegs;VJFi;S16R10RfRdA4S41R1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L2Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_L2Bf C3_L2Bf Ems_L2Bf C4_L2Bf TM0_L2Bf run4_L2Bf RM_L2Bf D3_L2Bf W3_L2Bf EQ3_L2Bf NX3b_L2Bf RUN4_L2Bf L4_L2Bf D4_L2Bf W4_L2Bf EQ4_L2Bf
             HeM_L2Bf HchkM_L2Bf HTM_L2Bf FBM_L2Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L2Bf.
    apply (ef0_s5 2%nat st q_L2Bf false TM_L2Bf Eq_L2Bf EQ_L2Bf TQ0_L2Bf run5_L2Bf RQ_L2Bf NX5_L2Bf RUN5_L2Bf L5_L2Bf AXQ_L2Bf HeQ_L2Bf HchkQ_L2Bf HTQ_L2Bf FBQ_L2Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L2Bf.
    apply (ef0_s6 2%nat st false TQ_L2Bf Edr_L2Bf Xf_L2Bf run6_L2Bf NX6_L2Bf RUN6_L2Bf L6_L2Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true PMID_L2Bf exits1_L2Bf (eq_refl : (GW <=? ss_next (ax_S PMID_L2Bf))%positive = true) ECert1m_L2Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_L2Bf_1 C2_L2Bf_1 EfD_L2Bf_1 ED_L2Bf_1 run2_L2Bf_1 D2_L2Bf_1 W2_L2Bf_1 NX2_L2Bf_1 EQ2_L2Bf_1 RUN2_L2Bf_1 L2_L2Bf_1 AXD_L2Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_1 TDr_L2Bf_1 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_1 ENTD_L2Bf_1 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Bf_2 C2_L2Bf_2 EfD_L2Bf_2 ED_L2Bf_2 run2_L2Bf_2 D2_L2Bf_2 W2_L2Bf_2 NX2_L2Bf_2 EQ2_L2Bf_2 RUN2_L2Bf_2 L2_L2Bf_2 AXD_L2Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_2 TDr_L2Bf_2 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_2 ENTD_L2Bf_2 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Bf_3 C2_L2Bf_3 EfD_L2Bf_3 ED_L2Bf_3 run2_L2Bf_3 D2_L2Bf_3 W2_L2Bf_3 NX2_L2Bf_3 EQ2_L2Bf_3 RUN2_L2Bf_3 L2_L2Bf_3 AXD_L2Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_3 TDr_L2Bf_3 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_3 ENTD_L2Bf_3 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Bf_4 C2_L2Bf_4 EfD_L2Bf_4 ED_L2Bf_4 run2_L2Bf_4 D2_L2Bf_4 W2_L2Bf_4 NX2_L2Bf_4 EQ2_L2Bf_4 RUN2_L2Bf_4 L2_L2Bf_4 AXD_L2Bf_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_4 TDr_L2Bf_4 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_4 ENTD_L2Bf_4 RUN3_L2Bf L3_L2Bf NX3_L2Bf
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

Theorem free_lo_ia0_2Bf : ltac2:(tb__ "0|7|
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
  apply (fi_prefix 2 Wai_L2Bf Dai_L2Bf Wbi_L2Bf Wci_L2Bf Certi_L2Bf ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts false (Wcan 2) UStopLe q_L2Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe q_L2Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 2 UStopLe q_L2Bf Wbm_L2Bf Wcm_L2Bf Wdm_L2Bf Fb_L2Bf XIm_L2Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L2Bf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L2Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L2Bf_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L2Bf CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L2Bf CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_2Bf : ltac2:(tb__ "0|7|
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
  apply (efi_prefix 2 Wai_L2Bf Dai_L2Bf Wbi_L2Bf Wci_L2Bf ECerti_L2Bf A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts false (Wcan 2) UStopLe q_L2Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe q_L2Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 2 UStopLe q_L2Bf Wbm_L2Bf Wcm_L2Bf Wdm_L2Bf Fb_L2Bf XIm_L2Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L2Bf (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L2Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L2Bf_4 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L2Bf CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L2Bf CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML2Bf.
End F0A_mL2Bf.

(* [comment removed for export] *)
Module F0A_m1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be"; "q_1Be"; "Ebg_1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "Edr_1Be"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "Xf_1Be"; "exits1_1Be"; "W_1Be"; "st_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lv.F0A_m1Be"; "PMID_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst";
"XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_d1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.F0A_a1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_1Be : ltac2:(tb__ "0|0|
SbS15S1eS5aS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_1Be : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6cS12S6S2S1U1A1M4S0A3A1S5aG4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S6fA1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_1Be : ltac2:(tb__ "0|0|
SbS15S1eS5cS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_1Be : ltac2:(tb__ "0|0|
SbS15S1eS5dS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_1Be__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaUbb8S57S59U1S0A2A4").
Lemma Certi_1Be : ltac2:(tb__ "0|1|
SbS15S3dSaUbb8S57S48S59U1M0S0A2S14S10S58S1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 1 UStopLe) [MIDx (Wcan 1) UStopLe] Certi_1Be__runs); [unfold Certi_1Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_1Be : ltac2:(tb__ "0|2|
SbS15S3eSaUbb8S57S48S5bU1M0S0A2S14S3bS3cS58S1G0A1S0A2Z0M1S21G1A1A3S16S3bA1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 1 UStopLe) [mkVNA (MIDx (Wcan 1) UStopLe) 0 (SLit 0)] Certi_1Be__runs); [unfold Certi_1Be__runs; reflexivity | vmr]. Qed.

Definition PMID_1Be : axst := ltac2:(tb__ "0|0|
S64S13S2fS30S24A4").
Definition Cert1m_1Be__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaS5fS14S9S5eS16S9A1A3S14S10S3fS16S10A1A3A4").
Lemma Cert1m_1Be : ltac2:(tb__ "0|0|
SbS15S3dSaS5fS14S9S5eS16S9A1A3S48S14S10S3fS16S10A1A3S2eA6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_1Be] exits1_1Be Cert1m_1Be__runs); [unfold Cert1m_1Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_1Be : ltac2:(tb__ "0|2|
SbS15S3eSaS5fS14S9S5eS16S9A1A3S48S14S3bS3cS3fZ1S21Z0M0A1M1A3S16S3bA1A3S6bS10S3bS10S3cR1G0G1A3LE;S2eA4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_1Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_1Be) Cert1m_1Be__runs); [unfold Cert1m_1Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_1Be : ltac2:(tb__ "0|0|
SbS15S1eS65S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_1Be : ltac2:(tb__ "0|0|
SbS15S1eS66S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_1Be : ltac2:(tb__ "0|0|
SbS15S1eS67S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_1Be : ltac2:(tb__ "0|2|
SbS19S10A1S6eS68S13S1U1M0A1M1S0S24A4S72G0S24A2A2S1bS10S64S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M1Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4eU1S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_1Be : ltac2:(tb__ "0|1|
S9OF_;S54OF_;S4fS4S1dS1dS17S51Q40A1A1S53S5R5A1S47Vsegs;R8S46R6A1A3S4bR6R5A2S4cU1M0S0RbRaR9R8R6S26S2aR4AaS4cG0S0RcRbRaR9R7S27S2bR5AaS4cG0S0RdRcRbRaR8S28S2cR6AaS49ReRdRcRbR9S25R7A7S49RfReRdRcRaS29R8A7S49R10RfReRdRbS2dR9A7S1dS56Vsegs;R11S45Vsegs;VJFi;S13R10RfRdA4S3fR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_1Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_1Be C3_1Be Ems_1Be C4_1Be TM0_1Be run4_1Be RM_1Be D3_1Be W3_1Be EQ3_1Be NX3b_1Be RUN4_1Be L4_1Be D4_1Be W4_1Be EQ4_1Be
             HeM_1Be HchkM_1Be HTM_1Be FBM_1Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_1Be.
    apply (f0_s5 1%nat st q_1Be false TM_1Be Eq_1Be EQ_1Be TQ0_1Be run5_1Be RQ_1Be NX5_1Be RUN5_1Be L5_1Be AXQ_1Be HeQ_1Be HchkQ_1Be HTQ_1Be FBQ_1Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_1Be.
    apply (f0_s6 1%nat st false TQ_1Be Edr_1Be Xf_1Be run6_1Be NX6_1Be RUN6_1Be L6_1Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true PMID_1Be exits1_1Be Cert1m_1Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_1Be_1 C2_1Be_1 EfD_1Be_1 ED_1Be_1 run2_1Be_1 D2_1Be_1 W2_1Be_1 NX2_1Be_1 EQ2_1Be_1 RUN2_1Be_1 L2_1Be_1 AXD_1Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Be_1 TDr_1Be_1 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_1 ENTD_1Be_1 RUN3_1Be L3_1Be NX3_1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Be_2 C2_1Be_2 EfD_1Be_2 ED_1Be_2 run2_1Be_2 D2_1Be_2 W2_1Be_2 NX2_1Be_2 EQ2_1Be_2 RUN2_1Be_2 L2_1Be_2 AXD_1Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Be_2 TDr_1Be_2 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_2 ENTD_1Be_2 RUN3_1Be L3_1Be NX3_1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Be_3 C2_1Be_3 EfD_1Be_3 ED_1Be_3 run2_1Be_3 D2_1Be_3 W2_1Be_3 NX2_1Be_3 EQ2_1Be_3 RUN2_1Be_3 L2_1Be_3 AXD_1Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Be_3 TDr_1Be_3 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_3 ENTD_1Be_3 RUN3_1Be L3_1Be NX3_1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_1Be : ltac2:(tb__ "0|1|
S9OF_;S4fS4S1dS1dS17S51Q40A1A1S54OF_;S5R5A1S4bR5R4A2S4dU1M0S0R9R8R7R5S26S2aR3A9S4dG0S0RaR9R8R6S27S2bR4A9S4dG0S0RbRaR9R7S28S2cR5A9S4aRcRbRaR8S25R6A6S4aRdRcRbR9S29R7A6S4aReRdRcRaS2dR8A6S1dS55Vsegs;S45Vsegs;VJFi;S13RfReRcA4S3fR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_1Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_1Be C3_1Be Ems_1Be C4_1Be TM0_1Be run4_1Be RM_1Be D3_1Be W3_1Be EQ3_1Be NX3b_1Be RUN4_1Be L4_1Be D4_1Be W4_1Be EQ4_1Be
             HeM_1Be HchkM_1Be HTM_1Be FBM_1Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_1Be.
    apply (ef0_s5 1%nat st q_1Be false TM_1Be Eq_1Be EQ_1Be TQ0_1Be run5_1Be RQ_1Be NX5_1Be RUN5_1Be L5_1Be AXQ_1Be HeQ_1Be HchkQ_1Be HTQ_1Be FBQ_1Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_1Be.
    apply (ef0_s6 1%nat st false TQ_1Be Edr_1Be Xf_1Be run6_1Be NX6_1Be RUN6_1Be L6_1Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true PMID_1Be exits1_1Be (eq_refl : (GW <=? ss_next (ax_S PMID_1Be))%positive = true) ECert1m_1Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_1Be_1 C2_1Be_1 EfD_1Be_1 ED_1Be_1 run2_1Be_1 D2_1Be_1 W2_1Be_1 NX2_1Be_1 EQ2_1Be_1 RUN2_1Be_1 L2_1Be_1 AXD_1Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Be_1 TDr_1Be_1 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_1 ENTD_1Be_1 RUN3_1Be L3_1Be NX3_1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Be_2 C2_1Be_2 EfD_1Be_2 ED_1Be_2 run2_1Be_2 D2_1Be_2 W2_1Be_2 NX2_1Be_2 EQ2_1Be_2 RUN2_1Be_2 L2_1Be_2 AXD_1Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Be_2 TDr_1Be_2 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_2 ENTD_1Be_2 RUN3_1Be L3_1Be NX3_1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Be_3 C2_1Be_3 EfD_1Be_3 ED_1Be_3 run2_1Be_3 D2_1Be_3 W2_1Be_3 NX2_1Be_3 EQ2_1Be_3 RUN2_1Be_3 L2_1Be_3 AXD_1Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Be_3 TDr_1Be_3 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_3 ENTD_1Be_3 RUN3_1Be L3_1Be NX3_1Be
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

Theorem free_hi_ia0_1Be : ltac2:(tb__ "0|7|
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
  apply (fi_prefix 1 Wai_1Be Dai_1Be Wbi_1Be Wci_1Be Certi_1Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts true (Wcan 1) UStopLe q_1Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe q_1Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 1 UStopLe q_1Be Wbm_1Be Wcm_1Be Wdm_1Be Fb_1Be XIm_1Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_1Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_1Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_1Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_1Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_1Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_1Be : ltac2:(tb__ "0|7|
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
  apply (efi_prefix 1 Wai_1Be Dai_1Be Wbi_1Be Wci_1Be ECerti_1Be A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts true (Wcan 1) UStopLe q_1Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe q_1Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 1 UStopLe q_1Be Wbm_1Be Wcm_1Be Wdm_1Be Fb_1Be XIm_1Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_1Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_1Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_1Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_1Be_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_1Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M1Be.
End F0A_m1Be.

(* [comment removed for export] *)
Module F0A_m1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "nil"; "list"; "pair"; "option"; "prod"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf"; "q_1Bf"; "Ebg_1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "Edr_1Bf"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "Xf_1Bf"; "exits1_1Bf"; "W_1Bf"; "st_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lv.F0A_m1Bf"; "PMID_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst";
"XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_d1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.F0A_a1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_1Bf : ltac2:(tb__ "0|0|
SbS15S1eS5aS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Dai_1Bf : ltac2:(tb__ "0|5|
SbS19S1aS17S1aS20S20A2M0A1M1S17S22A1M2A2M3A1S6cS12S6S2S1U1A1M4S0A3A1S5aG4S0A2A2S1bG3S18G1G2S14G0S18S20S20S23P18A1S21S6fA1A4S16G0A1A3S16S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_1Bf : ltac2:(tb__ "0|0|
SbS15S1eS5cS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Lemma Wci_1Bf : ltac2:(tb__ "0|0|
SbS15S1eS5dS1U1A1S0A2A1S13A3"). Proof. vmr. Qed.
Definition Certi_1Bf__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaUbb8S57S59U1S0A2A4").
Lemma Certi_1Bf : ltac2:(tb__ "0|1|
SbS15S3dSaUbb8S57S48S59U1M0S0A2S14S10S58S1G0A1S0A2S16S10A1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 1 UStopLe) [MIDx (Wcan 1) UStopLe] Certi_1Bf__runs); [unfold Certi_1Bf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_1Bf : ltac2:(tb__ "0|2|
SbS15S3eSaUbb8S57S48S5bU1M0S0A2S14S3bS3cS58S1G0A1S0A2Z0M1S21G1A1A3S16S3bA1A3A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 1 UStopLe) [mkVNA (MIDx (Wcan 1) UStopLe) 0 (SLit 0)] Certi_1Bf__runs); [unfold Certi_1Bf__runs; reflexivity | vmr]. Qed.

Definition PMID_1Bf : axst := ltac2:(tb__ "0|0|
S64S13S2fS30S24A4").
Definition Cert1m_1Bf__runs : ltac2:(tb__ "0|0|
S17S19S17S11A1A1A1") := ltac2:(tb__ "0|0|
S60SaS5fS14S9S5eS16S9A1A3S14S10S3fS16S10A1A3A4").
Lemma Cert1m_1Bf : ltac2:(tb__ "0|0|
SbS15S3dSaS5fS14S9S5eS16S9A1A3S48S14S10S3fS16S10A1A3S2eA6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_1Bf] exits1_1Bf Cert1m_1Bf__runs); [unfold Cert1m_1Bf__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_1Bf : ltac2:(tb__ "0|2|
SbS15S3eSaS5fS14S9S5eS16S9A1A3S48S14S3bS3cS3fZ1S21Z0M0A1M1A3S16S3bA1A3S6bS10S3bS10S3cR1G0G1A3LE;S2eA4A6S13A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_1Bf 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_1Bf) Cert1m_1Bf__runs); [unfold Cert1m_1Bf__runs; reflexivity | vmr]. Qed.

Lemma Wbm_1Bf : ltac2:(tb__ "0|0|
SbS15S1eS65S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wcm_1Bf : ltac2:(tb__ "0|0|
SbS15S1eS66S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma Wdm_1Bf : ltac2:(tb__ "0|0|
SbS15S1eS67S1U1A1S0S24A3A1S13A3"). Proof. vmr. Qed.
Lemma XIm_1Bf : ltac2:(tb__ "0|2|
SbS19S10A1S6eS68S13S1U1M0A1M1S0S24A4S72G0S24A2A2S1bS10S64S13G1S0S24A4A2A3"). Proof. vmr. Qed.

Section M1Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4eU1S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_1Bf : ltac2:(tb__ "0|1|
S9OF_;S54OF_;S4fS4S1dS1dS17S51Q40A1A1S53S5R5A1S47Vsegs;R8S46R6A1A3S4bR6R5A2S4cU1M0S0RbRaR9R8R6S26S2aR4AaS4cG0S0RcRbRaR9R7S27S2bR5AaS4cG0S0RdRcRbRaR8S28S2cR6AaS49ReRdRcRbR9S25R7A7S49RfReRdRcRaS29R8A7S49R10RfReRdRbS2dR9A7S1dS56Vsegs;R11S45Vsegs;VJFi;S13R10RfRdA4S3fR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_1Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_1Bf C3_1Bf Ems_1Bf C4_1Bf TM0_1Bf run4_1Bf RM_1Bf D3_1Bf W3_1Bf EQ3_1Bf NX3b_1Bf RUN4_1Bf L4_1Bf D4_1Bf W4_1Bf EQ4_1Bf
             HeM_1Bf HchkM_1Bf HTM_1Bf FBM_1Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_1Bf.
    apply (f0_s5 1%nat st q_1Bf false TM_1Bf Eq_1Bf EQ_1Bf TQ0_1Bf run5_1Bf RQ_1Bf NX5_1Bf RUN5_1Bf L5_1Bf AXQ_1Bf HeQ_1Bf HchkQ_1Bf HTQ_1Bf FBQ_1Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_1Bf.
    apply (f0_s6 1%nat st false TQ_1Bf Edr_1Bf Xf_1Bf run6_1Bf NX6_1Bf RUN6_1Bf L6_1Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true PMID_1Bf exits1_1Bf Cert1m_1Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_1Bf_1 C2_1Bf_1 EfD_1Bf_1 ED_1Bf_1 run2_1Bf_1 D2_1Bf_1 W2_1Bf_1 NX2_1Bf_1 EQ2_1Bf_1 RUN2_1Bf_1 L2_1Bf_1 AXD_1Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Bf_1 TDr_1Bf_1 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_1 ENTD_1Bf_1 RUN3_1Bf L3_1Bf NX3_1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Bf_2 C2_1Bf_2 EfD_1Bf_2 ED_1Bf_2 run2_1Bf_2 D2_1Bf_2 W2_1Bf_2 NX2_1Bf_2 EQ2_1Bf_2 RUN2_1Bf_2 L2_1Bf_2 AXD_1Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Bf_2 TDr_1Bf_2 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_2 ENTD_1Bf_2 RUN3_1Bf L3_1Bf NX3_1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Bf_3 C2_1Bf_3 EfD_1Bf_3 ED_1Bf_3 run2_1Bf_3 D2_1Bf_3 W2_1Bf_3 NX2_1Bf_3 EQ2_1Bf_3 RUN2_1Bf_3 L2_1Bf_3 AXD_1Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Bf_3 TDr_1Bf_3 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_3 ENTD_1Bf_3 RUN3_1Bf L3_1Bf NX3_1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_1Bf : ltac2:(tb__ "0|1|
S9OF_;S4fS4S1dS1dS17S51Q40A1A1S54OF_;S5R5A1S4bR5R4A2S4dU1M0S0R9R8R7R5S26S2aR3A9S4dG0S0RaR9R8R6S27S2bR4A9S4dG0S0RbRaR9R7S28S2cR5A9S4aRcRbRaR8S25R6A6S4aRdRcRbR9S29R7A6S4aReRdRcRaS2dR8A6S1dS55Vsegs;S45Vsegs;VJFi;S13RfReRcA4S3fR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_1Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_1Bf C3_1Bf Ems_1Bf C4_1Bf TM0_1Bf run4_1Bf RM_1Bf D3_1Bf W3_1Bf EQ3_1Bf NX3b_1Bf RUN4_1Bf L4_1Bf D4_1Bf W4_1Bf EQ4_1Bf
             HeM_1Bf HchkM_1Bf HTM_1Bf FBM_1Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_1Bf.
    apply (ef0_s5 1%nat st q_1Bf false TM_1Bf Eq_1Bf EQ_1Bf TQ0_1Bf run5_1Bf RQ_1Bf NX5_1Bf RUN5_1Bf L5_1Bf AXQ_1Bf HeQ_1Bf HchkQ_1Bf HTQ_1Bf FBQ_1Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_1Bf.
    apply (ef0_s6 1%nat st false TQ_1Bf Edr_1Bf Xf_1Bf run6_1Bf NX6_1Bf RUN6_1Bf L6_1Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true PMID_1Bf exits1_1Bf (eq_refl : (GW <=? ss_next (ax_S PMID_1Bf))%positive = true) ECert1m_1Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_1Bf_1 C2_1Bf_1 EfD_1Bf_1 ED_1Bf_1 run2_1Bf_1 D2_1Bf_1 W2_1Bf_1 NX2_1Bf_1 EQ2_1Bf_1 RUN2_1Bf_1 L2_1Bf_1 AXD_1Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Bf_1 TDr_1Bf_1 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_1 ENTD_1Bf_1 RUN3_1Bf L3_1Bf NX3_1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Bf_2 C2_1Bf_2 EfD_1Bf_2 ED_1Bf_2 run2_1Bf_2 D2_1Bf_2 W2_1Bf_2 NX2_1Bf_2 EQ2_1Bf_2 RUN2_1Bf_2 L2_1Bf_2 AXD_1Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Bf_2 TDr_1Bf_2 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_2 ENTD_1Bf_2 RUN3_1Bf L3_1Bf NX3_1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Bf_3 C2_1Bf_3 EfD_1Bf_3 ED_1Bf_3 run2_1Bf_3 D2_1Bf_3 W2_1Bf_3 NX2_1Bf_3 EQ2_1Bf_3 RUN2_1Bf_3 L2_1Bf_3 AXD_1Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Bf_3 TDr_1Bf_3 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_3 ENTD_1Bf_3 RUN3_1Bf L3_1Bf NX3_1Bf
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

Theorem free_hi_ia0_1Bf : ltac2:(tb__ "0|7|
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
  apply (fi_prefix 1 Wai_1Bf Dai_1Bf Wbi_1Bf Wci_1Bf Certi_1Bf ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instF_facts true (Wcan 1) UStopLe q_1Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe q_1Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid true 1 UStopLe q_1Bf Wbm_1Bf Wcm_1Bf Wdm_1Bf Fb_1Bf XIm_1Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_1Bf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_1Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_1Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_1Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_1Bf CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_1Bf CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_ia0_1Bf : ltac2:(tb__ "0|7|
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
  apply (efi_prefix 1 Wai_1Bf Dai_1Bf Wbi_1Bf Wci_1Bf ECerti_1Bf A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instF_facts true (Wcan 1) UStopLe q_1Bf (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe q_1Bf HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid true 1 UStopLe q_1Bf Wbm_1Bf Wcm_1Bf Wdm_1Bf Fb_1Bf XIm_1Bf A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_1Bf (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_1Bf_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_1Bf_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_1Bf_3 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_1Bf CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_1Bf CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End M1Bf.
End F0A_m1Bf.

