(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2 an.

(* [comment removed for export] *)
Module SpineCallocS1i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_callocI"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "option"; "app"; "nil"; "pair"; "Some"; "cons"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sprop_below"; "ss_next"; "SLit"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "P0c"; "E_s1"; "F_hi_p"; "F_lo_p"; "E_pre"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "FACTSe"; "F_hi_e"; "F_lo_e"; "P0e"; "sa_c"; "sb_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "s_sw"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1"; "dp_okb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wa_c : ltac2:(tb__ "0|0|
SfS4S13S28S1U0A1S0A2A1S5A3"). Proof. MemoFast.vmc. Qed.
Lemma Da_c : ltac2:(tb__ "0|5|
SfS8S6S7S6S12S12A2M0A1M1S7S11A1M2A2M3A1S21S18S3S2S1U0A1M4S0A3A1S28G4S0A2A2ScG3SbG1G2SdG0SbS12S12S17P18A1S16S2dA1A4SaG0A1A3SaS11A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma Wb_c : ltac2:(tb__ "0|0|
SfS4S13S29S1U0A1S0A2A1S5A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbh_c : ltac2:(tb__ "0|0|
SfS4S2bS11S14S22A1S9S11S24S1U0A1S0A2S25A3A3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbl_c : ltac2:(tb__ "0|0|
SfS4S2bS11S14S22A1S9S11S24S1U0A1S0A2S26A3A3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTh_c : ltac2:(tb__ "0|1|
SfS4S19S27S1U0A1M0S0S25A3S1aG0S0S1cA3S2aA3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTl_c : ltac2:(tb__ "0|1|
SfS4S19S27S1U0A1M0S0S26A3S1aG0S0S1dA3S2aA3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma WE1_c : ltac2:(tb__ "0|0|
S20S10S1fZ0R1A2S1fR1Z8A2A2SfS4S13S18S1bS1U0A1S0Z2R2A4A1A1S5A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DE1_c : ltac2:(tb__ "0|5|
S20S10S1fZ0R1A2S1fR1Z8A2A2SfS4S8S6S7S6S12S12A2A1M0S7S11A1M1A2M2A1S4Lx;S21S18S1eS1U0A1M3S0Z2M4R2A4A1S18S1bG3S0G4R2A4A1A2G2G2S4Lp;R1G0G1S2eR5R2A2Ll;Ld;X6x1Lp;SeX8x2S5A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HSW_c : stopJ_sw (Wcan 0) UStopLe. Proof. apply stopJ_sw_le. Qed.
Lemma HUS_c : stopJ_stable (Wcan 0) UStopLe. Proof. apply stopJ_stable_le. Qed.
Lemma NXhi_c : ltac2:(tb__ "0|0|
S2cS23S15S18S1aS1U0A1S0S1cA3A1A1A2"). Proof. apply Pos.leb_le. MemoFast.vmc. Qed.
Lemma NXlo_c : ltac2:(tb__ "0|0|
S2cS23S15S18S1aS1U0A1S0S1dA3A1A1A2"). Proof. apply Pos.leb_le. MemoFast.vmc. Qed.
End SpineCallocS1i.

(* [comment removed for export] *)
Module CSecOKInv.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "modulo"; "pow"; "sub"; "div"; "ge"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "alloc_top"; "event"; "m_vm_lazy"; "vm_noaccess"; "vm_reserved"; "region_free"; "vm_limit"; "with_vmmaps"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "app"; "cons"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "GN"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "FS_total"; "IMG_HI"; "IMG_LO"; "dyn_in"; "kPtrArrayReserve"; "kSpaceSize"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_V"; "aa_depot"; "aa_geom"; "aa_sec"; "sec_chunk"; "DG"; "aa_Kf"; "aa_Km"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "ageom"; "budget_ok_alloc"; "mkAA"; "sc_map_beg"; "sc_map_size"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv.JGS"; "JGs"; "SHC"; "JGsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "depot_vm"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bumpV (A : AA) (n : Z) : AA := ltac2:(tb__ "0|0|
S4fS38VA;A1S3fVA;A1S3eVA;A1S39VA;A1S44VA;A1S43VA;A1S46VA;A1S45VA;A1S37VA;A1S41VA;A1S40VA;A1S42VA;A1S5S36VA;A1Vn;A2S3dVA;A1S3cVA;A1Af").

Definition pendS (A : AA) (ua L : Z) (md : Model) : Prop := ltac2:(tb__ "0|6|
S38VA;A1S4dS1S33S1aS20Q40M0A1M1G1A2S19G1G1S21G0Vua;A2S21G0VL;A2A4SfSdVmd;A1A1A3S1S2S0S8Vua;S2cA2Z0M2A3S1S6G2VL;A2S1S30S52R1A1Vua;VL;A3S1S26S19S0S0Vua;VL;A4M3S19S0S0S4cR1A1Z1000M4A4A2S1S26G3S19S0S0S47R1A1G4A4A2S1S26G3S19S0S0S48R1A1G4A4A2S1S26G3S19S0S0S49R1A1S2dA4A2S1S26G3S19S0S0S4bR1A1S5S32G4A2A4A2S1S26G3S19S0S0S4aR1A1S31A4A2S1S3aS33S3aR1S39VA;A1A3S26G3S19S0S0S50R2A1S51R2A1A4A2F_;Fch;S1aS0S0A2M5S33G5R1S66S37VA;A1A1A3S26R2G3A2F_;Fbn;A2A2A2A2A2A2A2A2A2A2A2TG;").

Section S.
Let segs : list Segment := segsA.

Lemma depot_vm_grow : ltac2:(tb__ "0|6|
S3bSeSeS18S20Q40A1M0A1S1aG0G0A2M1S33G1R1SfSdR4A1M2A1M3A3S33G1R2G3A3F_;Fe;S2S18G1A1M4S12R3A1S12R4A1A3S2G4S13G2A1S13SdR5A1M5A1A3S2S0S10G5A1S10SdR6A1A1A3S65R8R7R5A3S65R9R7R6A3F_;F_;F_;F_;F_;Ftp;Fmd';Fmd;FG;").
Proof.
  intros G md md' tp Hm Hl Hna Htop [A B C D E F]. constructor.
  - intros bn Hbn. apply Hm. exact (A bn Hbn).
  - intros b Hb. rewrite Hl. exact (B b Hb).
  - intros b j Hb Hj. rewrite Hna. exact (C b j Hb Hj).
  - exact D.
  - intros bn Hbn. rewrite Htop. exact (E bn Hbn).
  - rewrite Htop. exact F.
Qed.

Lemma AInvA_sec_grant : ltac2:(tb__ "0|a|
S35S0S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1M3SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1M4A1A3A3S2G3S13G4A1S13SdR6A1M5A1A3S2G3S14G5A1S14SdR7A1M6A1A3S2S0S16G6A1S16SdR8A1M7A1A3S2S0S10G7A1S10SdR9A1A1A3S2G3S12R9A1S12RaA1A3S2S0S1fG0R8A2R7A3S6Z0R8A2S4R9S7Z2R10A2A2S4S27R11A2S2S1bS15S1dG2S14SdRfA1M8A1SfG8A1A3RdRcA3S1cA3S4S53RfR11A2S5S53R10R11A2RcA2A2S4S5S25S36R15A1M9A1RdA2S25S5G9R14A2A1A2S34Vsegs;R16R14R13R12A5S34Vsegs;S55R17R16A2R15R14R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;Fnv;FA;").
Proof.
  intros A nv rho tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL HL2 HGN Hfree Hpaid Hac (HG & HR & HF & HRest & HM & HI3 & HB).
  cbn [aa_geom bumpV] in *.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|].
  split.
  { unfold rest_inv in HRest |- *. cbn [aa_geom aa_live aa_cls aa_sec aa_ptr_committed aa_q_thread aa_q_global aa_depot aa_internal_inited aa_cache_inited aa_fs_busy aa_fs_hint bumpV] in HRest |- *.
    exact HRest. }
  split; [|exact (conj HI3 HB)].
  unfold model_inv, ledger_inv in HM |- *.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpV] in HM |- *.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split.
  { destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold vm_geom. cbn [aa_geom aa_sec bumpV]. rewrite Hna, Hlz.
    split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
    - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
    - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
    - exact G9. }
  split.
  { rewrite (PrimCredit.prim_credit_same A (bumpV A nv) eq_refl).
    unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV] in V2 |- *. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 Hpaid Hac. lia. }
  split; [rewrite Hlm; exact V3|]. split; [clear -V4 HGN; unfold GN in HGN; lia|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
  split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
  split.
  { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot bumpV] in L4 |- *.
    rewrite Hrs, Hvm. destruct L4 as [N4 S4].
    pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
    pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
    split; [clear -N4 IN HGN; unfold GN in *; nia | clear -S4 IS HL2; lia]. }
  split.
  { eapply depot_vm_grow; [| exact Hlz | exact Hna | exact Htop | exact L5]. intros e He. rewrite Hvm. right. exact He. }
  split; [exact L6|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

  destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
  intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
Qed.

Lemma pendS_intro : ltac2:(tb__ "0|6|
S35S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1A1A3A3S2S0S1fG0R3A2R2A3S4Z11c01R3A2S2S0S8S1fG0R6A2S2cA2Z0M3A3S6G3S1fG0R7A2A2S4S5S1fG0R8A2R6A2S10SdRaA1A1A2S0S1S4S1fG0RaA2M4R1A2S6R1S5G4R8A2A2A2S3S1S4S2fR2A2S6R2S2eA2A2A1F_;Fx;S2S1bS15S1dG2S14SdRcA1M5A1SfG5A1A3RaR9A3S1cA3S34Vsegs;R10RfReRdA5S56R11S1fG0RcA2RaRdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md md' a n L Hvm HnL HL Hal Hpos Hceil Himg Hfree (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  destruct HM as (VG & _ & _ & _ & _ & _ & V7 & L1 & L2 & L3 & L4 & L5 & _).
  destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A)) as TGR.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (ua, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  unfold pendS. cbn zeta.
  split. { rewrite Hvm. left. unfold ua. rewrite Z_to_bv_bv_unsigned. rewrite <- HnL, Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hal|]. split; [lia|].
  split.
  { assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
    { apply band_covered_app_r. exact L2. }
    pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
    rewrite HnL in W. unfold dyn_in. rewrite TG, <- V7. unfold IMG_LO, IMG_HI, PG in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact W].
    right. destruct (Z_lt_le_dec ua 6578176) as [Hlt|Hge]; [|exact Hge]. exfalso.
    destruct (Z_lt_le_dec ua 65536) as [X|X]; [apply (Himg 65536); lia | apply (Himg ua); lia]. }
  split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
  split; [apply APT; replace (ag_spacebeg (aa_geom A) + (kSpaceSize + 4096)) with (ag_spacebeg (aa_geom A) + kSpaceSize + 4096) by lia; exact G2|].
  split; [apply APT; exact G7|].
  split.
  - intros ch Hch. destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as (D1 & D2 & D3 & _).
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
  - intros bn Hbn. destruct L5 as [DVM _ _ _ DVT DR].
    pose proof (apart_of_region_free _ a n Hfree (wentry bn) ltac:(apply in_or_app; right; exact (DVM bn Hbn))) as X.
    pose proof (DVT bn Hbn) as T. destruct HRest as (_ & _ & _ & _ & _ & HD & _).
    assert (B : IMG_HI <= fst bn /\ 0 < snd bn).
    { unfold dblocks in Hbn. apply in_app_or in Hbn as [Hb|Hb]; apply in_map_iff in Hb as (b & <- & Hb); cbn [fst snd].
      - destruct (dm_nb _ _ HD b Hb) as (_ & Y & _). unfold NBSZ. split; [exact Y | lia].
      - destruct (dm_fbases _ _ HD b Hb) as (_ & Y & _). unfold FBSZ. split; [exact Y | lia]. }
    unfold wentry, apartW in X. cbn [fst snd] in X. unfold IMG_HI in B.
    rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.
End S.

Section JGS.
Variable W : list ulink. Variable st : ustop. Variable tmax : Z.
Let segs : list Segment := segsA.

Definition JGs (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S22S18S20Q40M0A1M1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S24S58S2bVA;Vrho;A2R5A3S1S2G1S23R5S57VW;Vst;Vtmax;A3A2Va;A3S1S34Vsegs;S55VA;R1A2R5R4R2A5S1S56VA;S1fG0Va;A2S29R1A1R2A4S1VKc;R3R2A2S1S63VA;R5A2S1S64VW;Vst;R5A3S1S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S1S62VA;R5A2S4eVA;R1A2A2A2A2A2A2A2A2A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Definition SHC (nv : Z) : Z := ltac2:(tb__ "0|0|
S7S2cS5SbS29Vnv;A1S7Z8S2cA2A2Z2A2A2").
Definition JGsC (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|1|
S22S18S20Q40M0A1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S5dVA;VKc;Vrho;Va;R5R4R3R2A8S4S5S5S53R2R4A2S69VA;A1A2S5eR1A1A2S28S55VA;R1A2A1A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Lemma acost_step' : ltac2:(tb__ "0|1|
S0S0S4Z0R2A2M0G0ScS7Z4SaS25S5R4R3A2A1S25R4A1A2A2SaS7Z7R3A2Z3A2A2F_;F_;Fn;FV;").
Proof.
  intros V n HV Hn. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * (V + n) + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (V + n) + 4 - 1) 4 ltac:(lia)).
  pose proof (Z.div_mod (7 * V + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * V + 4 - 1) 4 ltac:(lia)). lia.
Qed.
Lemma acost_pays_map : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S25R4A1S29R3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS.
  assert (B : secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  lia.
Qed.

Lemma JGs_grant : ltac2:(tb__ "0|3|
S35S60S22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S61RbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S58S57VW;Vst;Vtmax;A3M2A2S1cA3S5dR14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc [Hag HJ] HMI nv Hnv HnZ Hpl Hnx.
  pose proof Hag as (Hagw & Hagl & Hagm). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & _ & _ & _ & HM & _).
  pose proof HM as (_ & _ & _ & V0 & _ & _ & V7 & L1 & _).
  destruct (grant_facts_A addr flags md len a Hpl L1) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof Hpl as (_ & _ & _ & Gfree & _).
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  assert (NEQ : forall i, (i < GW)%positive -> i <> nxS W st tmax).
  { intros i Hi E. rewrite <- E in Hnx. apply Pos.leb_le in Hnx. exact (proj1 (Pos.lt_nle _ _) Hi Hnx). }
  set (h' := mmap_rw_vm (m_vmmaps md) len a). set (rho1 := rho_set_rw rhoX (nxS W st tmax) a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB, HN. rewrite E12 in HB, HN. fold nv in HB, HN.
  assert (Hag1 : agree_below GW rhoX rho1) by (unfold rho1; apply agree_below_set_rw; apply Pos.leb_le; exact Hnx).
  pose proof Hag1 as (A1w & A1l & A1m).
  assert (SMB : 72705 <= secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  unfold JGs. fold nv. cbn zeta.
  split.
  { split; [|split].
    - intros i Hi. rewrite (Hagw i Hi). apply A1w. exact Hi.
    - intros l. rewrite (Hagl l). apply A1l.
    - intros x. rewrite (Hagm x). apply A1m. }
  split; [unfold rho1; apply rho_set_rw_at|].
  split.
  { assert (Erm : rm rho1 = rm rhoX) by reflexivity.
    unfold AInvA. rewrite Erm. fold (AInvA segs (bumpV A nv) rhoX tp (with_vmmaps h' md)).
    refine (AInvA_sec_grant A nv rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv) _ _ _ _ _ _ En ltac:(lia) ltac:(lia) ltac:(unfold GN; lia) Gfree _ _ HA);
      rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try reflexivity.
    - rewrite paid_with_vmmaps.
      pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
      rewrite En in U. lia.
    - unfold budget_ok_alloc, limit_ok_alloc in HB. apply acost_pays_map; [exact V0 | lia]. }
  split.
  { apply (pendS_intro A rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv)); try assumption. clear -SMB. lia. }
  split.
  { replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity). apply HKc. exact HK. }
  split; [unfold tp_ok in Htp |- *; unfold rho1; rewrite rho_set_rw_other by (apply NEQ; unfold GW; lia); exact Htp|].
  split; [apply (HUS rhoX rho1); [eapply agree_below_le; [|exact Hag1]; unfold GW, NF; lia | exact HU]|].
  split; [exact Hnv|].
  split; [|exact HB].
  unfold top_high in Htop |- *. unfold rho1. rewrite !rho_set_rw_other by (apply NEQ; unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma secmapsize_bounds : ltac2:(tb__ "0|1|
S0S4Zfc01R1A2S1S1S4Z12000S29R2A1M0A2S4G0S5R2Z3007A2A2A2S2S0S8G0S2cA2Z0A3A2F_;Fnv;").
Proof.
  intros nv Hn. unfold secmapsize, secneeded, round_up, PG.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
  set (r8 := (nv + 8 - 1) / 8 * 8).
  pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)).
  split; [lia|]. rewrite Z.add_mod, Z_mod_mult by lia. reflexivity.
Qed.

Lemma SHC_pays : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S5S25R4A1S29R3A1A2S5eR3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS. pose proof (secmapsize_bounds nv Hn) as [B _].
  unfold SHC, PG. pose proof (Z.div_mod (secmapsize nv) (8 * 4096) ltac:(lia)). pose proof (Z.mod_pos_bound (secmapsize nv) (8 * 4096) ltac:(lia)). lia.
Qed.

Lemma JGsC_grant : ltac2:(tb__ "0|3|
S35S60S22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S61RbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S58S57VW;Vst;Vtmax;A3M2A2S1cA3S5fR14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI nv Hnv HnZ Hpl Hnx.
  split; [exact (JGs_grant A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI Hnv HnZ Hpl Hnx)|].
  destruct HJG as [Hag HJ]. pose proof Hag as (Hagw & _ & _). destruct HJ as (HA & _ & _ & _ & HB & _).
  pose proof HA as (_ & _ & _ & _ & HM & _). pose proof HM as (_ & V2 & _ & V0 & _ & _ & V7 & L1 & _).
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  set (h' := mmap_rw_vm (m_vmmaps md) len a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  rewrite paid_with_vmmaps.
  pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
  rewrite En in U.
  pose proof (SHC_pays (aa_V A) nv V0 ltac:(lia)) as SP.
  unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV]. fold nv. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 U SP. lia.
Qed.
End JGS.
End CSecOKInv.

(* [comment removed for export] *)
Module SpineCallocS1iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "Wcan"; "AE_A"; "Pre_callocI"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "prod"; "nil"; "app"; "option"; "pair"; "Some"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sprop_below"; "SLit"; "SVar"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "P0c"; "F_hi_p"; "F_lo_p"; "E_s1"; "stop_le"; "stop_pc"; "E_pre"; "s1_cuts_pcs"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "FACTSe"; "F_hi_e"; "F_lo_e"; "P0e"; "sa_c"; "sb_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "s_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1"; "dp_okb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wa_c : ltac2:(tb__ "0|0|
SfS4S13S2dS1U1A1S0A2A1S6A3"). Proof. MemoFast.vmc. Qed.
Lemma Da_c : ltac2:(tb__ "0|5|
SfSbS8S7S8S12S12A2M0A1M1S7S11A1M2A2M3A1S26S18S3S2S1U1A1M4S0A3A1S2dG4S0A2A2SdG3ScG1G2S5G0ScS12S12S16P18A1S15S31A1A4S9G0A1A3S9S11A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma Wb_c : ltac2:(tb__ "0|0|
SfS4S13S2eS1U1A1S0A2A1S6A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbh_c : ltac2:(tb__ "0|0|
SfS4S24S11S14S28A1SaS11S29S1U1A1S0A2S2aA3A3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbl_c : ltac2:(tb__ "0|0|
SfS4S24S11S14S28A1SaS11S29S1U1A1S0A2S2bA3A3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTh_c : ltac2:(tb__ "0|1|
SfS4S1aS2cS1U1A1M0S0S2aA3S1bG0S0S1cA3S2fA3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTl_c : ltac2:(tb__ "0|1|
SfS4S1aS2cS1U1A1M0S0S2bA3S1bG0S0S1dA3S2fA3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma WE1_c : ltac2:(tb__ "0|0|
S27S10S25Z0R1A2S25R1Z8A2A2SfS4S13S18S1eS1U1A1S0Z3R2A4A1A1S6A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DE1_c : ltac2:(tb__ "0|5|
S27S10S25Z0R1A2S25R1Z8A2A2SfS4SbS8S7S8S12S12A2A1M0S7S11A1M1A2M2A1S4Lx;S26S18S21S1U1A1M3S0Z3M4R2A4A1S18S1eG3S0G4R2A4A1A2G2G2S4Lp;R1G0G1S32R5R2A2Ll;Ld;X8x1Lp;SeXbx2S6A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HSW_c : stopJ_sw (Wcan 1) UStopLeOrPc. Proof. exact stopJ_sw_1pc. Qed.
Lemma HUS_c : stopJ_stable (Wcan 1) UStopLeOrPc. Proof. exact stopJ_stable_1pc. Qed.
Lemma Est_c : UStopLeOrPc = UStopLeOrPc. Proof. reflexivity. Qed.
Lemma HWne_c : Wcan 1 <> []. Proof. discriminate. Qed.
Lemma WPC_c : ltac2:(tb__ "0|3|
S7S11A1M0G0S23G0R2S5G0S1cS5G0S1dS9G0A1M1A3A3A3S23G0R2S5G0S20S1U1A1M2A1S5G0S1fG2A1G1A3A3A3SfS4S13S18S1bG2S0SaS11R4R3A3A3A1A1S6A3F_;F_;Fsx;Ffx;").
Proof. intros fx sx Hf Hs. destruct Hf as [<-|[<-|[]]]; destruct Hs as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DPC_c : ltac2:(tb__ "0|6|
S7S11A1M0G0S23G0R2S5G0S1cS5G0S1dS9G0A1M1A3A3A3S23G0R2S5G0S20S1U1A1M2A1S5G0S1fG2A1G1A3A3A3SfSbS8S7S8S12S12A2M3A1M4G0A2M5A1S26S18S1bG2S0R4A3A1S18S1bG2S0SaS11R4R3A3A3A1A2SdG5ScG4G0S9G3A1R3A4A2A3F_;F_;Fsx;Ffx;").
Proof. intros fx sx Hf Hs. destruct Hf as [<-|[<-|[]]]; destruct Hs as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXpc_c : ltac2:(tb__ "0|0|
S19S23S19R1S22U1S0A2A3S33S30S17S18R2A1A1A2F_;Fc;").
Proof. intros c Hc. apply Pos.leb_le. unfold s1_cuts_pcs in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End SpineCallocS1iW1.

(* [comment removed for export] *)
Module CertCallocSN.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "list"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "ss_objs"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN.W"; "NOBJ"; "stKn"; "stRn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ESn"; "V_NCH"; "V_NRES"; "V_PAB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "kPtrArrayReserve"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_null"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN"; "C_seci"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "stack_win"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymCall SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N_secn : list carve_spec := ltac2:(tb__ "0|11|
S1S3S3S3S9S8A2M0S8A2M1S5S3S3S8S2A2M2S9A2M3A1M4A2M5S0G1G4S0G0S8S0S9S8SaZ0A1M6S17A4S18S17Z40A2M7A4S1G3S0G2S9S0S8S2S17U8M8A4SaS24A1A4S1G3S0G2S9S0S8S2S18S17Z8A2G8A4SbS23A1M9A4S1G3S0G2S9S0S8S2S18S17Z10A2G8A4G9A4S1G3S0G2S9S0S8S2S18S17Z18A2G8A4SaS25A1A4S1G3S0G2S9S0S8S2S18S17Z30A2G8A4SbS22A1A4S1G3S0G2S9S0S8S2S18S17Z38A2G8A4SbS21A1A4S4G3A1MaA3A3A3A3A3A3A4S1G5S0G1G4S0G0S8S0S9S8G6G7A4Zee040MbA4GaA4S1G5S0G1G4S0G0S8S0S9S8G6GbA4Zee044A4S1G3S0G2S9S0S8S2GbU4McA4G6A4GaA3A4S1G5S0G1G4S0G0S8S0S9S8G6Zee048A4Zee070A4GaA4S1G5S0G1G4S0G0S8S0S9S8G6Ze9b28MdA4Ze9b30A4S1G3S0G2S9S0S8S2GdG8A4SaZ1a36fA1A4GaA3A4S1G5S0G1G4S0G0S8S0S9S8G6Z173660MeA4Z173662A4S1G3S0G2S9S0S8S2GeU1MfA4SaZ1A1M10A4S1G3S0G2S9S0S8S2Z173661GfA4G10A4GaA3A3A4S1G5S0G1G4S0G0S8S0S9S8G6S1cA4S18S1cZ4A2A4S1G3S0G2S9S0S8S2S1cGcA4SaZcA1A4GaA3A4S1G5S0G1G4S0G0S8S0S9S8S2eZad0A4Zc60A4GaA4S4G5A1A3A3A3A3A3A3A3A3").

Definition N_secc : list carve_spec := ltac2:(tb__ "0|a|
S1S3S3S3S9S8A2M0S8A2M1S5S3S3S8S2A2M2S9A2M3A1M4A2M5S0G1G4S0G0S8S0S9S8SaZ0A1M6Zee040M7A4Zee044A4S1G3S0G2S9S0S8S2G7U4A4G6A4S4G3A1M8A3A4S1G5S0G1G4S0G0S8S0S9S8G6Ze9b28M9A4Ze9b30A4S1G3S0G2S9S0S8S2G9U8A4SaZ1a36fA1A4G8A3A4S4G5A1A3A3").
Definition C_seci : list (Z * nat * sv) := ltac2:(tb__ "0|4|
S1S3S3S8S2A2M0S9A2M1S0G0S9S0S8S2S17U8M2A4SaS24A1A4S1G1S0G0S9S0S8S2S18S17Z8A2G2A4SbS23A1M3A4S1G1S0G0S9S0S8S2S18S17Z10A2G2A4G3A4S1G1S0G0S9S0S8S2S18S17Z18A2G2A4SaS25A1A4S1G1S0G0S9S0S8S2S18S17Z30A2G2A4SbS22A1A4S1G1S0G0S9S0S8S2S18S17Z38A2G2A4SbS21A1A4S4G1A1A3A3A3A3A3A3").
Definition K_seci : carve_spec := ltac2:(tb__ "0|1|
S0S3S3S9S8A2M0S8A2S5S3S3S8S2A2S9A2A1S0G0S8S0S9S8SaZ0A1S17A4S18S17Z40A2A4S2dA4").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.

Definition NOBJ : nat := ltac2:(tb__ "0|0|
S7ScS1ScS30S6ScS31VW;A1S2fA3A3A2").

Definition stKn : axst := ltac2:(tb__ "0|1|
S20VW;Vst;Vtmax;A3S1bS1aR1S2bS19R1A1M0S26ScS1dSdG0A1A3A2A2TE;").

Definition stRn_S : sstate := ltac2:(tb__ "0|2|
SeS14S19S1eA1M0A1S29S15G0A1S1S3S2S9A2M1S0S2S9U4SbP18A1A4S4G1A1A3A2S11G0A1S10G0A1S16G0A1SdG0A1SfG0A1S13G0A1S12G0A1A9").
Definition stRn : axst := ax_setS stKn stRn_S.

Definition s_n : wsub := ltac2:(tb__ "0|0|
S2aS28S19S1fA1S19S2cVW;Vst;A2A1A3").

Definition R_n : list sobj := ltac2:(tb__ "0|0|
S27ScS1dSdS19S20VW;Vst;Vtmax;A3A1A1A3").
End W.
End CertCallocSN.

(* [comment removed for export] *)
Module SpineCallocS2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "ss_facts"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sobj"; "swf"; "SPNot"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "list"; "pair"; "prod"; "true"; "cons"; "nat"; "Some"; "false"; "option"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E2a"; "E2b"; "V_CLS"; "creg_a"; "creg_b"; "F_gen"; "V_ND"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2.S2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@Corelib.Numbers.BinNums"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@Stdlib.Lists.List"; "In"; "incl"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Notation only_var := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.only_var.
Notation rho_one := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.rho_one.
Notation eval_only_var := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.eval_only_var.
Notation zseq8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.zseq8.
Notation in_zseq8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.in_zseq8.
Notation tab_ok := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.tab_ok.
Notation tab_ok_sound := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.tab_ok_sound.

Section S2.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VW;Vst;VA;VKc;S4PcA1A6").

Hypothesis OVa : ltac2:(tb__ "0|0|
S18SeS31P9dS1cVW;Vst;Vtmax;A3A2S12A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S18SeS31P9dS1dVW;Vst;Vtmax;A3A2S12A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S18SeS32P9dS1cVW;Vst;Vtmax;A3S2dZ208S36S37S25S26S27S25S28A1A1A1A1A1A1A5S12A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S18SeS32P9dS1dVW;Vst;Vtmax;A3S2dZ18U3eA5S12A3").

Definition E2a' : axst := ltac2:(tb__ "0|1|
S20VW;Vst;Vtmax;S19VW;Vst;Vtmax;A3Z40bacS13S11S14S2A2M0S10S14S2U8S4S1bA1A4SdG0A1A3SdSaA1S16SdS3A1A9").
Definition E2b' : axst := ltac2:(tb__ "0|1|
S20VW;Vst;Vtmax;S1aVW;Vst;Vtmax;A3Z40bacS13S11S14S2A2M0S10S14S2U8S4S1bA1A4SdG0A1A3SdSaA1S16SdS3A1A9").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S18SeSbS0S22A1A1S12A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S18SeSbS0S23A1A1S12A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S18S17S11SfS11S2S2A2M0A1M1SfS3A1M2A2M3A1S2cS0S19VW;Vst;Vtmax;A3A1S0S22A1A2S15G3S10G1G2S13G0S10S2S2S1cVW;Vst;Vtmax;A3S4S1bA1A4SdG0A1A3SdS3A1A4A2A3").

Hypothesis NXa : ltac2:(tb__ "0|0|
S18S29S6S0S22A1A1S6S0S19VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S18S29S6S0S23A1A1S6S0S1aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S18S17S11SfS11S2S2A2M0A1M1SfS3A1M2A2M3A1S2cS0S1aVW;Vst;Vtmax;A3A1S0S23A1A2S15G3S10G1G2S13G0S10S2S2S1dVW;Vst;Vtmax;A3S4S1bA1A4SdG0A1A3SdS3A1A4A2A3").

Hypothesis Fa : ltac2:(tb__ "0|0|
S33S3S9S2aS8Z200A1S4S1fA1A3S5S0S19VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S33S3ScS9S2aS8Z200A1S4S1fA1A3A1S5S0S1aVW;Vst;Vtmax;A3A1A1A3").

Hypothesis Ga : ltac2:(tb__ "0|0|
S34S3S1eS5S0S19VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S34S3S1eS5S0S1aVW;Vst;Vtmax;A3A1A1A3").

Lemma class_restate_a : ltac2:(tb__ "0|1|
S30S2eS7SfS35Q40A1A1S2bS7S21Vsegs;S24VW;Vst;R6R5R4A5S19VW;Vst;Vtmax;A3M0R1R3R2A6S21Vsegs;S24VW;Vst;R7R6R5A5S1G0S0S22A1A2R2R4R3A6F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE H. pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *.
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ Fa) as F1. cbn [holds eval V_ND] in F1. unfold V_ND in F1. rewrite E157 in F1.
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto). cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3.
  rewrite bt_ltu_lit in F1 by lia. apply Z.ltb_lt in F1. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia.
  eapply SPA_restate; [exact Wa' | exact Da' | exact NXa | | constructor | exact H].
  constructor; [|constructor]. cbn [fst snd]. cbn [eval]. unfold V_CLS. rewrite E158.
  rewrite (tab_ok_sound 157 _ ClassID 520 8128%nat rhoE (needed8 nv) TABa OVa E157); [unfold cls_of; reflexivity | cbn; lia |].
  replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Lemma class_restate_b : ltac2:(tb__ "0|1|
S30S2eS7SfS35Q40A1A1S2bS7S21Vsegs;S24VW;Vst;R6R5R4A5S1aVW;Vst;Vtmax;A3M0R1R3R2A6S21Vsegs;S24VW;Vst;R7R6R5A5S1G0S0S23A1A2R2R4R3A6F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE H. pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *.
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ Fb) as F1. cbn [holds eval V_ND] in F1. unfold V_ND in F1. rewrite E157 in F1.
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto). cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3.
  unfold not in F1. rewrite bt_ltu_lit in F1 by lia. rewrite Z.ltb_lt in F1. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia.
  eapply SPA_restate; [exact Wb' | exact Db' | exact NXb | | constructor | exact H].
  constructor; [|constructor]. cbn [fst snd]. cbn [eval]. unfold V_CLS. rewrite E158.
  rewrite (tab_ok_sound 157 _ ClassID 24 62%nat rhoE (needed8 nv) TABb OVb E157); [unfold cls_of; reflexivity | cbn; lia |].
  replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.
End S2.
End SpineCallocS2.

(* [comment removed for export] *)
Module SpineMallocS3c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_facts"; "ss_next"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E2a"; "E2b"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "C1g"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "E2a'"; "E2b'"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "ulink"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SPINE2C.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S53S5cVsegs;A1VW;Vst;VA;VKc;S15PcA1A6").
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let Xa : axst := ltac2:(tb__ "0|0|
S4S1dVW;Vst;Vtmax;A3S1S2eVnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S4S1eVW;Vst;Vtmax;A3S1S2fVnW;Vst;Vtmax;A3A1A2").

Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S5S5bS5dUfa0S8S3cZ40bacSbS3cA1A3S2bS8S2S24VW;Vst;Vtmax;A3SbS2A1M0A3S8S2S1dVW;Vst;Vtmax;A3S8S2S1eVW;Vst;Vtmax;A3G0A3A3A6S6A3").

Hypothesis OVa : ltac2:(tb__ "0|0|
S0S5S30P9dS22VW;Vst;Vtmax;A3A2S6A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S5S30P9dS23VW;Vst;Vtmax;A3A2S6A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S5S31P9dS22VW;Vst;Vtmax;A3S4cZ208S59S5aS43S44S45S43S46A1A1A1A1A1A1A5S6A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S5S31P9dS23VW;Vst;Vtmax;A3S4cZ18U3eA5S6A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S5S11S1S2eVnW;Vst;Vtmax;A3A1A1S6A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S5S11S1S2fVnW;Vst;Vtmax;A3A1A1S6A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SeSaS9SaS10S10A2M0A1M1S9SfA1M2A2M3A1S48S1S1dVW;Vst;Vtmax;A3A1S1S2eVnW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS10S10S22VW;Vst;Vtmax;A3S15S26A1A4SbG0A1A3SbSfA1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SeSaS9SaS10S10A2M0A1M1S9SfA1M2A2M3A1S48S1S1eVW;Vst;Vtmax;A3A1S1S2fVnW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS10S10S23VW;Vst;Vtmax;A3S15S26A1A4SbG0A1A3SbSfA1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S3dS14S1S2eVnW;Vst;Vtmax;A3A1A1S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S3dS14S1S2fVnW;Vst;Vtmax;A3A1A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S3aSfS18S47S17Z200A1S15S27A1A3S13S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S3aSfS1bS18S47S17Z200A1S15S27A1A3A1S13S1S1eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S39SfS1fS13S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S39SfS1fS13S1S1eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis SKa : ltac2:(tb__ "0|1|
S0S9SaSaS10S10A2S10A2M0A1S2cS12G0S34S1aS1VXa;A1A1A4S2cS12G0S34S7S12S8S12S4bS7S12S52VW;A1S4dA3A3S4aA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0S9SaSaS10S10A2S10A2M0A1S2cS12G0S34S1aS1VXb;A1A1A4S2cS12G0S34S7S12S8S12S4bS7S12S52VW;A1S4dA3A3S4aA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S39SfS7SfS7SfS7SfS51VW;Vst;A2S4fS4eA1A3S49A3S1fA3S13S1VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S39SfS7SfS7SfS7SfS51VW;Vst;A2S4fS4eA1A3S49A3S1fA3S13S1VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S5S11S1S35VXa;A1A1A1S6A3").   Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S5S11S1S36VXa;A1A1A1S6A3").  Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S5S11S1S37VXa;A1A1A1S6A3").  Hypothesis W2a : ltac2:(tb__ "0|0|
S0S5S11S1S32VXa;A1A1A1S6A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S5S11S1S38VXa;A1A1A1S6A3"). Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S5S11S1S33VXa;A1A1A1S6A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S5S11S1S35VXb;A1A1A1S6A3").   Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S5S11S1S36VXb;A1A1A1S6A3").  Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S5S11S1S37VXb;A1A1A1S6A3").  Hypothesis W2b : ltac2:(tb__ "0|0|
S0S5S11S1S32VXb;A1A1A1S6A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S5S11S1S38VXb;A1A1A1S6A3"). Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S5S11S1S33VXb;A1A1A1S6A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S5S3S32VXa;A1S20VW;Vst;Vtmax;A3Vsa;A3S6A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S5S3S33VXa;A1S21VW;Vst;Vtmax;A3Vsra;A3S6A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S5S3S32VXb;A1S20VW;Vst;Vtmax;A3Vsb;A3S6A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S5S3S33VXb;A1S21VW;Vst;Vtmax;A3Vsrb;A3S6A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S5S2dVsa;S2bA2S6A3").   Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S5S2dVsra;S2bA2S6A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S5S2dVsb;S2bA2S6A3").   Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S5S2dVsrb;S2bA2S6A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S5S3bSfS19S14S1S20VW;Vst;Vtmax;A3A1A1A1S7SfS25S2aA3A3S6A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S5S3bSfS19S14S1S21VW;Vst;Vtmax;A3A1A1A1S25A3S6A3").

Theorem spine_s2c : ltac2:(tb__ "0|2|
S40OF_;S5eS54S16S9S61Q40M0A1A1S3fS0S57Vst;S56A3S0S9S50A1VW;SbS50A1A3F_;S60VW;Vst;A2S55R6A1S42Vsegs;R9VJ;VW;Vst;R8R7A4A3S16S3eVsegs;RbS41Vsegs;S58VW;Vst;RaR9R8A5S28VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;S0S3cS5fRaS62G0S1cR8PcA2A2A2Z0A3S16S3eVsegs;RdS41Vsegs;S58VW;Vst;RcRbRaA5M1S29VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;S16S3eVsegs;RdS41Vsegs;G1S24VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HW HUS HKc Hokf HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (cfg_soundA segs 4000%nat [0x40bac] GW [C1g W st tmax] [E2a W st tmax; E2b W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert2.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End SPINE2C.
End SpineMallocS3c.

