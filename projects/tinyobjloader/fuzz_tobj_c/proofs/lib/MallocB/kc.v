(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.

(* [comment removed for export] *)
Module DrainI3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI3"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 3.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_3 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI3.

(* [comment removed for export] *)
Module DrainI4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI4"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 4.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_4 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI4.

(* [comment removed for export] *)
Module DrainI5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI5"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 5.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_5 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI5.

(* [comment removed for export] *)
Module DrainI6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI6"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 6.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_6 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI6.

(* [comment removed for export] *)
Module DrainI8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI8"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 8.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_8 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI8.

(* [comment removed for export] *)
Module DrainC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "false"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC"; "DRAIN_NS"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "JD"; "JLD"; "L_dh_f"; "NXD"; "Pre_dh_f"; "drain_contract_f"; "drain_contract_fE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition DRAIN_NS : list Z := ltac2:(tb__ "0|0|
S1S0Z1S1S0Z2S1S0Z3S1S0Z4S1S0Z5S1S0Z6S1S0Z8S2S0A1A3A3A3A3A3A3A3").
Lemma kchunks_cases : ltac2:(tb__ "0|0|
S0S9SfZ1R1A2SfR1Z1eA2A2S8S0S1dR2A1S7A3F_;Fc;").
Proof.
  intros c Hc. assert (H : forallb (fun c => existsb (Z.eqb (kchunks c)) DRAIN_NS) CLS30 = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) H c (proj2 (In_CLS30 c) Hc)) as X. apply existsb_exists in X as (k & Hk & E). apply Z.eqb_eq in E. rewrite E. exact Hk.
Qed.

Theorem drain_f_all : ltac2:(tb__ "0|1|
S0S8S0R1S7A3S1aSaSaOF_;F_;S19R2R1A2S1bR3A1S1cS0S10S4S1eQ40A1A1R7S11SeS12RaS3R4R8R3A5S16RaA1R2R1A5SdSeS15R2R1S1S6SbScA2M0S5SbScS14RaA1S13R4R8R3A3A4S2G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;F_;Fn;").
Proof.
  intros n Hn. unfold DRAIN_NS in Hn. cbn [In] in Hn.
  destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainI1.drain_f_1 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainI2.drain_f_2 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI3.drain_f_3 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI4.drain_f_4 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI5.drain_f_5 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI6.drain_f_6 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainI8.drain_f_8].
Qed.

Theorem drain_contract_f_all : ltac2:(tb__ "0|0|
S0S8S0R1S7A3S9S17R2A1S18R2A1A2F_;Fn;").
Proof.
  intros n Hn. split.
  - intros ok A Kc c rho tp HKc H1 H2. exact (drain_f_all n Hn Kc (triple segs ok) (TRokD_triple Kc ok H1 H2) HKc A c rho tp).
  - intros A Kc c rho tp HKc. exact (drain_f_all n Hn Kc (etriple segs) (TRokD_etriple Kc) HKc A c rho tp).
Qed.
End DrainC.

