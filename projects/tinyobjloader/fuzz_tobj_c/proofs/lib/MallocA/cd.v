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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.

(* [comment removed for export] *)
Module SpineMallocRu0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "valuation"; "rw"; "swf"; "ss_facts"; "ss_lenient"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "axst"; "leafA"; "sym_runA"; "ax_X"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "false"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cd.SpineMallocRu0"; "r_u1_0"; "r_u2_0"; "e3u"; "cellsf_u"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocRi0"; "W0"; "e3r"; "FUEL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocU1"; "cU0"; "cU1"; "kU1"; "kU2"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5"; "posts_conv"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocU1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.SpineMallocU2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocRi0.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_u1__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5").
Local Strategy expand [R_u1__R].
Definition r_u1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_u1__R).
Definition r_u1_0 := Eval vm_compute in (nth 0 r_u1 (mkLeafA (cU0 e3r) RsCut)).
Definition cu1 := Eval vm_compute in (cU1 (la_state r_u1_0)).
Definition r_u2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41260] cu1 true with Some l => l | None => [] end).
Definition r_u2_0 := Eval vm_compute in (nth 0 r_u2 (mkLeafA cu1 RsCut)).
Definition cellsf_u := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (la_state r_u2_0))) O_pcc0)).
Definition e3u := Eval vm_compute in (eU (la_state r_u2_0)).
Lemma E3u_eq : ltac2:(tb__ "0|0|
S0ScS2cSaS1bA1A1S1cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma WU0 : ltac2:(tb__ "0|0|
S0S10S6SbS24S22A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u1 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5S18G0S14SdS1aS13SdA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_u1__R <: R_u1__R = Some [r_u1_0]). Qed.
Lemma LN_u1 : ltac2:(tb__ "0|0|
S0S10S8SbS24S22A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u1 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS24S22A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM1 : ltac2:(tb__ "0|1|
S0S10S29S32SaS1aA1M0A1S2dG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_s1 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbS2fSaS1aA1M0A1A1A1M1S16S1S31S1S38S32G0A1U2A2G1A3S14S1S3fS14S1S2bS13S1A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_k1 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS26SaS1aA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k1b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS26SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k1 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS26SaS1aA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c1 : ltac2:(tb__ "0|0|
S0S10S6SbS25SaS1aA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u2 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ41260S13S1eA1A3S25SaS1aA1A1S11A5S18G0S14SdS1bS13SdA1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_u2 : ltac2:(tb__ "0|0|
S0S10S8SbS25SaS1aA1A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u2 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS25SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_u2 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbSaS1bA1M0A1A1M1S16S1S31S1S38S32G0A1U1A2G1A3S14S1S2aS1dA1S13S1A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ARR_ok : arr_okb cellsf_u = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_k2 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS27SaS1bA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k2b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS27SaS1bA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k2 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS27SaS1bA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c2 : ltac2:(tb__ "0|0|
S0S10S6SbS28SaS1bA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM2 : ltac2:(tb__ "0|1|
S0S10S29S32S28SaS1bA1A1M0A1S2eG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_uninit_i : ltac2:(tb__ "0|4|
S12S15S1eS1eA2A1M0G0S48R2A1S49R2A1S40S34S12S15ScS3dA2A1F_;F_;S4bR5R4R1A3ScScS0ScR2S22A3S0ScR2S1cA3S40S34S4S12S4cQ40M1A1M2A1S39S39OF_;F_;S47R4R1A2S35R5A1S0S10S41R7A1S17A3S0S1eS4aR8S4dG1S5R6PcA2A2A2Z0A3S4S4S0S1fG2F_;S5R2A1S5R9A1A3R8S3bS20S44S21S33S46RcA1M3RbR3A5RfR2R9A5S3cS20S3aR3R9R12G3RbA2A5A2F_;FrX;Frho1;S4R7S3bS20S44S21S33RbRaR9A5RfR1R8A5S3cS20S3aR9R8R11RbRaA2A5A2FrhoE;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3U;FE3;FHPF;FPFam;FHXGL;FHCST;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL PFam HPF E3 E3U -> ->. rewrite <- E3u_eq.
  intros A Kc rho tp TR KIT HKc Hini Hcnt HCONT.
  exact (refill_uninit CST XGL HCST HXGL PFam HPF 0 UStopLe FUEL e3r r_u1_0 r_u2_0 cellsf_u SK3 XX3 (inclb_incl _ _ XF3b) WU0 R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 (inclb_incl _ _ XF_k1b) XX_k1 W_c1
           R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 (inclb_incl _ _ XF_k2b) XX_k2 W_c2 PERM2 A Kc rho tp TR KIT HKc HW0 Hini Hcnt HCONT).
Qed.
End SpineMallocRu0.

(* [comment removed for export] *)
Module SpineMallocRu2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "valuation"; "rw"; "swf"; "ss_facts"; "ss_lenient"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "axst"; "leafA"; "sym_runA"; "ax_X"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "false"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cd.SpineMallocRu2"; "r_u1_0"; "r_u2_0"; "e3u"; "cellsf_u"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocRi2"; "W0"; "e3r"; "FUEL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocU1"; "cU0"; "cU1"; "kU1"; "kU2"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5"; "posts_conv"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocU1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.SpineMallocU2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocRi2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_u1__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5").
Local Strategy expand [R_u1__R].
Definition r_u1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_u1__R).
Definition r_u1_0 := Eval vm_compute in (nth 0 r_u1 (mkLeafA (cU0 e3r) RsCut)).
Definition cu1 := Eval vm_compute in (cU1 (la_state r_u1_0)).
Definition r_u2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41260] cu1 true with Some l => l | None => [] end).
Definition r_u2_0 := Eval vm_compute in (nth 0 r_u2 (mkLeafA cu1 RsCut)).
Definition cellsf_u := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (la_state r_u2_0))) O_pcc0)).
Definition e3u := Eval vm_compute in (eU (la_state r_u2_0)).
Lemma E3u_eq : ltac2:(tb__ "0|0|
S0ScS2cSaS1bA1A1S1cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma WU0 : ltac2:(tb__ "0|0|
S0S10S6SbS24S22A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u1 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5S18G0S14SdS1aS13SdA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_u1__R <: R_u1__R = Some [r_u1_0]). Qed.
Lemma LN_u1 : ltac2:(tb__ "0|0|
S0S10S8SbS24S22A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u1 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS24S22A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM1 : ltac2:(tb__ "0|1|
S0S10S29S32SaS1aA1M0A1S2dG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_s1 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbS2fSaS1aA1M0A1A1A1M1S16S1S31S1S38S32G0A1U2A2G1A3S14S1S3fS14S1S2bS13S1A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_k1 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS26SaS1aA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k1b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS26SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k1 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS26SaS1aA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c1 : ltac2:(tb__ "0|0|
S0S10S6SbS25SaS1aA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u2 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ41260S13S1eA1A3S25SaS1aA1A1S11A5S18G0S14SdS1bS13SdA1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_u2 : ltac2:(tb__ "0|0|
S0S10S8SbS25SaS1aA1A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u2 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS25SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_u2 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbSaS1bA1M0A1A1M1S16S1S31S1S38S32G0A1U1A2G1A3S14S1S2aS1dA1S13S1A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ARR_ok : arr_okb cellsf_u = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_k2 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS27SaS1bA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k2b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS27SaS1bA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k2 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS27SaS1bA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c2 : ltac2:(tb__ "0|0|
S0S10S6SbS28SaS1bA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM2 : ltac2:(tb__ "0|1|
S0S10S29S32S28SaS1bA1A1M0A1S2eG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_uninit_i : ltac2:(tb__ "0|4|
S12S15S1eS1eA2A1M0G0S48R2A1S49R2A1S40S34S12S15ScS3dA2A1F_;F_;S4bR5R4R1A3ScScS0ScR2S22A3S0ScR2S1cA3S40S34S4S12S4cQ40M1A1M2A1S39S39OF_;F_;S47R4R1A2S35R5A1S0S10S41R7A1S17A3S0S1eS4aR8S4dG1S5R6PcA2A2A2Z0A3S4S4S0S1fG2F_;S5R2A1S5R9A1A3R8S3bS20S44S21S33S46RcA1M3RbR3A5RfR2R9A5S3cS20S3aR3R9R12G3RbA2A5A2F_;FrX;Frho1;S4R7S3bS20S44S21S33RbRaR9A5RfR1R8A5S3cS20S3aR9R8R11RbRaA2A5A2FrhoE;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3U;FE3;FHPF;FPFam;FHXGL;FHCST;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL PFam HPF E3 E3U -> ->. rewrite <- E3u_eq.
  intros A Kc rho tp TR KIT HKc Hini Hcnt HCONT.
  exact (refill_uninit CST XGL HCST HXGL PFam HPF 2 UStopLe FUEL e3r r_u1_0 r_u2_0 cellsf_u SK3 XX3 (inclb_incl _ _ XF3b) WU0 R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 (inclb_incl _ _ XF_k1b) XX_k1 W_c1
           R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 (inclb_incl _ _ XF_k2b) XX_k2 W_c2 PERM2 A Kc rho tp TR KIT HKc HW0 Hini Hcnt HCONT).
Qed.
End SpineMallocRu2.

