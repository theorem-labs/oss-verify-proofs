(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_071.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ce cb.

(* [comment removed for export] *)
Module DrainIg3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg3"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 3.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_3 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg3.

(* [comment removed for export] *)
Module DrainIg4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg4"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 4.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_4 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg4.

(* [comment removed for export] *)
Module DrainIg5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg5"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 5.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_5 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg5.

(* [comment removed for export] *)
Module DrainIg6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg6"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 6.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_6 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg6.

(* [comment removed for export] *)
Module DrainIg8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg8"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 8.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_8 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg8.

(* [comment removed for export] *)
Module DrainCG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC"; "DRAIN_NS"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "pair"; "prod"; "true"; "@Corelib.Init.Logic"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "JD"; "JLD"; "NXD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "drain_contract_g"; "drain_contract_gE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ce.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cb.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Theorem drain_g_all : ltac2:(tb__ "0|1|
S0S7S0R1S6A3S1aS1S1OF_;F_;S19R2R1A2S1bR3A1S1cS0SfS9S1fQ40A1A1S1eS1dR4A1S11A2R8S10S5S12RbSdR5R9R4A5S16RbA1R3R2A5S4S5S14R3R2S8ScS2S3A2M0SbS2S3S15RbA1S13R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;F_;Fn;").
Proof.
  intros n Hn. unfold DRAIN_NS in Hn. cbn [In] in Hn.
  destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.DrainIg1.drain_g_1 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.DrainIg2.drain_g_2 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg3.drain_g_3 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg4.drain_g_4 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg5.drain_g_5 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg6.drain_g_6 | exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainIg8.drain_g_8].
Qed.

Theorem drain_contract_g_all : ltac2:(tb__ "0|0|
S0S7S0R1S6A3SeS17R2A1S18R2A1A2F_;Fn;").
Proof.
  intros n Hn. split.
  - intros ok A Kc c rho tp HKc H1 H2 HB. exact (drain_g_all n Hn Kc (triple segs ok) (TRokD_triple Kc ok H1 H2) HKc A c rho tp HB).
  - intros A Kc c rho tp HKc HB. exact (drain_g_all n Hn Kc (etriple segs) (TRokD_etriple Kc) HKc A c rho tp HB).
Qed.
End DrainCG.

