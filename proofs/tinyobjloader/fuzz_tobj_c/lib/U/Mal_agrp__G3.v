(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "list"; "prod"; "option"; "pair"; "None"; "false"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "SLit"; "sprop"; "cell"; "mkCell"; "SPUle"; "sobj"; "mkObj"; "SAlu"; "DUnknown"; "SPAlign"; "DRom"; "SPBranch"; "SPNot"; "sstate"; "FcsrFrm0"; "mkSS"; "DZero"; "ss_facts"; "SExt"; "sprop_eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_EQ"; "ALU_SLL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sym_run"; "leaf"; "lf_state"; "stop_reason"; "RsFuel"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "CUTS_K"; "segs"; "lfs"; "SK_a"; "SK_b"; "SK_c"; "SK_d"; "ST_a"; "ST_b"; "ST_c"; "ST_d"; "SV_a"; "SV_b"; "SV_c"; "SV_d"; "SF0_a"; "SF0_b"; "SF0_c"; "SF0_d"; "SW_a"; "SW_b"; "SW_c"; "SW_d"; "LK_a"; "LK_b"; "LK_c"; "LK_d"; "LT_a"; "LT_b"; "LT_c"; "LT_d"; "LV_a"; "LV_b"; "LV_c"; "LV_d"; "RF0_a"; "RF0_b"; "RF0_c"; "RF0_d"; "RK_a"; "RK_b"; "RK_c"; "RK_d"; "RT_a"; "RT_b"; "RT_c"; "RT_d"; "RV_a"; "RV_b"; "RV_c"; "RV_d"; "RW_a"; "RW_b"; "RW_c"; "RW_d"; "@Corelib.Init.Logic"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rN5"; "CUTS_N"; "segs"; "SN_10_10_L"; "SN_10_10_Z"; "SN_11_2_L"; "SN_11_2_Z"; "SN_11_4_L"; "SN_11_4_Z"; "SN_11_8_L"; "SN_11_8_Z"; "SN_12_7_L"; "SN_12_7_Z"; "RN_10_10_L"; "RN_10_10_Z"; "RN_11_2_L"; "RN_11_2_Z"; "RN_11_4_L"; "RN_11_4_Z"; "RN_11_8_L"; "RN_11_8_Z"; "RN_12_7_L"; "RN_12_7_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "sh"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rN7"; "CUTS_N"; "segs"; "SN_17_3_L"; "SN_17_3_Z"; "SN_19_2_L"; "SN_19_2_Z"; "RN_17_3_L"; "RN_17_3_Z"; "RN_19_2_L"; "RN_19_2_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "SJ3"; "mkSKF"; "mkSKT"; "mkSKV"; "mkSKW"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.Lists.List"; "existsb"; "filter"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "M1a"; "M1b"; "M1c"; "M1d"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_rK.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS_K : list Z := ltac2:(tb__ "0|0|
S0S7bZ21ea0S0S7bZ21a44S0S7bZ21938S0S7bZ21974S0S7bZ202a8S2S7bA1A3A3A3A3A3").
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
S26S8bS25Vi;Vl;S29Vd;S28A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S4S4S4S4S4S4S4S7bS27A2SbA2SbA2SbA2SbA2SbA2S3SdA1A2") := ltac2:(tb__ "0|6|
S6S4S4S4S4S4S4S7bS27A2M0SbA2M1SbA2M2SbA2M3SbA2M4SbA2S3SdA1S6G4SbS6G3SbS6G2SbS6G1SbS6G0SbS7aVL;A1S79S26VL;A1M5U13A2A4S79G5UeA2A4S79G5UaA2A4S79G5UbA2A4S79G5U19A2A4S8dSdSdS9S8cSdS1fR1A1S1dVS;A1A3A1Lp;S1dG5A1A3A4").

Definition SK_a : sstate := ltac:(let x := eval vm_compute in (SJ3 M1a) in exact x).
Lemma SK_a_eq : ltac2:(tb__ "0|0|
S61S19S86S8eA1S2dA3"). Proof. vm_cast_no_check (@eq_refl sstate SK_a). Qed.
Definition MRK_a : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS2dS1A5").
Definition MRK_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS2dS1A5").
Definition RK_a : option (list leaf) := ltac:(let x := eval vm_compute in MRK_a__f in exact x).
Lemma MRK_a_c : MRK_a = RK_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRK_a MRK_a__f. Qed.
Lemma runK_a : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS2dS1A5S51A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SK_a true) MRK_a RK_a (@eq_refl _ (sym_run segs 500 CUTS_K SK_a true)) MRK_a_c). Qed.
Definition LK_a : list leaf := ltac:(let x := eval vm_compute in (unopt RK_a) in exact x).
Definition ST_a : sstate := ltac:(let x := eval vm_compute in (mkSKT (lfs LK_a 0 SK_a)) in exact x).
Lemma ST_a_eq : ltac2:(tb__ "0|0|
S61S19S88S2cS41U0S2dA3A1S31A3"). Proof. vm_cast_no_check (@eq_refl sstate ST_a). Qed.
Definition MRT_a : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS31S1A5").
Definition MRT_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS31S1A5").
Definition RT_a : option (list leaf) := ltac:(let x := eval vm_compute in MRT_a__f in exact x).
Lemma MRT_a_c : MRT_a = RT_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRT_a MRT_a__f. Qed.
Lemma runT_a : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS31S1A5S55A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K ST_a true) MRT_a RT_a (@eq_refl _ (sym_run segs 500 CUTS_K ST_a true)) MRT_a_c). Qed.
Definition LT_a : list leaf := ltac:(let x := eval vm_compute in (unopt RT_a) in exact x).
Definition SV_a : sstate := ltac:(let x := eval vm_compute in (mkSKV (lfs LT_a 0 ST_a)) in exact x).
Lemma SV_a_eq : ltac2:(tb__ "0|0|
S61S19S89S2cS45U0S31A3A1S35A3"). Proof. vm_cast_no_check (@eq_refl sstate SV_a). Qed.
Definition MRV_a : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS35S1A5").
Definition MRV_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS35S1A5").
Definition RV_a : option (list leaf) := ltac:(let x := eval vm_compute in MRV_a__f in exact x).
Lemma MRV_a_c : MRV_a = RV_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRV_a MRV_a__f. Qed.
Lemma runV_a : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS35S1A5S59A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SV_a true) MRV_a RV_a (@eq_refl _ (sym_run segs 500 CUTS_K SV_a true)) MRV_a_c). Qed.
Definition LV_a : list leaf := ltac:(let x := eval vm_compute in (unopt RV_a) in exact x).
Definition SW_a : sstate := ltac:(let x := eval vm_compute in (mkSKW (lfs LV_a 0 SV_a)) in exact x).
Lemma SW_a_eq : ltac2:(tb__ "0|0|
S61S19S8aS2cS49U0S35A3A1S3dA3"). Proof. vm_cast_no_check (@eq_refl sstate SW_a). Qed.
Definition MRW_a : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS3dS1A5").
Definition MRW_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS3dS1A5").
Definition RW_a : option (list leaf) := ltac:(let x := eval vm_compute in MRW_a__f in exact x).
Lemma MRW_a_c : MRW_a = RW_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRW_a MRW_a__f. Qed.
Lemma runW_a : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS3dS1A5S5dA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SW_a true) MRW_a RW_a (@eq_refl _ (sym_run segs 500 CUTS_K SW_a true)) MRW_a_c). Qed.
Definition LW_a : list leaf := ltac:(let x := eval vm_compute in (unopt RW_a) in exact x).
Definition SF0_a : sstate := ltac:(let x := eval vm_compute in (mkSKF (lfs LK_a 0 SK_a)) in exact x).
Lemma SF0_a_eq : ltac2:(tb__ "0|0|
S61S19S87S2cS41U0S2dA3A1S39A3"). Proof. vm_cast_no_check (@eq_refl sstate SF0_a). Qed.
Definition MRF0_a : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS39S1A5").
Definition MRF0_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS39S1A5").
Definition RF0_a : option (list leaf) := ltac:(let x := eval vm_compute in MRF0_a__f in exact x).
Lemma MRF0_a_c : MRF0_a = RF0_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRF0_a MRF0_a__f. Qed.
Lemma runF0_a : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS39S1A5S4dA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SF0_a true) MRF0_a RF0_a (@eq_refl _ (sym_run segs 500 CUTS_K SF0_a true)) MRF0_a_c). Qed.
Definition LF0_a : list leaf := ltac:(let x := eval vm_compute in (unopt RF0_a) in exact x).
Definition SK_b : sstate := ltac:(let x := eval vm_compute in (SJ3 M1b) in exact x).
Lemma SK_b_eq : ltac2:(tb__ "0|0|
S61S19S86S8fA1S2eA3"). Proof. vm_cast_no_check (@eq_refl sstate SK_b). Qed.
Definition MRK_b : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS2eS1A5").
Definition MRK_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS2eS1A5").
Definition RK_b : option (list leaf) := ltac:(let x := eval vm_compute in MRK_b__f in exact x).
Lemma MRK_b_c : MRK_b = RK_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRK_b MRK_b__f. Qed.
Lemma runK_b : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS2eS1A5S52A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SK_b true) MRK_b RK_b (@eq_refl _ (sym_run segs 500 CUTS_K SK_b true)) MRK_b_c). Qed.
Definition LK_b : list leaf := ltac:(let x := eval vm_compute in (unopt RK_b) in exact x).
Definition ST_b : sstate := ltac:(let x := eval vm_compute in (mkSKT (lfs LK_b 0 SK_b)) in exact x).
Lemma ST_b_eq : ltac2:(tb__ "0|0|
S61S19S88S2cS42U0S2eA3A1S32A3"). Proof. vm_cast_no_check (@eq_refl sstate ST_b). Qed.
Definition MRT_b : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS32S1A5").
Definition MRT_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS32S1A5").
Definition RT_b : option (list leaf) := ltac:(let x := eval vm_compute in MRT_b__f in exact x).
Lemma MRT_b_c : MRT_b = RT_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRT_b MRT_b__f. Qed.
Lemma runT_b : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS32S1A5S56A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K ST_b true) MRT_b RT_b (@eq_refl _ (sym_run segs 500 CUTS_K ST_b true)) MRT_b_c). Qed.
Definition LT_b : list leaf := ltac:(let x := eval vm_compute in (unopt RT_b) in exact x).
Definition SV_b : sstate := ltac:(let x := eval vm_compute in (mkSKV (lfs LT_b 0 ST_b)) in exact x).
Lemma SV_b_eq : ltac2:(tb__ "0|0|
S61S19S89S2cS46U0S32A3A1S36A3"). Proof. vm_cast_no_check (@eq_refl sstate SV_b). Qed.
Definition MRV_b : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS36S1A5").
Definition MRV_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS36S1A5").
Definition RV_b : option (list leaf) := ltac:(let x := eval vm_compute in MRV_b__f in exact x).
Lemma MRV_b_c : MRV_b = RV_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRV_b MRV_b__f. Qed.
Lemma runV_b : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS36S1A5S5aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SV_b true) MRV_b RV_b (@eq_refl _ (sym_run segs 500 CUTS_K SV_b true)) MRV_b_c). Qed.
Definition LV_b : list leaf := ltac:(let x := eval vm_compute in (unopt RV_b) in exact x).
Definition SW_b : sstate := ltac:(let x := eval vm_compute in (mkSKW (lfs LV_b 0 SV_b)) in exact x).
Lemma SW_b_eq : ltac2:(tb__ "0|0|
S61S19S8aS2cS4aU0S36A3A1S3eA3"). Proof. vm_cast_no_check (@eq_refl sstate SW_b). Qed.
Definition MRW_b : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS3eS1A5").
Definition MRW_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS3eS1A5").
Definition RW_b : option (list leaf) := ltac:(let x := eval vm_compute in MRW_b__f in exact x).
Lemma MRW_b_c : MRW_b = RW_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRW_b MRW_b__f. Qed.
Lemma runW_b : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS3eS1A5S5eA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SW_b true) MRW_b RW_b (@eq_refl _ (sym_run segs 500 CUTS_K SW_b true)) MRW_b_c). Qed.
Definition LW_b : list leaf := ltac:(let x := eval vm_compute in (unopt RW_b) in exact x).
Definition SF0_b : sstate := ltac:(let x := eval vm_compute in (mkSKF (lfs LK_b 0 SK_b)) in exact x).
Lemma SF0_b_eq : ltac2:(tb__ "0|0|
S61S19S87S2cS42U0S2eA3A1S3aA3"). Proof. vm_cast_no_check (@eq_refl sstate SF0_b). Qed.
Definition MRF0_b : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS3aS1A5").
Definition MRF0_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS3aS1A5").
Definition RF0_b : option (list leaf) := ltac:(let x := eval vm_compute in MRF0_b__f in exact x).
Lemma MRF0_b_c : MRF0_b = RF0_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRF0_b MRF0_b__f. Qed.
Lemma runF0_b : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS3aS1A5S4eA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SF0_b true) MRF0_b RF0_b (@eq_refl _ (sym_run segs 500 CUTS_K SF0_b true)) MRF0_b_c). Qed.
Definition LF0_b : list leaf := ltac:(let x := eval vm_compute in (unopt RF0_b) in exact x).
Definition SK_c : sstate := ltac:(let x := eval vm_compute in (SJ3 M1c) in exact x).
Lemma SK_c_eq : ltac2:(tb__ "0|0|
S61S19S86S90A1S2fA3"). Proof. vm_cast_no_check (@eq_refl sstate SK_c). Qed.
Definition MRK_c : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS2fS1A5").
Definition MRK_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS2fS1A5").
Definition RK_c : option (list leaf) := ltac:(let x := eval vm_compute in MRK_c__f in exact x).
Lemma MRK_c_c : MRK_c = RK_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRK_c MRK_c__f. Qed.
Lemma runK_c : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS2fS1A5S53A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SK_c true) MRK_c RK_c (@eq_refl _ (sym_run segs 500 CUTS_K SK_c true)) MRK_c_c). Qed.
Definition LK_c : list leaf := ltac:(let x := eval vm_compute in (unopt RK_c) in exact x).
Definition ST_c : sstate := ltac:(let x := eval vm_compute in (mkSKT (lfs LK_c 0 SK_c)) in exact x).
Lemma ST_c_eq : ltac2:(tb__ "0|0|
S61S19S88S2cS43U0S2fA3A1S33A3"). Proof. vm_cast_no_check (@eq_refl sstate ST_c). Qed.
Definition MRT_c : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS33S1A5").
Definition MRT_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS33S1A5").
Definition RT_c : option (list leaf) := ltac:(let x := eval vm_compute in MRT_c__f in exact x).
Lemma MRT_c_c : MRT_c = RT_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRT_c MRT_c__f. Qed.
Lemma runT_c : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS33S1A5S57A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K ST_c true) MRT_c RT_c (@eq_refl _ (sym_run segs 500 CUTS_K ST_c true)) MRT_c_c). Qed.
Definition LT_c : list leaf := ltac:(let x := eval vm_compute in (unopt RT_c) in exact x).
Definition SV_c : sstate := ltac:(let x := eval vm_compute in (mkSKV (lfs LT_c 0 ST_c)) in exact x).
Lemma SV_c_eq : ltac2:(tb__ "0|0|
S61S19S89S2cS47U0S33A3A1S37A3"). Proof. vm_cast_no_check (@eq_refl sstate SV_c). Qed.
Definition MRV_c : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS37S1A5").
Definition MRV_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS37S1A5").
Definition RV_c : option (list leaf) := ltac:(let x := eval vm_compute in MRV_c__f in exact x).
Lemma MRV_c_c : MRV_c = RV_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRV_c MRV_c__f. Qed.
Lemma runV_c : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS37S1A5S5bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SV_c true) MRV_c RV_c (@eq_refl _ (sym_run segs 500 CUTS_K SV_c true)) MRV_c_c). Qed.
Definition LV_c : list leaf := ltac:(let x := eval vm_compute in (unopt RV_c) in exact x).
Definition SW_c : sstate := ltac:(let x := eval vm_compute in (mkSKW (lfs LV_c 0 SV_c)) in exact x).
Lemma SW_c_eq : ltac2:(tb__ "0|0|
S61S19S8aS2cS4bU0S37A3A1S3fA3"). Proof. vm_cast_no_check (@eq_refl sstate SW_c). Qed.
Definition MRW_c : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS3fS1A5").
Definition MRW_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS3fS1A5").
Definition RW_c : option (list leaf) := ltac:(let x := eval vm_compute in MRW_c__f in exact x).
Lemma MRW_c_c : MRW_c = RW_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRW_c MRW_c__f. Qed.
Lemma runW_c : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS3fS1A5S5fA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SW_c true) MRW_c RW_c (@eq_refl _ (sym_run segs 500 CUTS_K SW_c true)) MRW_c_c). Qed.
Definition LW_c : list leaf := ltac:(let x := eval vm_compute in (unopt RW_c) in exact x).
Definition SF0_c : sstate := ltac:(let x := eval vm_compute in (mkSKF (lfs LK_c 0 SK_c)) in exact x).
Lemma SF0_c_eq : ltac2:(tb__ "0|0|
S61S19S87S2cS43U0S2fA3A1S3bA3"). Proof. vm_cast_no_check (@eq_refl sstate SF0_c). Qed.
Definition MRF0_c : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS3bS1A5").
Definition MRF0_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS3bS1A5").
Definition RF0_c : option (list leaf) := ltac:(let x := eval vm_compute in MRF0_c__f in exact x).
Lemma MRF0_c_c : MRF0_c = RF0_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRF0_c MRF0_c__f. Qed.
Lemma runF0_c : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS3bS1A5S4fA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SF0_c true) MRF0_c RF0_c (@eq_refl _ (sym_run segs 500 CUTS_K SF0_c true)) MRF0_c_c). Qed.
Definition LF0_c : list leaf := ltac:(let x := eval vm_compute in (unopt RF0_c) in exact x).
Definition SK_d : sstate := ltac:(let x := eval vm_compute in (SJ3 M1d) in exact x).
Lemma SK_d_eq : ltac2:(tb__ "0|0|
S61S19S86S91A1S30A3"). Proof. vm_cast_no_check (@eq_refl sstate SK_d). Qed.
Definition MRK_d : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS30S1A5").
Definition MRK_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS30S1A5").
Definition RK_d : option (list leaf) := ltac:(let x := eval vm_compute in MRK_d__f in exact x).
Lemma MRK_d_c : MRK_d = RK_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRK_d MRK_d__f. Qed.
Lemma runK_d : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS30S1A5S54A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SK_d true) MRK_d RK_d (@eq_refl _ (sym_run segs 500 CUTS_K SK_d true)) MRK_d_c). Qed.
Definition LK_d : list leaf := ltac:(let x := eval vm_compute in (unopt RK_d) in exact x).
Definition ST_d : sstate := ltac:(let x := eval vm_compute in (mkSKT (lfs LK_d 0 SK_d)) in exact x).
Lemma ST_d_eq : ltac2:(tb__ "0|0|
S61S19S88S2cS44U0S30A3A1S34A3"). Proof. vm_cast_no_check (@eq_refl sstate ST_d). Qed.
Definition MRT_d : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS34S1A5").
Definition MRT_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS34S1A5").
Definition RT_d : option (list leaf) := ltac:(let x := eval vm_compute in MRT_d__f in exact x).
Lemma MRT_d_c : MRT_d = RT_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRT_d MRT_d__f. Qed.
Lemma runT_d : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS34S1A5S58A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K ST_d true) MRT_d RT_d (@eq_refl _ (sym_run segs 500 CUTS_K ST_d true)) MRT_d_c). Qed.
Definition LT_d : list leaf := ltac:(let x := eval vm_compute in (unopt RT_d) in exact x).
Definition SV_d : sstate := ltac:(let x := eval vm_compute in (mkSKV (lfs LT_d 0 ST_d)) in exact x).
Lemma SV_d_eq : ltac2:(tb__ "0|0|
S61S19S89S2cS48U0S34A3A1S38A3"). Proof. vm_cast_no_check (@eq_refl sstate SV_d). Qed.
Definition MRV_d : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS38S1A5").
Definition MRV_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS38S1A5").
Definition RV_d : option (list leaf) := ltac:(let x := eval vm_compute in MRV_d__f in exact x).
Lemma MRV_d_c : MRV_d = RV_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRV_d MRV_d__f. Qed.
Lemma runV_d : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS38S1A5S5cA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SV_d true) MRV_d RV_d (@eq_refl _ (sym_run segs 500 CUTS_K SV_d true)) MRV_d_c). Qed.
Definition LV_d : list leaf := ltac:(let x := eval vm_compute in (unopt RV_d) in exact x).
Definition SW_d : sstate := ltac:(let x := eval vm_compute in (mkSKW (lfs LV_d 0 SV_d)) in exact x).
Lemma SW_d_eq : ltac2:(tb__ "0|0|
S61S19S8aS2cS4cU0S38A3A1S40A3"). Proof. vm_cast_no_check (@eq_refl sstate SW_d). Qed.
Definition MRW_d : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS40S1A5").
Definition MRW_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS40S1A5").
Definition RW_d : option (list leaf) := ltac:(let x := eval vm_compute in MRW_d__f in exact x).
Lemma MRW_d_c : MRW_d = RW_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRW_d MRW_d__f. Qed.
Lemma runW_d : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS40S1A5S60A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SW_d true) MRW_d RW_d (@eq_refl _ (sym_run segs 500 CUTS_K SW_d true)) MRW_d_c). Qed.
Definition LW_d : list leaf := ltac:(let x := eval vm_compute in (unopt RW_d) in exact x).
Definition SF0_d : sstate := ltac:(let x := eval vm_compute in (mkSKF (lfs LK_d 0 SK_d)) in exact x).
Lemma SF0_d_eq : ltac2:(tb__ "0|0|
S61S19S87S2cS44U0S30A3A1S3cA3"). Proof. vm_cast_no_check (@eq_refl sstate SF0_d). Qed.
Definition MRF0_d : option (list leaf) := ltac2:(tb__ "0|0|
S24S2bU1f4S2aS3cS1A5").
Definition MRF0_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S2bU1f4S2aS3cS1A5").
Definition RF0_d : option (list leaf) := ltac:(let x := eval vm_compute in MRF0_d__f in exact x).
Lemma MRF0_d_c : MRF0_d = RF0_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRF0_d MRF0_d__f. Qed.
Lemma runF0_d : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S2bU1f4S2aS3cS1A5S50A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K SF0_d true) MRF0_d RF0_d (@eq_refl _ (sym_run segs 500 CUTS_K SF0_d true)) MRF0_d_c). Qed.
Definition LF0_d : list leaf := ltac:(let x := eval vm_compute in (unopt RF0_d) in exact x).
End Mal_agrp_rK.

Module Mal_agrp_rN7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS_N : list Z := [0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
S26S8bS25Vi;Vl;S29Vd;S28A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S4S4S4S4S4S4S4S7bS27A2SbA2SbA2SbA2SbA2SbA2S3SdA1A2") := ltac2:(tb__ "0|6|
S6S4S4S4S4S4S4S7bS27A2M0SbA2M1SbA2M2SbA2M3SbA2M4SbA2S3SdA1S6G4SbS6G3SbS6G2SbS6G1SbS6G0SbS7aVL;A1S79S26VL;A1M5U13A2A4S79G5UeA2A4S79G5UaA2A4S79G5UbA2A4S79G5U19A2A4S8dSdSdS9S8cSdS1fR1A1S1dVS;A1A3A1Lp;S1dG5A1A3A4").

Definition SN_17_3_L : sstate := ltac:(let x := eval vm_compute in (SN3z 17 3 false) in exact x).
Lemma SN_17_3_L_eq : SN3z 17 3 false = SN_17_3_L. Proof. vm_cast_no_check (@eq_refl sstate SN_17_3_L). Qed.
Definition MRN_17_3_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S7dU1f4S7cS7eS1A5").
Definition MRN_17_3_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S7dU1f4S7cS7eS1A5").
Definition RN_17_3_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_17_3_L__f in exact x).
Lemma MRN_17_3_L_c : MRN_17_3_L = RN_17_3_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_17_3_L MRN_17_3_L__f. Qed.
Lemma runN_17_3_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S7dU1f4S7cS7eS1A5S82A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_17_3_L true) MRN_17_3_L RN_17_3_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_17_3_L true)) MRN_17_3_L_c). Qed.
Definition LN_17_3_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_17_3_L) in exact x).
Definition SN_17_3_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 17 3 true) in exact x).
Lemma SN_17_3_Z_eq : SN3z 17 3 true = SN_17_3_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_17_3_Z). Qed.
Definition MRN_17_3_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S7dU1f4S7cS7fS1A5").
Definition MRN_17_3_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S7dU1f4S7cS7fS1A5").
Definition RN_17_3_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_17_3_Z__f in exact x).
Lemma MRN_17_3_Z_c : MRN_17_3_Z = RN_17_3_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_17_3_Z MRN_17_3_Z__f. Qed.
Lemma runN_17_3_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S7dU1f4S7cS7fS1A5S83A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_17_3_Z true) MRN_17_3_Z RN_17_3_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_17_3_Z true)) MRN_17_3_Z_c). Qed.
Definition LN_17_3_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_17_3_Z) in exact x).
Definition SN_19_2_L : sstate := ltac:(let x := eval vm_compute in (SN3z 19 2 false) in exact x).
Lemma SN_19_2_L_eq : SN3z 19 2 false = SN_19_2_L. Proof. vm_cast_no_check (@eq_refl sstate SN_19_2_L). Qed.
Definition MRN_19_2_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S7dU1f4S7cS80S1A5").
Definition MRN_19_2_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S7dU1f4S7cS80S1A5").
Definition RN_19_2_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_19_2_L__f in exact x).
Lemma MRN_19_2_L_c : MRN_19_2_L = RN_19_2_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_19_2_L MRN_19_2_L__f. Qed.
Lemma runN_19_2_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S7dU1f4S7cS80S1A5S84A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_19_2_L true) MRN_19_2_L RN_19_2_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_19_2_L true)) MRN_19_2_L_c). Qed.
Definition LN_19_2_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_19_2_L) in exact x).
Definition SN_19_2_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 19 2 true) in exact x).
Lemma SN_19_2_Z_eq : SN3z 19 2 true = SN_19_2_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_19_2_Z). Qed.
Definition MRN_19_2_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S7dU1f4S7cS81S1A5").
Definition MRN_19_2_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S7dU1f4S7cS81S1A5").
Definition RN_19_2_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_19_2_Z__f in exact x).
Lemma MRN_19_2_Z_c : MRN_19_2_Z = RN_19_2_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_19_2_Z MRN_19_2_Z__f. Qed.
Lemma runN_19_2_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S7dU1f4S7cS81S1A5S85A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_19_2_Z true) MRN_19_2_Z RN_19_2_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_19_2_Z true)) MRN_19_2_Z_c). Qed.
Definition LN_19_2_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_19_2_Z) in exact x).
End Mal_agrp_rN7.

Module Mal_agrp_rN5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS_N : list Z := [0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
S26S8bS25Vi;Vl;S29Vd;S28A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S4S4S4S4S4S4S4S7bS27A2SbA2SbA2SbA2SbA2SbA2S3SdA1A2") := ltac2:(tb__ "0|6|
S6S4S4S4S4S4S4S7bS27A2M0SbA2M1SbA2M2SbA2M3SbA2M4SbA2S3SdA1S6G4SbS6G3SbS6G2SbS6G1SbS6G0SbS7aVL;A1S79S26VL;A1M5U13A2A4S79G5UeA2A4S79G5UaA2A4S79G5UbA2A4S79G5U19A2A4S8dSdSdS9S8cSdS1fR1A1S1dVS;A1A3A1Lp;S1dG5A1A3A4").

Definition SN_10_10_L : sstate := ltac:(let x := eval vm_compute in (SN3z 10 10 false) in exact x).
Lemma SN_10_10_L_eq : SN3z 10 10 false = SN_10_10_L. Proof. vm_cast_no_check (@eq_refl sstate SN_10_10_L). Qed.
Definition MRN_10_10_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S65S1A5").
Definition MRN_10_10_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S65S1A5").
Definition RN_10_10_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_10_10_L__f in exact x).
Lemma MRN_10_10_L_c : MRN_10_10_L = RN_10_10_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_10_10_L MRN_10_10_L__f. Qed.
Lemma runN_10_10_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S65S1A5S6fA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_10_10_L true) MRN_10_10_L RN_10_10_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_10_10_L true)) MRN_10_10_L_c). Qed.
Definition LN_10_10_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_10_10_L) in exact x).
Definition SN_10_10_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 10 10 true) in exact x).
Lemma SN_10_10_Z_eq : SN3z 10 10 true = SN_10_10_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_10_10_Z). Qed.
Definition MRN_10_10_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S66S1A5").
Definition MRN_10_10_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S66S1A5").
Definition RN_10_10_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_10_10_Z__f in exact x).
Lemma MRN_10_10_Z_c : MRN_10_10_Z = RN_10_10_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_10_10_Z MRN_10_10_Z__f. Qed.
Lemma runN_10_10_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S66S1A5S70A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_10_10_Z true) MRN_10_10_Z RN_10_10_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_10_10_Z true)) MRN_10_10_Z_c). Qed.
Definition LN_10_10_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_10_10_Z) in exact x).
Definition SN_11_2_L : sstate := ltac:(let x := eval vm_compute in (SN3z 11 2 false) in exact x).
Lemma SN_11_2_L_eq : SN3z 11 2 false = SN_11_2_L. Proof. vm_cast_no_check (@eq_refl sstate SN_11_2_L). Qed.
Definition MRN_11_2_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S67S1A5").
Definition MRN_11_2_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S67S1A5").
Definition RN_11_2_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_11_2_L__f in exact x).
Lemma MRN_11_2_L_c : MRN_11_2_L = RN_11_2_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_11_2_L MRN_11_2_L__f. Qed.
Lemma runN_11_2_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S67S1A5S71A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_11_2_L true) MRN_11_2_L RN_11_2_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_11_2_L true)) MRN_11_2_L_c). Qed.
Definition LN_11_2_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_11_2_L) in exact x).
Definition SN_11_2_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 11 2 true) in exact x).
Lemma SN_11_2_Z_eq : SN3z 11 2 true = SN_11_2_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_11_2_Z). Qed.
Definition MRN_11_2_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S68S1A5").
Definition MRN_11_2_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S68S1A5").
Definition RN_11_2_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_11_2_Z__f in exact x).
Lemma MRN_11_2_Z_c : MRN_11_2_Z = RN_11_2_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_11_2_Z MRN_11_2_Z__f. Qed.
Lemma runN_11_2_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S68S1A5S72A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_11_2_Z true) MRN_11_2_Z RN_11_2_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_11_2_Z true)) MRN_11_2_Z_c). Qed.
Definition LN_11_2_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_11_2_Z) in exact x).
Definition SN_11_4_L : sstate := ltac:(let x := eval vm_compute in (SN3z 11 4 false) in exact x).
Lemma SN_11_4_L_eq : SN3z 11 4 false = SN_11_4_L. Proof. vm_cast_no_check (@eq_refl sstate SN_11_4_L). Qed.
Definition MRN_11_4_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S69S1A5").
Definition MRN_11_4_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S69S1A5").
Definition RN_11_4_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_11_4_L__f in exact x).
Lemma MRN_11_4_L_c : MRN_11_4_L = RN_11_4_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_11_4_L MRN_11_4_L__f. Qed.
Lemma runN_11_4_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S69S1A5S73A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_11_4_L true) MRN_11_4_L RN_11_4_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_11_4_L true)) MRN_11_4_L_c). Qed.
Definition LN_11_4_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_11_4_L) in exact x).
Definition SN_11_4_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 11 4 true) in exact x).
Lemma SN_11_4_Z_eq : SN3z 11 4 true = SN_11_4_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_11_4_Z). Qed.
Definition MRN_11_4_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S6aS1A5").
Definition MRN_11_4_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S6aS1A5").
Definition RN_11_4_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_11_4_Z__f in exact x).
Lemma MRN_11_4_Z_c : MRN_11_4_Z = RN_11_4_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_11_4_Z MRN_11_4_Z__f. Qed.
Lemma runN_11_4_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S6aS1A5S74A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_11_4_Z true) MRN_11_4_Z RN_11_4_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_11_4_Z true)) MRN_11_4_Z_c). Qed.
Definition LN_11_4_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_11_4_Z) in exact x).
Definition SN_11_8_L : sstate := ltac:(let x := eval vm_compute in (SN3z 11 8 false) in exact x).
Lemma SN_11_8_L_eq : SN3z 11 8 false = SN_11_8_L. Proof. vm_cast_no_check (@eq_refl sstate SN_11_8_L). Qed.
Definition MRN_11_8_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S6bS1A5").
Definition MRN_11_8_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S6bS1A5").
Definition RN_11_8_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_11_8_L__f in exact x).
Lemma MRN_11_8_L_c : MRN_11_8_L = RN_11_8_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_11_8_L MRN_11_8_L__f. Qed.
Lemma runN_11_8_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S6bS1A5S75A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_11_8_L true) MRN_11_8_L RN_11_8_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_11_8_L true)) MRN_11_8_L_c). Qed.
Definition LN_11_8_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_11_8_L) in exact x).
Definition SN_11_8_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 11 8 true) in exact x).
Lemma SN_11_8_Z_eq : SN3z 11 8 true = SN_11_8_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_11_8_Z). Qed.
Definition MRN_11_8_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S6cS1A5").
Definition MRN_11_8_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S6cS1A5").
Definition RN_11_8_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_11_8_Z__f in exact x).
Lemma MRN_11_8_Z_c : MRN_11_8_Z = RN_11_8_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_11_8_Z MRN_11_8_Z__f. Qed.
Lemma runN_11_8_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S6cS1A5S76A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_11_8_Z true) MRN_11_8_Z RN_11_8_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_11_8_Z true)) MRN_11_8_Z_c). Qed.
Definition LN_11_8_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_11_8_Z) in exact x).
Definition SN_12_7_L : sstate := ltac:(let x := eval vm_compute in (SN3z 12 7 false) in exact x).
Lemma SN_12_7_L_eq : SN3z 12 7 false = SN_12_7_L. Proof. vm_cast_no_check (@eq_refl sstate SN_12_7_L). Qed.
Definition MRN_12_7_L : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S6dS1A5").
Definition MRN_12_7_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S6dS1A5").
Definition RN_12_7_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_12_7_L__f in exact x).
Lemma MRN_12_7_L_c : MRN_12_7_L = RN_12_7_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_12_7_L MRN_12_7_L__f. Qed.
Lemma runN_12_7_L : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S6dS1A5S77A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_12_7_L true) MRN_12_7_L RN_12_7_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_12_7_L true)) MRN_12_7_L_c). Qed.
Definition LN_12_7_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_12_7_L) in exact x).
Definition SN_12_7_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 12 7 true) in exact x).
Lemma SN_12_7_Z_eq : SN3z 12 7 true = SN_12_7_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_12_7_Z). Qed.
Definition MRN_12_7_Z : option (list leaf) := ltac2:(tb__ "0|0|
S24S64U1f4S63S6eS1A5").
Definition MRN_12_7_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S62S64U1f4S63S6eS1A5").
Definition RN_12_7_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_12_7_Z__f in exact x).
Lemma MRN_12_7_Z_c : MRN_12_7_Z = RN_12_7_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_12_7_Z MRN_12_7_Z__f. Qed.
Lemma runN_12_7_Z : ltac2:(tb__ "0|0|
S61S5S3S25A1A1S24S64U1f4S63S6eS1A5S78A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_12_7_Z true) MRN_12_7_Z RN_12_7_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_12_7_Z true)) MRN_12_7_Z_c). Qed.
Definition LN_12_7_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_12_7_Z) in exact x).
End Mal_agrp_rN5.
