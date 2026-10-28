(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "list"; "prod"; "pair"; "option"; "nil"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "CUTS_C"; "segs"; "SC_0"; "SC_1"; "SC_10"; "SC_11"; "SC_12"; "SC_13"; "SC_14"; "SC_15"; "SC_16"; "SC_17"; "SC_18"; "SC_19"; "SC_2"; "SC_20"; "SC_21"; "SC_22"; "SC_23"; "SC_24"; "SC_25"; "SC_26"; "SC_27"; "SC_28"; "SC_29"; "SC_3"; "SC_30"; "SC_31"; "SC_32"; "SC_33"; "SC_34"; "SC_35"; "SC_36"; "SC_37"; "SC_38"; "SC_39"; "SC_4"; "SC_40"; "SC_41"; "SC_42"; "SC_43"; "SC_44"; "SC_45"; "SC_46"; "SC_47"; "SC_5"; "SC_6"; "SC_7"; "SC_8"; "SC_9"; "LC_0"; "LC_1"; "LC_10"; "LC_11"; "LC_12"; "LC_13"; "LC_14"; "LC_15"; "LC_16"; "LC_17"; "LC_18"; "LC_19"; "LC_2"; "LC_20"; "LC_21"; "LC_22"; "LC_23"; "LC_24"; "LC_25"; "LC_26"; "LC_27"; "LC_28"; "LC_29"; "LC_3"; "LC_30"; "LC_31"; "LC_32"; "LC_33"; "LC_34"; "LC_35"; "LC_36"; "LC_37"; "LC_38"; "LC_39"; "LC_4"; "LC_40"; "LC_41"; "LC_42"; "LC_43"; "LC_44"; "LC_45"; "LC_46"; "LC_47"; "LC_5"; "LC_6"; "LC_7"; "LC_8"; "LC_9"; "RC_0"; "RC_1"; "RC_10"; "RC_11"; "RC_12"; "RC_13"; "RC_14"; "RC_15"; "RC_16"; "RC_17"; "RC_18"; "RC_19"; "RC_2"; "RC_20"; "RC_21"; "RC_22"; "RC_23"; "RC_24"; "RC_25"; "RC_26"; "RC_27"; "RC_28"; "RC_29"; "RC_3"; "RC_30"; "RC_31"; "RC_32"; "RC_33"; "RC_34"; "RC_35"; "RC_36"; "RC_37"; "RC_38"; "RC_39"; "RC_4"; "RC_40"; "RC_41"; "RC_42"; "RC_43"; "RC_44"; "RC_45"; "RC_46"; "RC_47"; "RC_5"; "RC_6"; "RC_7"; "RC_8"; "RC_9"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sym_run"; "stop_reason"; "leaf"; "RsCut"; "lf_state"; "RsFuel"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sstate"; "ss_facts"; "sprop_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "sh"; "reg"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rM1"; "CUTS_M1"; "segs"; "SM1_a"; "SM1_b"; "SM1_c"; "SM1_d"; "LM1_a"; "LM1_b"; "LM1_c"; "LM1_d"; "RM1_a"; "RM1_b"; "RM1_c"; "RM1_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rMA"; "CUTS_MA"; "segs"; "SMA_a"; "SMA_b"; "SMA_c"; "SMA_d"; "RMA_a"; "RMA_b"; "RMA_c"; "RMA_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rMB"; "CUTS_MB"; "segs"; "SMB_a"; "SMB_b"; "SMB_c"; "SMB_d"; "RMB_a"; "RMB_b"; "RMB_c"; "RMB_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rMC"; "CUTS_MC"; "segs"; "SMC_a"; "SMC_b"; "SMC_c"; "SMC_d"; "RMC_a"; "RMC_b"; "RMC_c"; "RMC_d"; "@Stdlib.Lists.List"; "existsb"; "filter"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "M1a"; "M1b"; "M1c"; "M1d"; "SM1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "SJA"; "SJB"; "SM23"].
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

Module Mal_agrp_rM1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS_M1 : list Z := [0x21818; 0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
Sa0SacS9eVi;Vl;Sa2Vd;Sa1A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S3S3S3S3S3S3S3S9bS9dA2Sa3A2Sa3A2Sa3A2Sa3A2Sa3A2S2Sa4A1A2") := ltac2:(tb__ "0|6|
S4S3S3S3S3S3S3S9bS9dA2M0Sa3A2M1Sa3A2M2Sa3A2M3Sa3A2M4Sa3A2S2Sa4A1S4G4Sa3S4G3Sa3S4G2Sa3S4G1Sa3S4G0Sa3Sa9VL;A1SaaSa0VL;A1M5U13A2A4SaaG5UeA2A4SaaG5UaA2A4SaaG5UbA2A4SaaG5U19A2A4SdaSa4Sa4S7Sd9Sa4Sa7R1A1Sa6VS;A1A3A1Lp;Sa6G5A1A3A4").

Definition SM1_a : sstate := ltac:(let x := eval vm_compute in (SM1 M1a) in exact x).
Lemma SM1_a_eq : ltac2:(tb__ "0|0|
S9aSa5SdfSdbA1SafA3"). Proof. vm_cast_no_check (@eq_refl sstate SM1_a). Qed.
Definition MRM1_a : option (list leaf) := ltac2:(tb__ "0|0|
S9cSaeU1f4SadSafS1A5").
Definition MRM1_a__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SaeU1f4SadSafS1A5").
Definition RM1_a : option (list leaf) := ltac:(let x := eval vm_compute in MRM1_a__f in exact x).
Lemma MRM1_a_c : MRM1_a = RM1_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRM1_a MRM1_a__f. Qed.
Lemma runM1_a : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSaeU1f4SadSafS1A5Sb7A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_M1 SM1_a true) MRM1_a RM1_a (@eq_refl _ (sym_run segs 500 CUTS_M1 SM1_a true)) MRM1_a_c). Qed.
Definition LM1_a : list leaf := ltac:(let x := eval vm_compute in (unopt RM1_a) in exact x).
Lemma LM1_a_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9Sb3A4S0G0S4S9bS9dZ21818S9fA4M1S0G0G1S6G0A1A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SM1_b : sstate := ltac:(let x := eval vm_compute in (SM1 M1b) in exact x).
Lemma SM1_b_eq : ltac2:(tb__ "0|0|
S9aSa5SdfSdcA1Sb0A3"). Proof. vm_cast_no_check (@eq_refl sstate SM1_b). Qed.
Definition MRM1_b : option (list leaf) := ltac2:(tb__ "0|0|
S9cSaeU1f4SadSb0S1A5").
Definition MRM1_b__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SaeU1f4SadSb0S1A5").
Definition RM1_b : option (list leaf) := ltac:(let x := eval vm_compute in MRM1_b__f in exact x).
Lemma MRM1_b_c : MRM1_b = RM1_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRM1_b MRM1_b__f. Qed.
Lemma runM1_b : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSaeU1f4SadSb0S1A5Sb8A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_M1 SM1_b true) MRM1_b RM1_b (@eq_refl _ (sym_run segs 500 CUTS_M1 SM1_b true)) MRM1_b_c). Qed.
Definition LM1_b : list leaf := ltac:(let x := eval vm_compute in (unopt RM1_b) in exact x).
Lemma LM1_b_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9Sb4A4S0G0S4S9bS9dZ21818S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SM1_c : sstate := ltac:(let x := eval vm_compute in (SM1 M1c) in exact x).
Lemma SM1_c_eq : ltac2:(tb__ "0|0|
S9aSa5SdfSddA1Sb1A3"). Proof. vm_cast_no_check (@eq_refl sstate SM1_c). Qed.
Definition MRM1_c : option (list leaf) := ltac2:(tb__ "0|0|
S9cSaeU1f4SadSb1S1A5").
Definition MRM1_c__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SaeU1f4SadSb1S1A5").
Definition RM1_c : option (list leaf) := ltac:(let x := eval vm_compute in MRM1_c__f in exact x).
Lemma MRM1_c_c : MRM1_c = RM1_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRM1_c MRM1_c__f. Qed.
Lemma runM1_c : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSaeU1f4SadSb1S1A5Sb9A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_M1 SM1_c true) MRM1_c RM1_c (@eq_refl _ (sym_run segs 500 CUTS_M1 SM1_c true)) MRM1_c_c). Qed.
Definition LM1_c : list leaf := ltac:(let x := eval vm_compute in (unopt RM1_c) in exact x).
Lemma LM1_c_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9Sb5A4S0G0S4S9bS9dZ21818S9fA4M1S0G0G1S6G0A1A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SM1_d : sstate := ltac:(let x := eval vm_compute in (SM1 M1d) in exact x).
Lemma SM1_d_eq : ltac2:(tb__ "0|0|
S9aSa5SdfSdeA1Sb2A3"). Proof. vm_cast_no_check (@eq_refl sstate SM1_d). Qed.
Definition MRM1_d : option (list leaf) := ltac2:(tb__ "0|0|
S9cSaeU1f4SadSb2S1A5").
Definition MRM1_d__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SaeU1f4SadSb2S1A5").
Definition RM1_d : option (list leaf) := ltac:(let x := eval vm_compute in MRM1_d__f in exact x).
Lemma MRM1_d_c : MRM1_d = RM1_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRM1_d MRM1_d__f. Qed.
Lemma runM1_d : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSaeU1f4SadSb2S1A5SbaA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_M1 SM1_d true) MRM1_d RM1_d (@eq_refl _ (sym_run segs 500 CUTS_M1 SM1_d true)) MRM1_d_c). Qed.
Definition LM1_d : list leaf := ltac:(let x := eval vm_compute in (unopt RM1_d) in exact x).
Lemma LM1_d_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9Sb6A4S0G0S4S9bS9dZ21818S9fA4M1S0G0G1S6G0A1A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
End Mal_agrp_rM1.

Module Mal_agrp_rMA.

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
Definition CUTS_MA : list Z := [0x2182c; 0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
Sa0SacS9eVi;Vl;Sa2Vd;Sa1A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S3S3S3S3S3S3S3S9bS9dA2Sa3A2Sa3A2Sa3A2Sa3A2Sa3A2S2Sa4A1A2") := ltac2:(tb__ "0|6|
S4S3S3S3S3S3S3S9bS9dA2M0Sa3A2M1Sa3A2M2Sa3A2M3Sa3A2M4Sa3A2S2Sa4A1S4G4Sa3S4G3Sa3S4G2Sa3S4G1Sa3S4G0Sa3Sa9VL;A1SaaSa0VL;A1M5U13A2A4SaaG5UeA2A4SaaG5UaA2A4SaaG5UbA2A4SaaG5U19A2A4SdaSa4Sa4S7Sd9Sa4Sa7R1A1Sa6VS;A1A3A1Lp;Sa6G5A1A3A4").

Definition SMA_a : sstate := ltac:(let x := eval vm_compute in (SM23 M1a) in exact x).
Lemma SMA_a_eq : ltac2:(tb__ "0|0|
S9aSa5Se2SdbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl sstate SMA_a). Qed.
Definition MRMA_a : option (list leaf) := ltac2:(tb__ "0|0|
S9cSbcU1f4SbbSbdS1A5").
Definition MRMA_a__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SbcU1f4SbbSbdS1A5").
Definition RMA_a : option (list leaf) := ltac:(let x := eval vm_compute in MRMA_a__f in exact x).
Lemma MRMA_a_c : MRMA_a = RMA_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMA_a MRMA_a__f. Qed.
Lemma runMA_a : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSbcU1f4SbbSbdS1A5Sc1A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MA SMA_a true) MRMA_a RMA_a (@eq_refl _ (sym_run segs 500 CUTS_MA SMA_a true)) MRMA_a_c). Qed.
Definition LMA_a : list leaf := ltac:(let x := eval vm_compute in (unopt RMA_a) in exact x).
Definition SMA_b : sstate := ltac:(let x := eval vm_compute in (SM23 M1b) in exact x).
Lemma SMA_b_eq : ltac2:(tb__ "0|0|
S9aSa5Se2SdcA1SbeA3"). Proof. vm_cast_no_check (@eq_refl sstate SMA_b). Qed.
Definition MRMA_b : option (list leaf) := ltac2:(tb__ "0|0|
S9cSbcU1f4SbbSbeS1A5").
Definition MRMA_b__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SbcU1f4SbbSbeS1A5").
Definition RMA_b : option (list leaf) := ltac:(let x := eval vm_compute in MRMA_b__f in exact x).
Lemma MRMA_b_c : MRMA_b = RMA_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMA_b MRMA_b__f. Qed.
Lemma runMA_b : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSbcU1f4SbbSbeS1A5Sc2A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MA SMA_b true) MRMA_b RMA_b (@eq_refl _ (sym_run segs 500 CUTS_MA SMA_b true)) MRMA_b_c). Qed.
Definition LMA_b : list leaf := ltac:(let x := eval vm_compute in (unopt RMA_b) in exact x).
Definition SMA_c : sstate := ltac:(let x := eval vm_compute in (SM23 M1c) in exact x).
Lemma SMA_c_eq : ltac2:(tb__ "0|0|
S9aSa5Se2SddA1SbfA3"). Proof. vm_cast_no_check (@eq_refl sstate SMA_c). Qed.
Definition MRMA_c : option (list leaf) := ltac2:(tb__ "0|0|
S9cSbcU1f4SbbSbfS1A5").
Definition MRMA_c__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SbcU1f4SbbSbfS1A5").
Definition RMA_c : option (list leaf) := ltac:(let x := eval vm_compute in MRMA_c__f in exact x).
Lemma MRMA_c_c : MRMA_c = RMA_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMA_c MRMA_c__f. Qed.
Lemma runMA_c : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSbcU1f4SbbSbfS1A5Sc3A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MA SMA_c true) MRMA_c RMA_c (@eq_refl _ (sym_run segs 500 CUTS_MA SMA_c true)) MRMA_c_c). Qed.
Definition LMA_c : list leaf := ltac:(let x := eval vm_compute in (unopt RMA_c) in exact x).
Definition SMA_d : sstate := ltac:(let x := eval vm_compute in (SM23 M1d) in exact x).
Lemma SMA_d_eq : ltac2:(tb__ "0|0|
S9aSa5Se2SdeA1Sc0A3"). Proof. vm_cast_no_check (@eq_refl sstate SMA_d). Qed.
Definition MRMA_d : option (list leaf) := ltac2:(tb__ "0|0|
S9cSbcU1f4SbbSc0S1A5").
Definition MRMA_d__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8SbcU1f4SbbSc0S1A5").
Definition RMA_d : option (list leaf) := ltac:(let x := eval vm_compute in MRMA_d__f in exact x).
Lemma MRMA_d_c : MRMA_d = RMA_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMA_d MRMA_d__f. Qed.
Lemma runMA_d : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSbcU1f4SbbSc0S1A5Sc4A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MA SMA_d true) MRMA_d RMA_d (@eq_refl _ (sym_run segs 500 CUTS_MA SMA_d true)) MRMA_d_c). Qed.
Definition LMA_d : list leaf := ltac:(let x := eval vm_compute in (unopt RMA_d) in exact x).
End Mal_agrp_rMA.

Module Mal_agrp_rC.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS_C : list Z := ltac2:(tb__ "0|0|
S0S9bZ21538S0S9bZ2126cS0S9bZ21ea0S0S9bZ21818S0S9bZ218fcS0S9bZ202a8S6S9bA1A3A3A3A3A3A3").
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
Sa0SacS9eVi;Vl;Sa2Vd;Sa1A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S3S3S3S3S3S3S3S9bS9dA2Sa3A2Sa3A2Sa3A2Sa3A2Sa3A2S2Sa4A1A2") := ltac2:(tb__ "0|6|
S4S3S3S3S3S3S3S9bS9dA2M0Sa3A2M1Sa3A2M2Sa3A2M3Sa3A2M4Sa3A2S2Sa4A1S4G4Sa3S4G3Sa3S4G2Sa3S4G1Sa3S4G0Sa3Sa9VL;A1SaaSa0VL;A1M5U13A2A4SaaG5UeA2A4SaaG5UaA2A4SaaG5UbA2A4SaaG5U19A2A4SdaSa4Sa4S7Sd9Sa4Sa7R1A1Sa6VS;A1A3A1Lp;Sa6G5A1A3A4").

Definition SC_0 : sstate := ltac:(let x := eval vm_compute in (SCz 0) in exact x).
Lemma SC_0_eq : SCz 0 = SC_0. Proof. vm_cast_no_check (@eq_refl sstate SC_0). Qed.
Definition MRC_0 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8SaS1A5").
Definition MRC_0__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8SaS1A5").
Definition RC_0 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_0__f in exact x).
Lemma MRC_0_c : MRC_0 = RC_0. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_0 MRC_0__f. Qed.
Lemma runC_0 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8SaS1A5S6aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_0 true) MRC_0 RC_0 (@eq_refl _ (sym_run segs 500 CUTS_C SC_0 true)) MRC_0_c). Qed.
Definition LC_0 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_0) in exact x).
Lemma LC_0_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S3aA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S6G0A1A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_1 : sstate := ltac:(let x := eval vm_compute in (SCz 1) in exact x).
Lemma SC_1_eq : SCz 1 = SC_1. Proof. vm_cast_no_check (@eq_refl sstate SC_1). Qed.
Definition MRC_1 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8SbS1A5").
Definition MRC_1__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8SbS1A5").
Definition RC_1 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_1__f in exact x).
Lemma MRC_1_c : MRC_1 = RC_1. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_1 MRC_1__f. Qed.
Lemma runC_1 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8SbS1A5S6bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_1 true) MRC_1 RC_1 (@eq_refl _ (sym_run segs 500 CUTS_C SC_1 true)) MRC_1_c). Qed.
Definition LC_1 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_1) in exact x).
Lemma LC_1_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S3bA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_2 : sstate := ltac:(let x := eval vm_compute in (SCz 2) in exact x).
Lemma SC_2_eq : SCz 2 = SC_2. Proof. vm_cast_no_check (@eq_refl sstate SC_2). Qed.
Definition MRC_2 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S16S1A5").
Definition MRC_2__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S16S1A5").
Definition RC_2 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_2__f in exact x).
Lemma MRC_2_c : MRC_2 = RC_2. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_2 MRC_2__f. Qed.
Lemma runC_2 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S16S1A5S76A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_2 true) MRC_2 RC_2 (@eq_refl _ (sym_run segs 500 CUTS_C SC_2 true)) MRC_2_c). Qed.
Definition LC_2 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_2) in exact x).
Lemma LC_2_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S46A4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_3 : sstate := ltac:(let x := eval vm_compute in (SCz 3) in exact x).
Lemma SC_3_eq : SCz 3 = SC_3. Proof. vm_cast_no_check (@eq_refl sstate SC_3). Qed.
Definition MRC_3 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S21S1A5").
Definition MRC_3__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S21S1A5").
Definition RC_3 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_3__f in exact x).
Lemma MRC_3_c : MRC_3 = RC_3. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_3 MRC_3__f. Qed.
Lemma runC_3 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S21S1A5S81A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_3 true) MRC_3 RC_3 (@eq_refl _ (sym_run segs 500 CUTS_C SC_3 true)) MRC_3_c). Qed.
Definition LC_3 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_3) in exact x).
Lemma LC_3_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S51A4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_4 : sstate := ltac:(let x := eval vm_compute in (SCz 4) in exact x).
Lemma SC_4_eq : SCz 4 = SC_4. Proof. vm_cast_no_check (@eq_refl sstate SC_4). Qed.
Definition MRC_4 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S2cS1A5").
Definition MRC_4__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S2cS1A5").
Definition RC_4 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_4__f in exact x).
Lemma MRC_4_c : MRC_4 = RC_4. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_4 MRC_4__f. Qed.
Lemma runC_4 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S2cS1A5S8cA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_4 true) MRC_4 RC_4 (@eq_refl _ (sym_run segs 500 CUTS_C SC_4 true)) MRC_4_c). Qed.
Definition LC_4 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_4) in exact x).
Lemma LC_4_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S5cA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_5 : sstate := ltac:(let x := eval vm_compute in (SCz 5) in exact x).
Lemma SC_5_eq : SCz 5 = SC_5. Proof. vm_cast_no_check (@eq_refl sstate SC_5). Qed.
Definition MRC_5 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S35S1A5").
Definition MRC_5__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S35S1A5").
Definition RC_5 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_5__f in exact x).
Lemma MRC_5_c : MRC_5 = RC_5. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_5 MRC_5__f. Qed.
Lemma runC_5 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S35S1A5S95A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_5 true) MRC_5 RC_5 (@eq_refl _ (sym_run segs 500 CUTS_C SC_5 true)) MRC_5_c). Qed.
Definition LC_5 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_5) in exact x).
Lemma LC_5_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S65A4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_6 : sstate := ltac:(let x := eval vm_compute in (SCz 6) in exact x).
Lemma SC_6_eq : SCz 6 = SC_6. Proof. vm_cast_no_check (@eq_refl sstate SC_6). Qed.
Definition MRC_6 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S36S1A5").
Definition MRC_6__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S36S1A5").
Definition RC_6 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_6__f in exact x).
Lemma MRC_6_c : MRC_6 = RC_6. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_6 MRC_6__f. Qed.
Lemma runC_6 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S36S1A5S96A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_6 true) MRC_6 RC_6 (@eq_refl _ (sym_run segs 500 CUTS_C SC_6 true)) MRC_6_c). Qed.
Definition LC_6 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_6) in exact x).
Lemma LC_6_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S66A4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_7 : sstate := ltac:(let x := eval vm_compute in (SCz 7) in exact x).
Lemma SC_7_eq : SCz 7 = SC_7. Proof. vm_cast_no_check (@eq_refl sstate SC_7). Qed.
Definition MRC_7 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S37S1A5").
Definition MRC_7__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S37S1A5").
Definition RC_7 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_7__f in exact x).
Lemma MRC_7_c : MRC_7 = RC_7. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_7 MRC_7__f. Qed.
Lemma runC_7 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S37S1A5S97A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_7 true) MRC_7 RC_7 (@eq_refl _ (sym_run segs 500 CUTS_C SC_7 true)) MRC_7_c). Qed.
Definition LC_7 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_7) in exact x).
Lemma LC_7_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S67A4S0G0S4S9bS9dZ21538S9fA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_8 : sstate := ltac:(let x := eval vm_compute in (SCz 8) in exact x).
Lemma SC_8_eq : SCz 8 = SC_8. Proof. vm_cast_no_check (@eq_refl sstate SC_8). Qed.
Definition MRC_8 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S38S1A5").
Definition MRC_8__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S38S1A5").
Definition RC_8 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_8__f in exact x).
Lemma MRC_8_c : MRC_8 = RC_8. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_8 MRC_8__f. Qed.
Lemma runC_8 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S38S1A5S98A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_8 true) MRC_8 RC_8 (@eq_refl _ (sym_run segs 500 CUTS_C SC_8 true)) MRC_8_c). Qed.
Definition LC_8 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_8) in exact x).
Lemma LC_8_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S68A4S0G0S4S9bS9dZ21538S9fA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_9 : sstate := ltac:(let x := eval vm_compute in (SCz 9) in exact x).
Lemma SC_9_eq : SCz 9 = SC_9. Proof. vm_cast_no_check (@eq_refl sstate SC_9). Qed.
Definition MRC_9 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S39S1A5").
Definition MRC_9__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S39S1A5").
Definition RC_9 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_9__f in exact x).
Lemma MRC_9_c : MRC_9 = RC_9. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_9 MRC_9__f. Qed.
Lemma runC_9 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S39S1A5S99A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_9 true) MRC_9 RC_9 (@eq_refl _ (sym_run segs 500 CUTS_C SC_9 true)) MRC_9_c). Qed.
Definition LC_9 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_9) in exact x).
Lemma LC_9_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S69A4S0G0S4S9bS9dZ21538S9fA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_10 : sstate := ltac:(let x := eval vm_compute in (SCz 10) in exact x).
Lemma SC_10_eq : SCz 10 = SC_10. Proof. vm_cast_no_check (@eq_refl sstate SC_10). Qed.
Definition MRC_10 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8ScS1A5").
Definition MRC_10__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8ScS1A5").
Definition RC_10 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_10__f in exact x).
Lemma MRC_10_c : MRC_10 = RC_10. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_10 MRC_10__f. Qed.
Lemma runC_10 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8ScS1A5S6cA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_10 true) MRC_10 RC_10 (@eq_refl _ (sym_run segs 500 CUTS_C SC_10 true)) MRC_10_c). Qed.
Definition LC_10 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_10) in exact x).
Lemma LC_10_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S3cA4S0G0S4S9bS9dZ21538S9fA4S0G0S4S9bS9dZ2126cS9fA4M1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_11 : sstate := ltac:(let x := eval vm_compute in (SCz 11) in exact x).
Lemma SC_11_eq : SCz 11 = SC_11. Proof. vm_cast_no_check (@eq_refl sstate SC_11). Qed.
Definition MRC_11 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8SdS1A5").
Definition MRC_11__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8SdS1A5").
Definition RC_11 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_11__f in exact x).
Lemma MRC_11_c : MRC_11 = RC_11. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_11 MRC_11__f. Qed.
Lemma runC_11 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8SdS1A5S6dA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_11 true) MRC_11 RC_11 (@eq_refl _ (sym_run segs 500 CUTS_C SC_11 true)) MRC_11_c). Qed.
Definition LC_11 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_11) in exact x).
Lemma LC_11_shape : ltac2:(tb__ "0|3|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S3dA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0S4S9bS9dZ2126cS9fA4M2S0G0G2S0G0G2S0G0G2S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_12 : sstate := ltac:(let x := eval vm_compute in (SCz 12) in exact x).
Lemma SC_12_eq : SCz 12 = SC_12. Proof. vm_cast_no_check (@eq_refl sstate SC_12). Qed.
Definition MRC_12 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8SeS1A5").
Definition MRC_12__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8SeS1A5").
Definition RC_12 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_12__f in exact x).
Lemma MRC_12_c : MRC_12 = RC_12. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_12 MRC_12__f. Qed.
Lemma runC_12 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8SeS1A5S6eA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_12 true) MRC_12 RC_12 (@eq_refl _ (sym_run segs 500 CUTS_C SC_12 true)) MRC_12_c). Qed.
Definition LC_12 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_12) in exact x).
Lemma LC_12_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S3eA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0S4S9bS9dZ2126cS9fA4S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_13 : sstate := ltac:(let x := eval vm_compute in (SCz 13) in exact x).
Lemma SC_13_eq : SCz 13 = SC_13. Proof. vm_cast_no_check (@eq_refl sstate SC_13). Qed.
Definition MRC_13 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8SfS1A5").
Definition MRC_13__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8SfS1A5").
Definition RC_13 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_13__f in exact x).
Lemma MRC_13_c : MRC_13 = RC_13. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_13 MRC_13__f. Qed.
Lemma runC_13 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8SfS1A5S6fA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_13 true) MRC_13 RC_13 (@eq_refl _ (sym_run segs 500 CUTS_C SC_13 true)) MRC_13_c). Qed.
Definition LC_13 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_13) in exact x).
Lemma LC_13_shape : ltac2:(tb__ "0|3|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S3fA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0S4S9bS9dZ2126cS9fA4M2S0G0G2S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_14 : sstate := ltac:(let x := eval vm_compute in (SCz 14) in exact x).
Lemma SC_14_eq : SCz 14 = SC_14. Proof. vm_cast_no_check (@eq_refl sstate SC_14). Qed.
Definition MRC_14 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S10S1A5").
Definition MRC_14__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S10S1A5").
Definition RC_14 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_14__f in exact x).
Lemma MRC_14_c : MRC_14 = RC_14. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_14 MRC_14__f. Qed.
Lemma runC_14 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S10S1A5S70A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_14 true) MRC_14 RC_14 (@eq_refl _ (sym_run segs 500 CUTS_C SC_14 true)) MRC_14_c). Qed.
Definition LC_14 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_14) in exact x).
Lemma LC_14_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S40A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0S4S9bS9dZ2126cS9fA4S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_15 : sstate := ltac:(let x := eval vm_compute in (SCz 15) in exact x).
Lemma SC_15_eq : SCz 15 = SC_15. Proof. vm_cast_no_check (@eq_refl sstate SC_15). Qed.
Definition MRC_15 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S11S1A5").
Definition MRC_15__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S11S1A5").
Definition RC_15 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_15__f in exact x).
Lemma MRC_15_c : MRC_15 = RC_15. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_15 MRC_15__f. Qed.
Lemma runC_15 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S11S1A5S71A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_15 true) MRC_15 RC_15 (@eq_refl _ (sym_run segs 500 CUTS_C SC_15 true)) MRC_15_c). Qed.
Definition LC_15 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_15) in exact x).
Lemma LC_15_shape : ltac2:(tb__ "0|3|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S41A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0S4S9bS9dZ2126cS9fA4M2S0G0G2S0G0G2S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_16 : sstate := ltac:(let x := eval vm_compute in (SCz 16) in exact x).
Lemma SC_16_eq : SCz 16 = SC_16. Proof. vm_cast_no_check (@eq_refl sstate SC_16). Qed.
Definition MRC_16 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S12S1A5").
Definition MRC_16__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S12S1A5").
Definition RC_16 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_16__f in exact x).
Lemma MRC_16_c : MRC_16 = RC_16. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_16 MRC_16__f. Qed.
Lemma runC_16 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S12S1A5S72A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_16 true) MRC_16 RC_16 (@eq_refl _ (sym_run segs 500 CUTS_C SC_16 true)) MRC_16_c). Qed.
Definition LC_16 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_16) in exact x).
Lemma LC_16_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S42A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_17 : sstate := ltac:(let x := eval vm_compute in (SCz 17) in exact x).
Lemma SC_17_eq : SCz 17 = SC_17. Proof. vm_cast_no_check (@eq_refl sstate SC_17). Qed.
Definition MRC_17 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S13S1A5").
Definition MRC_17__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S13S1A5").
Definition RC_17 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_17__f in exact x).
Lemma MRC_17_c : MRC_17 = RC_17. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_17 MRC_17__f. Qed.
Lemma runC_17 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S13S1A5S73A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_17 true) MRC_17 RC_17 (@eq_refl _ (sym_run segs 500 CUTS_C SC_17 true)) MRC_17_c). Qed.
Definition LC_17 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_17) in exact x).
Lemma LC_17_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S43A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0S4S9bS9dZ2126cS9fA4S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_18 : sstate := ltac:(let x := eval vm_compute in (SCz 18) in exact x).
Lemma SC_18_eq : SCz 18 = SC_18. Proof. vm_cast_no_check (@eq_refl sstate SC_18). Qed.
Definition MRC_18 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S14S1A5").
Definition MRC_18__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S14S1A5").
Definition RC_18 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_18__f in exact x).
Lemma MRC_18_c : MRC_18 = RC_18. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_18 MRC_18__f. Qed.
Lemma runC_18 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S14S1A5S74A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_18 true) MRC_18 RC_18 (@eq_refl _ (sym_run segs 500 CUTS_C SC_18 true)) MRC_18_c). Qed.
Definition LC_18 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_18) in exact x).
Lemma LC_18_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S44A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_19 : sstate := ltac:(let x := eval vm_compute in (SCz 19) in exact x).
Lemma SC_19_eq : SCz 19 = SC_19. Proof. vm_cast_no_check (@eq_refl sstate SC_19). Qed.
Definition MRC_19 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S15S1A5").
Definition MRC_19__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S15S1A5").
Definition RC_19 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_19__f in exact x).
Lemma MRC_19_c : MRC_19 = RC_19. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_19 MRC_19__f. Qed.
Lemma runC_19 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S15S1A5S75A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_19 true) MRC_19 RC_19 (@eq_refl _ (sym_run segs 500 CUTS_C SC_19 true)) MRC_19_c). Qed.
Definition LC_19 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_19) in exact x).
Lemma LC_19_shape : ltac2:(tb__ "0|3|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S45A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0S4S9bS9dZ2126cS9fA4M2S0G0G2S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_20 : sstate := ltac:(let x := eval vm_compute in (SCz 20) in exact x).
Lemma SC_20_eq : SCz 20 = SC_20. Proof. vm_cast_no_check (@eq_refl sstate SC_20). Qed.
Definition MRC_20 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S17S1A5").
Definition MRC_20__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S17S1A5").
Definition RC_20 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_20__f in exact x).
Lemma MRC_20_c : MRC_20 = RC_20. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_20 MRC_20__f. Qed.
Lemma runC_20 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S17S1A5S77A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_20 true) MRC_20 RC_20 (@eq_refl _ (sym_run segs 500 CUTS_C SC_20 true)) MRC_20_c). Qed.
Definition LC_20 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_20) in exact x).
Lemma LC_20_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S47A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_21 : sstate := ltac:(let x := eval vm_compute in (SCz 21) in exact x).
Lemma SC_21_eq : SCz 21 = SC_21. Proof. vm_cast_no_check (@eq_refl sstate SC_21). Qed.
Definition MRC_21 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S18S1A5").
Definition MRC_21__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S18S1A5").
Definition RC_21 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_21__f in exact x).
Lemma MRC_21_c : MRC_21 = RC_21. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_21 MRC_21__f. Qed.
Lemma runC_21 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S18S1A5S78A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_21 true) MRC_21 RC_21 (@eq_refl _ (sym_run segs 500 CUTS_C SC_21 true)) MRC_21_c). Qed.
Definition LC_21 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_21) in exact x).
Lemma LC_21_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S48A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_22 : sstate := ltac:(let x := eval vm_compute in (SCz 22) in exact x).
Lemma SC_22_eq : SCz 22 = SC_22. Proof. vm_cast_no_check (@eq_refl sstate SC_22). Qed.
Definition MRC_22 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S19S1A5").
Definition MRC_22__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S19S1A5").
Definition RC_22 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_22__f in exact x).
Lemma MRC_22_c : MRC_22 = RC_22. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_22 MRC_22__f. Qed.
Lemma runC_22 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S19S1A5S79A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_22 true) MRC_22 RC_22 (@eq_refl _ (sym_run segs 500 CUTS_C SC_22 true)) MRC_22_c). Qed.
Definition LC_22 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_22) in exact x).
Lemma LC_22_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S49A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_23 : sstate := ltac:(let x := eval vm_compute in (SCz 23) in exact x).
Lemma SC_23_eq : SCz 23 = SC_23. Proof. vm_cast_no_check (@eq_refl sstate SC_23). Qed.
Definition MRC_23 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S1aS1A5").
Definition MRC_23__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S1aS1A5").
Definition RC_23 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_23__f in exact x).
Lemma MRC_23_c : MRC_23 = RC_23. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_23 MRC_23__f. Qed.
Lemma runC_23 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S1aS1A5S7aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_23 true) MRC_23 RC_23 (@eq_refl _ (sym_run segs 500 CUTS_C SC_23 true)) MRC_23_c). Qed.
Definition LC_23 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_23) in exact x).
Lemma LC_23_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S4aA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_24 : sstate := ltac:(let x := eval vm_compute in (SCz 24) in exact x).
Lemma SC_24_eq : SCz 24 = SC_24. Proof. vm_cast_no_check (@eq_refl sstate SC_24). Qed.
Definition MRC_24 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S1bS1A5").
Definition MRC_24__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S1bS1A5").
Definition RC_24 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_24__f in exact x).
Lemma MRC_24_c : MRC_24 = RC_24. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_24 MRC_24__f. Qed.
Lemma runC_24 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S1bS1A5S7bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_24 true) MRC_24 RC_24 (@eq_refl _ (sym_run segs 500 CUTS_C SC_24 true)) MRC_24_c). Qed.
Definition LC_24 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_24) in exact x).
Lemma LC_24_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S4bA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_25 : sstate := ltac:(let x := eval vm_compute in (SCz 25) in exact x).
Lemma SC_25_eq : SCz 25 = SC_25. Proof. vm_cast_no_check (@eq_refl sstate SC_25). Qed.
Definition MRC_25 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S1cS1A5").
Definition MRC_25__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S1cS1A5").
Definition RC_25 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_25__f in exact x).
Lemma MRC_25_c : MRC_25 = RC_25. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_25 MRC_25__f. Qed.
Lemma runC_25 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S1cS1A5S7cA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_25 true) MRC_25 RC_25 (@eq_refl _ (sym_run segs 500 CUTS_C SC_25 true)) MRC_25_c). Qed.
Definition LC_25 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_25) in exact x).
Lemma LC_25_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S4cA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_26 : sstate := ltac:(let x := eval vm_compute in (SCz 26) in exact x).
Lemma SC_26_eq : SCz 26 = SC_26. Proof. vm_cast_no_check (@eq_refl sstate SC_26). Qed.
Definition MRC_26 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S1dS1A5").
Definition MRC_26__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S1dS1A5").
Definition RC_26 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_26__f in exact x).
Lemma MRC_26_c : MRC_26 = RC_26. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_26 MRC_26__f. Qed.
Lemma runC_26 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S1dS1A5S7dA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_26 true) MRC_26 RC_26 (@eq_refl _ (sym_run segs 500 CUTS_C SC_26 true)) MRC_26_c). Qed.
Definition LC_26 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_26) in exact x).
Lemma LC_26_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S4dA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_27 : sstate := ltac:(let x := eval vm_compute in (SCz 27) in exact x).
Lemma SC_27_eq : SCz 27 = SC_27. Proof. vm_cast_no_check (@eq_refl sstate SC_27). Qed.
Definition MRC_27 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S1eS1A5").
Definition MRC_27__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S1eS1A5").
Definition RC_27 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_27__f in exact x).
Lemma MRC_27_c : MRC_27 = RC_27. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_27 MRC_27__f. Qed.
Lemma runC_27 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S1eS1A5S7eA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_27 true) MRC_27 RC_27 (@eq_refl _ (sym_run segs 500 CUTS_C SC_27 true)) MRC_27_c). Qed.
Definition LC_27 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_27) in exact x).
Lemma LC_27_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S4eA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_28 : sstate := ltac:(let x := eval vm_compute in (SCz 28) in exact x).
Lemma SC_28_eq : SCz 28 = SC_28. Proof. vm_cast_no_check (@eq_refl sstate SC_28). Qed.
Definition MRC_28 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S1fS1A5").
Definition MRC_28__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S1fS1A5").
Definition RC_28 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_28__f in exact x).
Lemma MRC_28_c : MRC_28 = RC_28. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_28 MRC_28__f. Qed.
Lemma runC_28 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S1fS1A5S7fA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_28 true) MRC_28 RC_28 (@eq_refl _ (sym_run segs 500 CUTS_C SC_28 true)) MRC_28_c). Qed.
Definition LC_28 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_28) in exact x).
Lemma LC_28_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S4fA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_29 : sstate := ltac:(let x := eval vm_compute in (SCz 29) in exact x).
Lemma SC_29_eq : SCz 29 = SC_29. Proof. vm_cast_no_check (@eq_refl sstate SC_29). Qed.
Definition MRC_29 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S20S1A5").
Definition MRC_29__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S20S1A5").
Definition RC_29 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_29__f in exact x).
Lemma MRC_29_c : MRC_29 = RC_29. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_29 MRC_29__f. Qed.
Lemma runC_29 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S20S1A5S80A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_29 true) MRC_29 RC_29 (@eq_refl _ (sym_run segs 500 CUTS_C SC_29 true)) MRC_29_c). Qed.
Definition LC_29 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_29) in exact x).
Lemma LC_29_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S50A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_30 : sstate := ltac:(let x := eval vm_compute in (SCz 30) in exact x).
Lemma SC_30_eq : SCz 30 = SC_30. Proof. vm_cast_no_check (@eq_refl sstate SC_30). Qed.
Definition MRC_30 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S22S1A5").
Definition MRC_30__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S22S1A5").
Definition RC_30 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_30__f in exact x).
Lemma MRC_30_c : MRC_30 = RC_30. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_30 MRC_30__f. Qed.
Lemma runC_30 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S22S1A5S82A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_30 true) MRC_30 RC_30 (@eq_refl _ (sym_run segs 500 CUTS_C SC_30 true)) MRC_30_c). Qed.
Definition LC_30 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_30) in exact x).
Lemma LC_30_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S52A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_31 : sstate := ltac:(let x := eval vm_compute in (SCz 31) in exact x).
Lemma SC_31_eq : SCz 31 = SC_31. Proof. vm_cast_no_check (@eq_refl sstate SC_31). Qed.
Definition MRC_31 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S23S1A5").
Definition MRC_31__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S23S1A5").
Definition RC_31 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_31__f in exact x).
Lemma MRC_31_c : MRC_31 = RC_31. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_31 MRC_31__f. Qed.
Lemma runC_31 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S23S1A5S83A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_31 true) MRC_31 RC_31 (@eq_refl _ (sym_run segs 500 CUTS_C SC_31 true)) MRC_31_c). Qed.
Definition LC_31 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_31) in exact x).
Lemma LC_31_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S53A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_32 : sstate := ltac:(let x := eval vm_compute in (SCz 32) in exact x).
Lemma SC_32_eq : SCz 32 = SC_32. Proof. vm_cast_no_check (@eq_refl sstate SC_32). Qed.
Definition MRC_32 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S24S1A5").
Definition MRC_32__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S24S1A5").
Definition RC_32 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_32__f in exact x).
Lemma MRC_32_c : MRC_32 = RC_32. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_32 MRC_32__f. Qed.
Lemma runC_32 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S24S1A5S84A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_32 true) MRC_32 RC_32 (@eq_refl _ (sym_run segs 500 CUTS_C SC_32 true)) MRC_32_c). Qed.
Definition LC_32 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_32) in exact x).
Lemma LC_32_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S54A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_33 : sstate := ltac:(let x := eval vm_compute in (SCz 33) in exact x).
Lemma SC_33_eq : SCz 33 = SC_33. Proof. vm_cast_no_check (@eq_refl sstate SC_33). Qed.
Definition MRC_33 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S25S1A5").
Definition MRC_33__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S25S1A5").
Definition RC_33 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_33__f in exact x).
Lemma MRC_33_c : MRC_33 = RC_33. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_33 MRC_33__f. Qed.
Lemma runC_33 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S25S1A5S85A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_33 true) MRC_33 RC_33 (@eq_refl _ (sym_run segs 500 CUTS_C SC_33 true)) MRC_33_c). Qed.
Definition LC_33 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_33) in exact x).
Lemma LC_33_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S55A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_34 : sstate := ltac:(let x := eval vm_compute in (SCz 34) in exact x).
Lemma SC_34_eq : SCz 34 = SC_34. Proof. vm_cast_no_check (@eq_refl sstate SC_34). Qed.
Definition MRC_34 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S26S1A5").
Definition MRC_34__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S26S1A5").
Definition RC_34 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_34__f in exact x).
Lemma MRC_34_c : MRC_34 = RC_34. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_34 MRC_34__f. Qed.
Lemma runC_34 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S26S1A5S86A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_34 true) MRC_34 RC_34 (@eq_refl _ (sym_run segs 500 CUTS_C SC_34 true)) MRC_34_c). Qed.
Definition LC_34 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_34) in exact x).
Lemma LC_34_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S56A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_35 : sstate := ltac:(let x := eval vm_compute in (SCz 35) in exact x).
Lemma SC_35_eq : SCz 35 = SC_35. Proof. vm_cast_no_check (@eq_refl sstate SC_35). Qed.
Definition MRC_35 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S27S1A5").
Definition MRC_35__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S27S1A5").
Definition RC_35 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_35__f in exact x).
Lemma MRC_35_c : MRC_35 = RC_35. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_35 MRC_35__f. Qed.
Lemma runC_35 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S27S1A5S87A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_35 true) MRC_35 RC_35 (@eq_refl _ (sym_run segs 500 CUTS_C SC_35 true)) MRC_35_c). Qed.
Definition LC_35 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_35) in exact x).
Lemma LC_35_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S57A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_36 : sstate := ltac:(let x := eval vm_compute in (SCz 36) in exact x).
Lemma SC_36_eq : SCz 36 = SC_36. Proof. vm_cast_no_check (@eq_refl sstate SC_36). Qed.
Definition MRC_36 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S28S1A5").
Definition MRC_36__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S28S1A5").
Definition RC_36 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_36__f in exact x).
Lemma MRC_36_c : MRC_36 = RC_36. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_36 MRC_36__f. Qed.
Lemma runC_36 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S28S1A5S88A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_36 true) MRC_36 RC_36 (@eq_refl _ (sym_run segs 500 CUTS_C SC_36 true)) MRC_36_c). Qed.
Definition LC_36 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_36) in exact x).
Lemma LC_36_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S58A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_37 : sstate := ltac:(let x := eval vm_compute in (SCz 37) in exact x).
Lemma SC_37_eq : SCz 37 = SC_37. Proof. vm_cast_no_check (@eq_refl sstate SC_37). Qed.
Definition MRC_37 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S29S1A5").
Definition MRC_37__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S29S1A5").
Definition RC_37 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_37__f in exact x).
Lemma MRC_37_c : MRC_37 = RC_37. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_37 MRC_37__f. Qed.
Lemma runC_37 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S29S1A5S89A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_37 true) MRC_37 RC_37 (@eq_refl _ (sym_run segs 500 CUTS_C SC_37 true)) MRC_37_c). Qed.
Definition LC_37 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_37) in exact x).
Lemma LC_37_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S59A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_38 : sstate := ltac:(let x := eval vm_compute in (SCz 38) in exact x).
Lemma SC_38_eq : SCz 38 = SC_38. Proof. vm_cast_no_check (@eq_refl sstate SC_38). Qed.
Definition MRC_38 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S2aS1A5").
Definition MRC_38__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S2aS1A5").
Definition RC_38 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_38__f in exact x).
Lemma MRC_38_c : MRC_38 = RC_38. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_38 MRC_38__f. Qed.
Lemma runC_38 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S2aS1A5S8aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_38 true) MRC_38 RC_38 (@eq_refl _ (sym_run segs 500 CUTS_C SC_38 true)) MRC_38_c). Qed.
Definition LC_38 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_38) in exact x).
Lemma LC_38_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S5aA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_39 : sstate := ltac:(let x := eval vm_compute in (SCz 39) in exact x).
Lemma SC_39_eq : SCz 39 = SC_39. Proof. vm_cast_no_check (@eq_refl sstate SC_39). Qed.
Definition MRC_39 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S2bS1A5").
Definition MRC_39__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S2bS1A5").
Definition RC_39 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_39__f in exact x).
Lemma MRC_39_c : MRC_39 = RC_39. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_39 MRC_39__f. Qed.
Lemma runC_39 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S2bS1A5S8bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_39 true) MRC_39 RC_39 (@eq_refl _ (sym_run segs 500 CUTS_C SC_39 true)) MRC_39_c). Qed.
Definition LC_39 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_39) in exact x).
Lemma LC_39_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S5bA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_40 : sstate := ltac:(let x := eval vm_compute in (SCz 40) in exact x).
Lemma SC_40_eq : SCz 40 = SC_40. Proof. vm_cast_no_check (@eq_refl sstate SC_40). Qed.
Definition MRC_40 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S2dS1A5").
Definition MRC_40__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S2dS1A5").
Definition RC_40 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_40__f in exact x).
Lemma MRC_40_c : MRC_40 = RC_40. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_40 MRC_40__f. Qed.
Lemma runC_40 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S2dS1A5S8dA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_40 true) MRC_40 RC_40 (@eq_refl _ (sym_run segs 500 CUTS_C SC_40 true)) MRC_40_c). Qed.
Definition LC_40 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_40) in exact x).
Lemma LC_40_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S5dA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_41 : sstate := ltac:(let x := eval vm_compute in (SCz 41) in exact x).
Lemma SC_41_eq : SCz 41 = SC_41. Proof. vm_cast_no_check (@eq_refl sstate SC_41). Qed.
Definition MRC_41 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S2eS1A5").
Definition MRC_41__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S2eS1A5").
Definition RC_41 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_41__f in exact x).
Lemma MRC_41_c : MRC_41 = RC_41. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_41 MRC_41__f. Qed.
Lemma runC_41 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S2eS1A5S8eA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_41 true) MRC_41 RC_41 (@eq_refl _ (sym_run segs 500 CUTS_C SC_41 true)) MRC_41_c). Qed.
Definition LC_41 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_41) in exact x).
Lemma LC_41_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S5eA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_42 : sstate := ltac:(let x := eval vm_compute in (SCz 42) in exact x).
Lemma SC_42_eq : SCz 42 = SC_42. Proof. vm_cast_no_check (@eq_refl sstate SC_42). Qed.
Definition MRC_42 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S2fS1A5").
Definition MRC_42__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S2fS1A5").
Definition RC_42 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_42__f in exact x).
Lemma MRC_42_c : MRC_42 = RC_42. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_42 MRC_42__f. Qed.
Lemma runC_42 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S2fS1A5S8fA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_42 true) MRC_42 RC_42 (@eq_refl _ (sym_run segs 500 CUTS_C SC_42 true)) MRC_42_c). Qed.
Definition LC_42 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_42) in exact x).
Lemma LC_42_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S5fA4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_43 : sstate := ltac:(let x := eval vm_compute in (SCz 43) in exact x).
Lemma SC_43_eq : SCz 43 = SC_43. Proof. vm_cast_no_check (@eq_refl sstate SC_43). Qed.
Definition MRC_43 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S30S1A5").
Definition MRC_43__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S30S1A5").
Definition RC_43 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_43__f in exact x).
Lemma MRC_43_c : MRC_43 = RC_43. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_43 MRC_43__f. Qed.
Lemma runC_43 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S30S1A5S90A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_43 true) MRC_43 RC_43 (@eq_refl _ (sym_run segs 500 CUTS_C SC_43 true)) MRC_43_c). Qed.
Definition LC_43 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_43) in exact x).
Lemma LC_43_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S60A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_44 : sstate := ltac:(let x := eval vm_compute in (SCz 44) in exact x).
Lemma SC_44_eq : SCz 44 = SC_44. Proof. vm_cast_no_check (@eq_refl sstate SC_44). Qed.
Definition MRC_44 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S31S1A5").
Definition MRC_44__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S31S1A5").
Definition RC_44 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_44__f in exact x).
Lemma MRC_44_c : MRC_44 = RC_44. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_44 MRC_44__f. Qed.
Lemma runC_44 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S31S1A5S91A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_44 true) MRC_44 RC_44 (@eq_refl _ (sym_run segs 500 CUTS_C SC_44 true)) MRC_44_c). Qed.
Definition LC_44 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_44) in exact x).
Lemma LC_44_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S61A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_45 : sstate := ltac:(let x := eval vm_compute in (SCz 45) in exact x).
Lemma SC_45_eq : SCz 45 = SC_45. Proof. vm_cast_no_check (@eq_refl sstate SC_45). Qed.
Definition MRC_45 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S32S1A5").
Definition MRC_45__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S32S1A5").
Definition RC_45 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_45__f in exact x).
Lemma MRC_45_c : MRC_45 = RC_45. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_45 MRC_45__f. Qed.
Lemma runC_45 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S32S1A5S92A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_45 true) MRC_45 RC_45 (@eq_refl _ (sym_run segs 500 CUTS_C SC_45 true)) MRC_45_c). Qed.
Definition LC_45 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_45) in exact x).
Lemma LC_45_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S62A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_46 : sstate := ltac:(let x := eval vm_compute in (SCz 46) in exact x).
Lemma SC_46_eq : SCz 46 = SC_46. Proof. vm_cast_no_check (@eq_refl sstate SC_46). Qed.
Definition MRC_46 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S33S1A5").
Definition MRC_46__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S33S1A5").
Definition RC_46 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_46__f in exact x).
Lemma MRC_46_c : MRC_46 = RC_46. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_46 MRC_46__f. Qed.
Lemma runC_46 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S33S1A5S93A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_46 true) MRC_46 RC_46 (@eq_refl _ (sym_run segs 500 CUTS_C SC_46 true)) MRC_46_c). Qed.
Definition LC_46 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_46) in exact x).
Lemma LC_46_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S63A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S6G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition SC_47 : sstate := ltac:(let x := eval vm_compute in (SCz 47) in exact x).
Lemma SC_47_eq : SCz 47 = SC_47. Proof. vm_cast_no_check (@eq_refl sstate SC_47). Qed.
Definition MRC_47 : option (list leaf) := ltac2:(tb__ "0|0|
S9cS9U1f4S8S34S1A5").
Definition MRC_47__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8S9U1f4S8S34S1A5").
Definition RC_47 : option (list leaf) := ltac:(let x := eval vm_compute in MRC_47__f in exact x).
Lemma MRC_47_c : MRC_47 = RC_47. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRC_47 MRC_47__f. Qed.
Lemma runC_47 : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cS9U1f4S8S34S1A5S94A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_C SC_47 true) MRC_47 RC_47 (@eq_refl _ (sym_run segs 500 CUTS_C SC_47 true)) MRC_47_c). Qed.
Definition LC_47 : list leaf := ltac:(let x := eval vm_compute in (unopt RC_47) in exact x).
Lemma LC_47_shape : ltac2:(tb__ "0|2|
S9aS2S3S9bS9dA2M0A1SabS9eG0Sa9S64A4S0G0S4S9bS9dZ21538S9fA4M1S0G0G1S0G0G1S0G0G1S0G0G1S0G0G1S6G0A1A3A3A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
End Mal_agrp_rC.

Module Mal_agrp_rMC.

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
Definition CUTS_MC : list Z := [0x218fc; 0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
Sa0SacS9eVi;Vl;Sa2Vd;Sa1A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S3S3S3S3S3S3S3S9bS9dA2Sa3A2Sa3A2Sa3A2Sa3A2Sa3A2S2Sa4A1A2") := ltac2:(tb__ "0|6|
S4S3S3S3S3S3S3S9bS9dA2M0Sa3A2M1Sa3A2M2Sa3A2M3Sa3A2M4Sa3A2S2Sa4A1S4G4Sa3S4G3Sa3S4G2Sa3S4G1Sa3S4G0Sa3Sa9VL;A1SaaSa0VL;A1M5U13A2A4SaaG5UeA2A4SaaG5UaA2A4SaaG5UbA2A4SaaG5U19A2A4SdaSa4Sa4S7Sd9Sa4Sa7R1A1Sa6VS;A1A3A1Lp;Sa6G5A1A3A4").

Definition SMC_a : sstate := ltac:(let x := eval vm_compute in (SJB M1a) in exact x).
Lemma SMC_a_eq : ltac2:(tb__ "0|0|
S9aSa5Se1SdbA1Sd1A3"). Proof. vm_cast_no_check (@eq_refl sstate SMC_a). Qed.
Definition MRMC_a : option (list leaf) := ltac2:(tb__ "0|0|
S9cSd0U1f4ScfSd1S1A5").
Definition MRMC_a__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sd0U1f4ScfSd1S1A5").
Definition RMC_a : option (list leaf) := ltac:(let x := eval vm_compute in MRMC_a__f in exact x).
Lemma MRMC_a_c : MRMC_a = RMC_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMC_a MRMC_a__f. Qed.
Lemma runMC_a : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSd0U1f4ScfSd1S1A5Sd5A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MC SMC_a true) MRMC_a RMC_a (@eq_refl _ (sym_run segs 500 CUTS_MC SMC_a true)) MRMC_a_c). Qed.
Definition LMC_a : list leaf := ltac:(let x := eval vm_compute in (unopt RMC_a) in exact x).
Definition SMC_b : sstate := ltac:(let x := eval vm_compute in (SJB M1b) in exact x).
Lemma SMC_b_eq : ltac2:(tb__ "0|0|
S9aSa5Se1SdcA1Sd2A3"). Proof. vm_cast_no_check (@eq_refl sstate SMC_b). Qed.
Definition MRMC_b : option (list leaf) := ltac2:(tb__ "0|0|
S9cSd0U1f4ScfSd2S1A5").
Definition MRMC_b__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sd0U1f4ScfSd2S1A5").
Definition RMC_b : option (list leaf) := ltac:(let x := eval vm_compute in MRMC_b__f in exact x).
Lemma MRMC_b_c : MRMC_b = RMC_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMC_b MRMC_b__f. Qed.
Lemma runMC_b : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSd0U1f4ScfSd2S1A5Sd6A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MC SMC_b true) MRMC_b RMC_b (@eq_refl _ (sym_run segs 500 CUTS_MC SMC_b true)) MRMC_b_c). Qed.
Definition LMC_b : list leaf := ltac:(let x := eval vm_compute in (unopt RMC_b) in exact x).
Definition SMC_c : sstate := ltac:(let x := eval vm_compute in (SJB M1c) in exact x).
Lemma SMC_c_eq : ltac2:(tb__ "0|0|
S9aSa5Se1SddA1Sd3A3"). Proof. vm_cast_no_check (@eq_refl sstate SMC_c). Qed.
Definition MRMC_c : option (list leaf) := ltac2:(tb__ "0|0|
S9cSd0U1f4ScfSd3S1A5").
Definition MRMC_c__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sd0U1f4ScfSd3S1A5").
Definition RMC_c : option (list leaf) := ltac:(let x := eval vm_compute in MRMC_c__f in exact x).
Lemma MRMC_c_c : MRMC_c = RMC_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMC_c MRMC_c__f. Qed.
Lemma runMC_c : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSd0U1f4ScfSd3S1A5Sd7A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MC SMC_c true) MRMC_c RMC_c (@eq_refl _ (sym_run segs 500 CUTS_MC SMC_c true)) MRMC_c_c). Qed.
Definition LMC_c : list leaf := ltac:(let x := eval vm_compute in (unopt RMC_c) in exact x).
Definition SMC_d : sstate := ltac:(let x := eval vm_compute in (SJB M1d) in exact x).
Lemma SMC_d_eq : ltac2:(tb__ "0|0|
S9aSa5Se1SdeA1Sd4A3"). Proof. vm_cast_no_check (@eq_refl sstate SMC_d). Qed.
Definition MRMC_d : option (list leaf) := ltac2:(tb__ "0|0|
S9cSd0U1f4ScfSd4S1A5").
Definition MRMC_d__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sd0U1f4ScfSd4S1A5").
Definition RMC_d : option (list leaf) := ltac:(let x := eval vm_compute in MRMC_d__f in exact x).
Lemma MRMC_d_c : MRMC_d = RMC_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMC_d MRMC_d__f. Qed.
Lemma runMC_d : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSd0U1f4ScfSd4S1A5Sd8A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MC SMC_d true) MRMC_d RMC_d (@eq_refl _ (sym_run segs 500 CUTS_MC SMC_d true)) MRMC_d_c). Qed.
Definition LMC_d : list leaf := ltac:(let x := eval vm_compute in (unopt RMC_d) in exact x).
End Mal_agrp_rMC.

Module Mal_agrp_rMB.

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
Definition CUTS_MB : list Z := [0x218a0; 0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
Sa0SacS9eVi;Vl;Sa2Vd;Sa1A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S3S3S3S3S3S3S3S9bS9dA2Sa3A2Sa3A2Sa3A2Sa3A2Sa3A2S2Sa4A1A2") := ltac2:(tb__ "0|6|
S4S3S3S3S3S3S3S9bS9dA2M0Sa3A2M1Sa3A2M2Sa3A2M3Sa3A2M4Sa3A2S2Sa4A1S4G4Sa3S4G3Sa3S4G2Sa3S4G1Sa3S4G0Sa3Sa9VL;A1SaaSa0VL;A1M5U13A2A4SaaG5UeA2A4SaaG5UaA2A4SaaG5UbA2A4SaaG5U19A2A4SdaSa4Sa4S7Sd9Sa4Sa7R1A1Sa6VS;A1A3A1Lp;Sa6G5A1A3A4").

Definition SMB_a : sstate := ltac:(let x := eval vm_compute in (SJA M1a) in exact x).
Lemma SMB_a_eq : ltac2:(tb__ "0|0|
S9aSa5Se0SdbA1Sc7A3"). Proof. vm_cast_no_check (@eq_refl sstate SMB_a). Qed.
Definition MRMB_a : option (list leaf) := ltac2:(tb__ "0|0|
S9cSc6U1f4Sc5Sc7S1A5").
Definition MRMB_a__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sc6U1f4Sc5Sc7S1A5").
Definition RMB_a : option (list leaf) := ltac:(let x := eval vm_compute in MRMB_a__f in exact x).
Lemma MRMB_a_c : MRMB_a = RMB_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMB_a MRMB_a__f. Qed.
Lemma runMB_a : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSc6U1f4Sc5Sc7S1A5ScbA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MB SMB_a true) MRMB_a RMB_a (@eq_refl _ (sym_run segs 500 CUTS_MB SMB_a true)) MRMB_a_c). Qed.
Definition LMB_a : list leaf := ltac:(let x := eval vm_compute in (unopt RMB_a) in exact x).
Definition SMB_b : sstate := ltac:(let x := eval vm_compute in (SJA M1b) in exact x).
Lemma SMB_b_eq : ltac2:(tb__ "0|0|
S9aSa5Se0SdcA1Sc8A3"). Proof. vm_cast_no_check (@eq_refl sstate SMB_b). Qed.
Definition MRMB_b : option (list leaf) := ltac2:(tb__ "0|0|
S9cSc6U1f4Sc5Sc8S1A5").
Definition MRMB_b__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sc6U1f4Sc5Sc8S1A5").
Definition RMB_b : option (list leaf) := ltac:(let x := eval vm_compute in MRMB_b__f in exact x).
Lemma MRMB_b_c : MRMB_b = RMB_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMB_b MRMB_b__f. Qed.
Lemma runMB_b : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSc6U1f4Sc5Sc8S1A5SccA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MB SMB_b true) MRMB_b RMB_b (@eq_refl _ (sym_run segs 500 CUTS_MB SMB_b true)) MRMB_b_c). Qed.
Definition LMB_b : list leaf := ltac:(let x := eval vm_compute in (unopt RMB_b) in exact x).
Definition SMB_c : sstate := ltac:(let x := eval vm_compute in (SJA M1c) in exact x).
Lemma SMB_c_eq : ltac2:(tb__ "0|0|
S9aSa5Se0SddA1Sc9A3"). Proof. vm_cast_no_check (@eq_refl sstate SMB_c). Qed.
Definition MRMB_c : option (list leaf) := ltac2:(tb__ "0|0|
S9cSc6U1f4Sc5Sc9S1A5").
Definition MRMB_c__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sc6U1f4Sc5Sc9S1A5").
Definition RMB_c : option (list leaf) := ltac:(let x := eval vm_compute in MRMB_c__f in exact x).
Lemma MRMB_c_c : MRMB_c = RMB_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMB_c MRMB_c__f. Qed.
Lemma runMB_c : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSc6U1f4Sc5Sc9S1A5ScdA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MB SMB_c true) MRMB_c RMB_c (@eq_refl _ (sym_run segs 500 CUTS_MB SMB_c true)) MRMB_c_c). Qed.
Definition LMB_c : list leaf := ltac:(let x := eval vm_compute in (unopt RMB_c) in exact x).
Definition SMB_d : sstate := ltac:(let x := eval vm_compute in (SJA M1d) in exact x).
Lemma SMB_d_eq : ltac2:(tb__ "0|0|
S9aSa5Se0SdeA1ScaA3"). Proof. vm_cast_no_check (@eq_refl sstate SMB_d). Qed.
Definition MRMB_d : option (list leaf) := ltac2:(tb__ "0|0|
S9cSc6U1f4Sc5ScaS1A5").
Definition MRMB_d__f : option (list leaf) := ltac2:(tb__ "0|0|
Sa8Sc6U1f4Sc5ScaS1A5").
Definition RMB_d : option (list leaf) := ltac:(let x := eval vm_compute in MRMB_d__f in exact x).
Lemma MRMB_d_c : MRMB_d = RMB_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRMB_d MRMB_d__f. Qed.
Lemma runMB_d : ltac2:(tb__ "0|0|
S9aS5S2S9eA1A1S9cSc6U1f4Sc5ScaS1A5SceA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_MB SMB_d true) MRMB_d RMB_d (@eq_refl _ (sym_run segs 500 CUTS_MB SMB_d true)) MRMB_d_c). Qed.
Definition LMB_d : list leaf := ltac:(let x := eval vm_compute in (unopt RMB_d) in exact x).
End Mal_agrp_rMB.
