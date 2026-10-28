(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SAlu"; "SVar"; "sprop"; "SMd"; "SPUle"; "sprop_eqb"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "true"; "bool"; "nil"; "Some"; "false"; "option"; "snd"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "ALU_AND"; "ALU_SRL"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3"; "SN3s"; "factsN3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN"; "iaN"; "mWN"; "bzN"; "nstrd"; "zp"; "nidx"; "nokR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs"; "leafN_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "icnt0"; "zl2"; "zr2"; "ia_sc"; "rho2"; "ij"; "isize"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "IEC_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_errno"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "div"; "lt"; "pow"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv"; "prov"; "@stdpp.bitvector.definitions"; "bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT0"; "dN_0_30_L"; "dN_0_30_Z"; "dN_1_15_L"; "dN_1_15_Z"; "dN_1_31_L"; "dN_1_31_Z"; "dN_2_10_L"; "dN_2_10_Z"; "dN_2_20_L"; "dN_2_20_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT1"; "dN_3_15_L"; "dN_3_15_Z"; "dN_3_31_L"; "dN_3_31_Z"; "dN_3_7_L"; "dN_3_7_Z"; "dN_4_12_L"; "dN_4_12_Z"; "dN_4_6_L"; "dN_4_6_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT3"; "dN_6_18_L"; "dN_6_18_Z"; "dN_6_8_L"; "dN_6_8_Z"; "dN_7_15_L"; "dN_7_15_Z"; "dN_7_7_L"; "dN_7_7_Z"; "dN_8_6_L"; "dN_8_6_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT4"; "dN_10_5_L"; "dN_10_5_Z"; "dN_8_14_L"; "dN_8_14_Z"; "dN_9_12_L"; "dN_9_12_Z"; "dN_9_3_L"; "dN_9_3_Z"; "dN_9_6_L"; "dN_9_6_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN0"; "LN_0_30_L"; "LN_0_30_Z"; "LN_1_15_L"; "LN_1_15_Z"; "LN_1_31_L"; "LN_1_31_Z"; "LN_2_10_L"; "LN_2_10_Z"; "LN_2_20_L"; "LN_2_20_Z"; "SN_0_30_L"; "SN_0_30_Z"; "SN_1_15_L"; "SN_1_15_Z"; "SN_1_31_L"; "SN_1_31_Z"; "SN_2_10_L"; "SN_2_10_Z"; "SN_2_20_L"; "SN_2_20_Z";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN1"; "LN_3_15_L"; "LN_3_15_Z"; "LN_3_31_L"; "LN_3_31_Z"; "LN_3_7_L"; "LN_3_7_Z"; "LN_4_12_L"; "LN_4_12_Z"; "LN_4_6_L"; "LN_4_6_Z"; "SN_3_15_L"; "SN_3_15_Z"; "SN_3_31_L"; "SN_3_31_Z"; "SN_3_7_L"; "SN_3_7_Z"; "SN_4_12_L"; "SN_4_12_Z"; "SN_4_6_L"; "SN_4_6_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN3"; "LN_6_18_L"; "LN_6_18_Z"; "LN_6_8_L"; "LN_6_8_Z"; "LN_7_15_L"; "LN_7_15_Z"; "LN_7_7_L"; "LN_7_7_Z"; "LN_8_6_L"; "LN_8_6_Z"; "SN_6_18_L"; "SN_6_18_Z"; "SN_6_8_L"; "SN_6_8_Z"; "SN_7_15_L"; "SN_7_15_Z"; "SN_7_7_L"; "SN_7_7_Z"; "SN_8_6_L"; "SN_8_6_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN4"; "LN_10_5_L"; "LN_10_5_Z"; "LN_8_14_L"; "LN_8_14_Z"; "LN_9_12_L"; "LN_9_12_Z"; "LN_9_3_L"; "LN_9_3_Z"; "LN_9_6_L"; "LN_9_6_Z"; "SN_10_5_L"; "SN_10_5_Z"; "SN_8_14_L"; "SN_8_14_Z"; "SN_9_12_L"; "SN_9_12_Z"; "SN_9_3_L"; "SN_9_3_Z"; "SN_9_6_L"; "SN_9_6_Z"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN0.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_NT0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN0.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_0_30_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_0_30_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_0_30_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S7bA2SfG0S49A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_0_30_L)). Qed.
Lemma nfN_0_30_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S49A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_0_30_L : swf SN_0_30_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_0_30_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z0Z1eS1bR1A1A3Ll;S71A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_0_30_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_0_30_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_0_30_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S7cA2SfG0S4aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_0_30_Z)). Qed.
Lemma nfN_0_30_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S4aA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_0_30_Z : swf SN_0_30_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_0_30_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z0Z1eS1bR1A1A3Ll;S72A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_1_15_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_1_15_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_1_15_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S7dA2SfG0S4bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_1_15_L)). Qed.
Lemma nfN_1_15_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S4bA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_1_15_L : swf SN_1_15_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_1_15_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z1ZfS1bR1A1A3Ll;S73A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_1_15_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_1_15_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_1_15_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S7eA2SfG0S4cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_1_15_Z)). Qed.
Lemma nfN_1_15_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S4cA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_1_15_Z : swf SN_1_15_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_1_15_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z1ZfS1bR1A1A3Ll;S74A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_1_31_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_1_31_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_1_31_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S7fA2SfG0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_1_31_L)). Qed.
Lemma nfN_1_31_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S4dA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_1_31_L : swf SN_1_31_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_1_31_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z1Z1fS1bR1A1A3Ll;S75A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_1_31_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_1_31_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_1_31_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S80A2SfG0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_1_31_Z)). Qed.
Lemma nfN_1_31_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S4eA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_1_31_Z : swf SN_1_31_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_1_31_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z1Z1fS1bR1A1A3Ll;S76A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_2_10_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_2_10_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_2_10_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S81A2SfG0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_2_10_L)). Qed.
Lemma nfN_2_10_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S4fA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_2_10_L : swf SN_2_10_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_2_10_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z2ZaS1bR1A1A3Ll;S77A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_2_10_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_2_10_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_2_10_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S82A2SfG0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_2_10_Z)). Qed.
Lemma nfN_2_10_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S50A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_2_10_Z : swf SN_2_10_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_2_10_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z2ZaS1bR1A1A3Ll;S78A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_2_20_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_2_20_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_2_20_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S83A2SfG0S51A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_2_20_L)). Qed.
Lemma nfN_2_20_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S51A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_2_20_L : swf SN_2_20_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_2_20_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z2Z14S1bR1A1A3Ll;S79A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_2_20_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_2_20_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_2_20_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S84A2SfG0S52A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_2_20_Z)). Qed.
Lemma nfN_2_20_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S52A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_2_20_Z : swf SN_2_20_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_2_20_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z2Z14S1bR1A1A3Ll;S7aA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section NT.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S46S2aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S3cS3bS3dS32Via;A1S2cVia;A1A2S45A2S3eS44Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S41S35S31Via;A1A1S35S2fVia;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S27Via;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Local Abbreviation nidx := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx rhoK).
Let j : Z := ij ia.
Local Abbreviation nstrd := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd ia).
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Abbreviation nstrd_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd_range ia Hi Hnest Htier).
Local Abbreviation nidx_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx_range ia Hi Hnest Htier rhoK mdK A2 g amg NK).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S39S38S43S2aS22VrhoK;A1A2S48Q40A1ScL_;A2S3aS37A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Abbreviation HiN := (@U.Mal_agrp__G17.Mal_agrp_IN.HiN ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh).
Local Notation "§1§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zgm_range := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.zgm_range).
Local Notation "§2§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg erv Herv) (at level 10, h__ global).
Local Abbreviation zeN170 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.zeN170).
Local Abbreviation zeN171 := (@U.Mal_agrp__G17.Mal_agrp_IN.zeN171 ia Hi Htier rhoK mdK A2 g amg erv Herv).
Local Abbreviation zeN178 := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.zeN178).
Local Abbreviation zeN181 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.zeN181).
Local Abbreviation zp := (@U.Mal_agrp__G17.Mal_agrp_IN.zp ia rhoK A2 amg).
Local Abbreviation ze_pslot := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.ze_pslot).
Local Abbreviation ze_cj := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.ze_cj).
Local Abbreviation bzN := (@U.Mal_agrp__G17.Mal_agrp_IN.bzN amg).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S47Via;VX;VU;VA;Vrho0;A5").
Let Q : assn := ltac2:(tb__ "0|0|
S42S2aS37S36VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Lemma zsN170 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PabA1A3S2cVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1eVz;S24Via;A1A3S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
Proof using Herv Hi Hnest Htier NK. intros ->. exact (ze_pslotZ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv). Qed.

Local Ltac sem2 HagX := lazymatch goal with |- eval ?r ?e1 = eval ?r ?e2 =>
  rewrite (EVw _ _ r e1 HagX) by reflexivity; rewrite (EVw _ _ r e2 HagX) by reflexivity; f_equal end.
Local Ltac finN Esc Ecnt Ej := unfold isize, j, sc; cbn [ia_sc ia_req U.Mal_agrp__G17.Mal_agrp_IN.iaN]; unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd; rewrite ?Esc, ?Ecnt, ?Ej; try reflexivity; Z.to_euclidean_division_equations; lia.
Local Ltac pairsN HagR Esc Ecnt Ej :=
  unfold diffs_ok; repeat (apply Forall_cons; [cbn [fst snd];
    first [ solve_scratch
          | sem2 HagR; rewrite ?zsN_pslot; try (erewrite zsN_pslotZ by (unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd, j; rewrite Ej; reflexivity));
            zsimp constr:(iaN) constr:(HiN); rewrite ?zsN170, ?zsN171, ?zsN178, ?zsN181; rewrite ?zsN_cj by lia;
            rewrite ?(ze_alu iaN), ?zsN181, ?ze_lit; cbn [zalu]; finN Esc Ecnt Ej ] |]);
  apply Forall_nil.

Theorem nt_0_30 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z0A3S18S1eS2cVia;A1Z1eA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_0_30_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_0_30_Z (fst dN_0_30_Z) (snd dN_0_30_Z) true w0 sdN_0_30_Z swfN_0_30_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_0_30_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_0_30_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_0_30_Z LN_0_30_Z (rho2 iaN mWN) Q HkB (eq_trans runN_0_30_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_0_30_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_0_30_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_0_30_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_0_30_L (fst dN_0_30_L) (snd dN_0_30_L) false w0 sdN_0_30_L swfN_0_30_L _ _ (eq_sym EB) _).
      - cbn [fst dN_0_30_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_0_30_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_0_30_L LN_0_30_L (rho2 iaN mWN) Q HkB (eq_trans runN_0_30_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_0_30_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_0_30_L | exact Hin | exact Hab].
Qed.

Theorem nt_1_15 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z1A3S18S1eS2cVia;A1ZfA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_1_15_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_1_15_Z (fst dN_1_15_Z) (snd dN_1_15_Z) true w0 sdN_1_15_Z swfN_1_15_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_1_15_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_1_15_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_1_15_Z LN_1_15_Z (rho2 iaN mWN) Q HkB (eq_trans runN_1_15_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_1_15_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_1_15_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_1_15_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_1_15_L (fst dN_1_15_L) (snd dN_1_15_L) false w0 sdN_1_15_L swfN_1_15_L _ _ (eq_sym EB) _).
      - cbn [fst dN_1_15_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_1_15_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_1_15_L LN_1_15_L (rho2 iaN mWN) Q HkB (eq_trans runN_1_15_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_1_15_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_1_15_L | exact Hin | exact Hab].
Qed.

Theorem nt_1_31 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z1A3S18S1eS2cVia;A1Z1fA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_1_31_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_1_31_Z (fst dN_1_31_Z) (snd dN_1_31_Z) true w0 sdN_1_31_Z swfN_1_31_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_1_31_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_1_31_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_1_31_Z LN_1_31_Z (rho2 iaN mWN) Q HkB (eq_trans runN_1_31_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_1_31_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_1_31_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_1_31_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_1_31_L (fst dN_1_31_L) (snd dN_1_31_L) false w0 sdN_1_31_L swfN_1_31_L _ _ (eq_sym EB) _).
      - cbn [fst dN_1_31_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_1_31_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_1_31_L LN_1_31_L (rho2 iaN mWN) Q HkB (eq_trans runN_1_31_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_1_31_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_1_31_L | exact Hin | exact Hab].
Qed.

Theorem nt_2_10 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z2A3S18S1eS2cVia;A1ZaA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_2_10_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_2_10_Z (fst dN_2_10_Z) (snd dN_2_10_Z) true w0 sdN_2_10_Z swfN_2_10_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_2_10_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_2_10_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_2_10_Z LN_2_10_Z (rho2 iaN mWN) Q HkB (eq_trans runN_2_10_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_2_10_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_2_10_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_2_10_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_2_10_L (fst dN_2_10_L) (snd dN_2_10_L) false w0 sdN_2_10_L swfN_2_10_L _ _ (eq_sym EB) _).
      - cbn [fst dN_2_10_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_2_10_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_2_10_L LN_2_10_L (rho2 iaN mWN) Q HkB (eq_trans runN_2_10_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_2_10_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_2_10_L | exact Hin | exact Hab].
Qed.

Theorem nt_2_20 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z2A3S18S1eS2cVia;A1Z14A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_2_20_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_2_20_Z (fst dN_2_20_Z) (snd dN_2_20_Z) true w0 sdN_2_20_Z swfN_2_20_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_2_20_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_2_20_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_2_20_Z LN_2_20_Z (rho2 iaN mWN) Q HkB (eq_trans runN_2_20_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_2_20_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_2_20_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_2_20_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_2_20_L (fst dN_2_20_L) (snd dN_2_20_L) false w0 sdN_2_20_L swfN_2_20_L _ _ (eq_sym EB) _).
      - cbn [fst dN_2_20_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_2_20_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_2_20_L LN_2_20_L (rho2 iaN mWN) Q HkB (eq_trans runN_2_20_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_2_20_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_2_20_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT0.

Module Mal_agrp_NT3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN3.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_6_8_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_6_8_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_6_8_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1Sa5A2SfG0S5fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_6_8_L)). Qed.
Lemma nfN_6_8_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S5fA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_6_8_L : swf SN_6_8_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_6_8_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z6Z8S1bR1A1A3Ll;S9bA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_6_8_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_6_8_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_6_8_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1Sa6A2SfG0S60A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_6_8_Z)). Qed.
Lemma nfN_6_8_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S60A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_6_8_Z : swf SN_6_8_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_6_8_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z6Z8S1bR1A1A3Ll;S9cA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_6_18_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_6_18_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_6_18_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1Sa3A2SfG0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_6_18_L)). Qed.
Lemma nfN_6_18_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S5dA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_6_18_L : swf SN_6_18_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_6_18_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z6Z12S1bR1A1A3Ll;S99A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_6_18_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_6_18_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_6_18_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1Sa4A2SfG0S5eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_6_18_Z)). Qed.
Lemma nfN_6_18_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S5eA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_6_18_Z : swf SN_6_18_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_6_18_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z6Z12S1bR1A1A3Ll;S9aA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_7_7_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_7_7_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_7_7_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1Sa9A2SfG0S63A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_7_7_L)). Qed.
Lemma nfN_7_7_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S63A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_7_7_L : swf SN_7_7_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_7_7_L : ltac2:(tb__ "0|1|
S18SdS1cS1aS1aS29Z7M0G0S1bR1A1A3Ll;S9fA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_7_7_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_7_7_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_7_7_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1SaaA2SfG0S64A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_7_7_Z)). Qed.
Lemma nfN_7_7_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S64A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_7_7_Z : swf SN_7_7_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_7_7_Z : ltac2:(tb__ "0|1|
S18SdS1cS1aS1aS29Z7M0G0S1bR1A1A3Ll;Sa0A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_7_15_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_7_15_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_7_15_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1Sa7A2SfG0S61A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_7_15_L)). Qed.
Lemma nfN_7_15_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S61A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_7_15_L : swf SN_7_15_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_7_15_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z7ZfS1bR1A1A3Ll;S9dA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_7_15_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_7_15_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_7_15_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1Sa8A2SfG0S62A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_7_15_Z)). Qed.
Lemma nfN_7_15_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S62A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_7_15_Z : swf SN_7_15_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_7_15_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z7ZfS1bR1A1A3Ll;S9eA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_8_6_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_8_6_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_8_6_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1SabA2SfG0S65A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_8_6_L)). Qed.
Lemma nfN_8_6_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S65A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_8_6_L : swf SN_8_6_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_8_6_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z8Z6S1bR1A1A3Ll;Sa1A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_8_6_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_8_6_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_8_6_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1SacA2SfG0S66A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_8_6_Z)). Qed.
Lemma nfN_8_6_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S66A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_8_6_Z : swf SN_8_6_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_8_6_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z8Z6S1bR1A1A3Ll;Sa2A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section NT.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S46S2aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S3cS3bS3dS32Via;A1S2cVia;A1A2S45A2S3eS44Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S41S35S31Via;A1A1S35S2fVia;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S27Via;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Local Abbreviation nidx := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx rhoK).
Let j : Z := ij ia.
Local Abbreviation nstrd := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd ia).
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Abbreviation nstrd_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd_range ia Hi Hnest Htier).
Local Abbreviation nidx_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx_range ia Hi Hnest Htier rhoK mdK A2 g amg NK).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S39S38S43S2aS22VrhoK;A1A2S48Q40A1ScL_;A2S3aS37A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Abbreviation HiN := (@U.Mal_agrp__G17.Mal_agrp_IN.HiN ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh).
Local Notation "§3§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zgm_range := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.zgm_range).
Local Notation "§4§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg erv Herv) (at level 10, h__ global).
Local Abbreviation zeN170 := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.zeN170).
Local Abbreviation zeN171 := (@U.Mal_agrp__G17.Mal_agrp_IN.zeN171 ia Hi Htier rhoK mdK A2 g amg erv Herv).
Local Abbreviation zeN178 := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.zeN178).
Local Abbreviation zeN181 := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.zeN181).
Local Abbreviation zp := (@U.Mal_agrp__G17.Mal_agrp_IN.zp ia rhoK A2 amg).
Local Abbreviation ze_pslot := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.ze_pslot).
Local Abbreviation ze_cj := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.ze_cj).
Local Abbreviation bzN := (@U.Mal_agrp__G17.Mal_agrp_IN.bzN amg).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S47Via;VX;VU;VA;Vrho0;A5").
Let Q : assn := ltac2:(tb__ "0|0|
S42S2aS37S36VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Lemma zsN170 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PabA1A3S2cVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1eVz;S24Via;A1A3S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
Proof using Herv Hi Hnest Htier NK. intros ->. exact (ze_pslotZ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv). Qed.

Local Ltac sem2 HagX := lazymatch goal with |- eval ?r ?e1 = eval ?r ?e2 =>
  rewrite (EVw _ _ r e1 HagX) by reflexivity; rewrite (EVw _ _ r e2 HagX) by reflexivity; f_equal end.
Local Ltac finN Esc Ecnt Ej := unfold isize, j, sc; cbn [ia_sc ia_req U.Mal_agrp__G17.Mal_agrp_IN.iaN]; unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd; rewrite ?Esc, ?Ecnt, ?Ej; try reflexivity; Z.to_euclidean_division_equations; lia.
Local Ltac pairsN HagR Esc Ecnt Ej :=
  unfold diffs_ok; repeat (apply Forall_cons; [cbn [fst snd];
    first [ solve_scratch
          | sem2 HagR; rewrite ?zsN_pslot; try (erewrite zsN_pslotZ by (unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd, j; rewrite Ej; reflexivity));
            zsimp constr:(iaN) constr:(HiN); rewrite ?zsN170, ?zsN171, ?zsN178, ?zsN181; rewrite ?zsN_cj by lia;
            rewrite ?(ze_alu iaN), ?zsN181, ?ze_lit; cbn [zalu]; finN Esc Ecnt Ej ] |]);
  apply Forall_nil.

Theorem nt_6_8 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z6A3S18S1eS2cVia;A1Z8A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_6_8_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_6_8_Z (fst dN_6_8_Z) (snd dN_6_8_Z) true w0 sdN_6_8_Z swfN_6_8_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_6_8_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_6_8_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_6_8_Z LN_6_8_Z (rho2 iaN mWN) Q HkB (eq_trans runN_6_8_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_6_8_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_6_8_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_6_8_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_6_8_L (fst dN_6_8_L) (snd dN_6_8_L) false w0 sdN_6_8_L swfN_6_8_L _ _ (eq_sym EB) _).
      - cbn [fst dN_6_8_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_6_8_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_6_8_L LN_6_8_L (rho2 iaN mWN) Q HkB (eq_trans runN_6_8_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_6_8_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_6_8_L | exact Hin | exact Hab].
Qed.

Theorem nt_6_18 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z6A3S18S1eS2cVia;A1Z12A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_6_18_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_6_18_Z (fst dN_6_18_Z) (snd dN_6_18_Z) true w0 sdN_6_18_Z swfN_6_18_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_6_18_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_6_18_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_6_18_Z LN_6_18_Z (rho2 iaN mWN) Q HkB (eq_trans runN_6_18_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_6_18_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_6_18_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_6_18_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_6_18_L (fst dN_6_18_L) (snd dN_6_18_L) false w0 sdN_6_18_L swfN_6_18_L _ _ (eq_sym EB) _).
      - cbn [fst dN_6_18_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_6_18_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_6_18_L LN_6_18_L (rho2 iaN mWN) Q HkB (eq_trans runN_6_18_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_6_18_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_6_18_L | exact Hin | exact Hab].
Qed.

Theorem nt_7_7 : ltac2:(tb__ "0|2|
S18S1eS2fVia;A1Z7M0A3S18S1eS2cVia;A1G0A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M1A2S1fS23Vamg;A1A1S30G1S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_7_7_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_7_7_Z (fst dN_7_7_Z) (snd dN_7_7_Z) true w0 sdN_7_7_Z swfN_7_7_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_7_7_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_7_7_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_7_7_Z LN_7_7_Z (rho2 iaN mWN) Q HkB (eq_trans runN_7_7_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_7_7_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_7_7_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_7_7_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_7_7_L (fst dN_7_7_L) (snd dN_7_7_L) false w0 sdN_7_7_L swfN_7_7_L _ _ (eq_sym EB) _).
      - cbn [fst dN_7_7_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_7_7_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_7_7_L LN_7_7_L (rho2 iaN mWN) Q HkB (eq_trans runN_7_7_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_7_7_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_7_7_L | exact Hin | exact Hab].
Qed.

Theorem nt_7_15 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z7A3S18S1eS2cVia;A1ZfA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_7_15_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_7_15_Z (fst dN_7_15_Z) (snd dN_7_15_Z) true w0 sdN_7_15_Z swfN_7_15_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_7_15_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_7_15_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_7_15_Z LN_7_15_Z (rho2 iaN mWN) Q HkB (eq_trans runN_7_15_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_7_15_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_7_15_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_7_15_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_7_15_L (fst dN_7_15_L) (snd dN_7_15_L) false w0 sdN_7_15_L swfN_7_15_L _ _ (eq_sym EB) _).
      - cbn [fst dN_7_15_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_7_15_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_7_15_L LN_7_15_L (rho2 iaN mWN) Q HkB (eq_trans runN_7_15_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_7_15_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_7_15_L | exact Hin | exact Hab].
Qed.

Theorem nt_8_6 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z8A3S18S1eS2cVia;A1Z6A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_8_6_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_8_6_Z (fst dN_8_6_Z) (snd dN_8_6_Z) true w0 sdN_8_6_Z swfN_8_6_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_8_6_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_8_6_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_8_6_Z LN_8_6_Z (rho2 iaN mWN) Q HkB (eq_trans runN_8_6_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_8_6_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_8_6_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_8_6_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_8_6_L (fst dN_8_6_L) (snd dN_8_6_L) false w0 sdN_8_6_L swfN_8_6_L _ _ (eq_sym EB) _).
      - cbn [fst dN_8_6_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_8_6_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_8_6_L LN_8_6_L (rho2 iaN mWN) Q HkB (eq_trans runN_8_6_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_8_6_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_8_6_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT3.

Module Mal_agrp_NT1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_3_7_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_3_7_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_3_7_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S93A2SfG0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_3_7_L)). Qed.
Lemma nfN_3_7_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S57A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_3_7_L : swf SN_3_7_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_3_7_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z3Z7S1bR1A1A3Ll;S89A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_3_7_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_3_7_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_3_7_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S94A2SfG0S58A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_3_7_Z)). Qed.
Lemma nfN_3_7_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S58A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_3_7_Z : swf SN_3_7_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_3_7_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z3Z7S1bR1A1A3Ll;S8aA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_3_15_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_3_15_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_3_15_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S8fA2SfG0S53A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_3_15_L)). Qed.
Lemma nfN_3_15_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S53A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_3_15_L : swf SN_3_15_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_3_15_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z3ZfS1bR1A1A3Ll;S85A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_3_15_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_3_15_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_3_15_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S90A2SfG0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_3_15_Z)). Qed.
Lemma nfN_3_15_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S54A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_3_15_Z : swf SN_3_15_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_3_15_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z3ZfS1bR1A1A3Ll;S86A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_3_31_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_3_31_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_3_31_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S91A2SfG0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_3_31_L)). Qed.
Lemma nfN_3_31_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S55A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_3_31_L : swf SN_3_31_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_3_31_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z3Z1fS1bR1A1A3Ll;S87A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_3_31_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_3_31_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_3_31_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S92A2SfG0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_3_31_Z)). Qed.
Lemma nfN_3_31_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S56A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_3_31_Z : swf SN_3_31_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_3_31_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z3Z1fS1bR1A1A3Ll;S88A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_4_6_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_4_6_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_4_6_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S97A2SfG0S5bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_4_6_L)). Qed.
Lemma nfN_4_6_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S5bA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_4_6_L : swf SN_4_6_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_4_6_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z4Z6S1bR1A1A3Ll;S8dA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_4_6_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_4_6_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_4_6_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S98A2SfG0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_4_6_Z)). Qed.
Lemma nfN_4_6_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S5cA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_4_6_Z : swf SN_4_6_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_4_6_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z4Z6S1bR1A1A3Ll;S8eA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_4_12_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_4_12_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_4_12_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S95A2SfG0S59A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_4_12_L)). Qed.
Lemma nfN_4_12_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S59A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_4_12_L : swf SN_4_12_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_4_12_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z4ZcS1bR1A1A3Ll;S8bA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_4_12_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_4_12_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_4_12_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S96A2SfG0S5aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_4_12_Z)). Qed.
Lemma nfN_4_12_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S5aA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_4_12_Z : swf SN_4_12_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_4_12_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z4ZcS1bR1A1A3Ll;S8cA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section NT.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S46S2aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S3cS3bS3dS32Via;A1S2cVia;A1A2S45A2S3eS44Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S41S35S31Via;A1A1S35S2fVia;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S27Via;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Local Abbreviation nidx := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx rhoK).
Let j : Z := ij ia.
Local Abbreviation nstrd := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd ia).
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Abbreviation nstrd_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd_range ia Hi Hnest Htier).
Local Abbreviation nidx_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx_range ia Hi Hnest Htier rhoK mdK A2 g amg NK).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S39S38S43S2aS22VrhoK;A1A2S48Q40A1ScL_;A2S3aS37A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Abbreviation HiN := (@U.Mal_agrp__G17.Mal_agrp_IN.HiN ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh).
Local Notation "§5§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zgm_range := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.zgm_range).
Local Notation "§6§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg erv Herv) (at level 10, h__ global).
Local Abbreviation zeN170 := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zeN170).
Local Abbreviation zeN171 := (@U.Mal_agrp__G17.Mal_agrp_IN.zeN171 ia Hi Htier rhoK mdK A2 g amg erv Herv).
Local Abbreviation zeN178 := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.zeN178).
Local Abbreviation zeN181 := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zeN181).
Local Abbreviation zp := (@U.Mal_agrp__G17.Mal_agrp_IN.zp ia rhoK A2 amg).
Local Abbreviation ze_pslot := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.ze_pslot).
Local Abbreviation ze_cj := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.ze_cj).
Local Abbreviation bzN := (@U.Mal_agrp__G17.Mal_agrp_IN.bzN amg).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S47Via;VX;VU;VA;Vrho0;A5").
Let Q : assn := ltac2:(tb__ "0|0|
S42S2aS37S36VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Lemma zsN170 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PabA1A3S2cVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1eVz;S24Via;A1A3S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
Proof using Herv Hi Hnest Htier NK. intros ->. exact (ze_pslotZ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv). Qed.

Local Ltac sem2 HagX := lazymatch goal with |- eval ?r ?e1 = eval ?r ?e2 =>
  rewrite (EVw _ _ r e1 HagX) by reflexivity; rewrite (EVw _ _ r e2 HagX) by reflexivity; f_equal end.
Local Ltac finN Esc Ecnt Ej := unfold isize, j, sc; cbn [ia_sc ia_req U.Mal_agrp__G17.Mal_agrp_IN.iaN]; unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd; rewrite ?Esc, ?Ecnt, ?Ej; try reflexivity; Z.to_euclidean_division_equations; lia.
Local Ltac pairsN HagR Esc Ecnt Ej :=
  unfold diffs_ok; repeat (apply Forall_cons; [cbn [fst snd];
    first [ solve_scratch
          | sem2 HagR; rewrite ?zsN_pslot; try (erewrite zsN_pslotZ by (unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd, j; rewrite Ej; reflexivity));
            zsimp constr:(iaN) constr:(HiN); rewrite ?zsN170, ?zsN171, ?zsN178, ?zsN181; rewrite ?zsN_cj by lia;
            rewrite ?(ze_alu iaN), ?zsN181, ?ze_lit; cbn [zalu]; finN Esc Ecnt Ej ] |]);
  apply Forall_nil.

Theorem nt_3_7 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z3A3S18S1eS2cVia;A1Z7A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_3_7_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_3_7_Z (fst dN_3_7_Z) (snd dN_3_7_Z) true w0 sdN_3_7_Z swfN_3_7_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_3_7_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_3_7_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_3_7_Z LN_3_7_Z (rho2 iaN mWN) Q HkB (eq_trans runN_3_7_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_3_7_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_3_7_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_3_7_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_3_7_L (fst dN_3_7_L) (snd dN_3_7_L) false w0 sdN_3_7_L swfN_3_7_L _ _ (eq_sym EB) _).
      - cbn [fst dN_3_7_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_3_7_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_3_7_L LN_3_7_L (rho2 iaN mWN) Q HkB (eq_trans runN_3_7_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_3_7_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_3_7_L | exact Hin | exact Hab].
Qed.

Theorem nt_3_15 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z3A3S18S1eS2cVia;A1ZfA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_3_15_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_3_15_Z (fst dN_3_15_Z) (snd dN_3_15_Z) true w0 sdN_3_15_Z swfN_3_15_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_3_15_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_3_15_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_3_15_Z LN_3_15_Z (rho2 iaN mWN) Q HkB (eq_trans runN_3_15_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_3_15_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_3_15_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_3_15_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_3_15_L (fst dN_3_15_L) (snd dN_3_15_L) false w0 sdN_3_15_L swfN_3_15_L _ _ (eq_sym EB) _).
      - cbn [fst dN_3_15_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_3_15_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_3_15_L LN_3_15_L (rho2 iaN mWN) Q HkB (eq_trans runN_3_15_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_3_15_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_3_15_L | exact Hin | exact Hab].
Qed.

Theorem nt_3_31 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z3A3S18S1eS2cVia;A1Z1fA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_3_31_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_3_31_Z (fst dN_3_31_Z) (snd dN_3_31_Z) true w0 sdN_3_31_Z swfN_3_31_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_3_31_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_3_31_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_3_31_Z LN_3_31_Z (rho2 iaN mWN) Q HkB (eq_trans runN_3_31_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_3_31_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_3_31_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_3_31_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_3_31_L (fst dN_3_31_L) (snd dN_3_31_L) false w0 sdN_3_31_L swfN_3_31_L _ _ (eq_sym EB) _).
      - cbn [fst dN_3_31_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_3_31_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_3_31_L LN_3_31_L (rho2 iaN mWN) Q HkB (eq_trans runN_3_31_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_3_31_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_3_31_L | exact Hin | exact Hab].
Qed.

Theorem nt_4_6 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z4A3S18S1eS2cVia;A1Z6A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_4_6_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_4_6_Z (fst dN_4_6_Z) (snd dN_4_6_Z) true w0 sdN_4_6_Z swfN_4_6_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_4_6_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_4_6_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_4_6_Z LN_4_6_Z (rho2 iaN mWN) Q HkB (eq_trans runN_4_6_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_4_6_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_4_6_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_4_6_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_4_6_L (fst dN_4_6_L) (snd dN_4_6_L) false w0 sdN_4_6_L swfN_4_6_L _ _ (eq_sym EB) _).
      - cbn [fst dN_4_6_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_4_6_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_4_6_L LN_4_6_L (rho2 iaN mWN) Q HkB (eq_trans runN_4_6_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_4_6_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_4_6_L | exact Hin | exact Hab].
Qed.

Theorem nt_4_12 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z4A3S18S1eS2cVia;A1ZcA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_4_12_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_4_12_Z (fst dN_4_12_Z) (snd dN_4_12_Z) true w0 sdN_4_12_Z swfN_4_12_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_4_12_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_4_12_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_4_12_Z LN_4_12_Z (rho2 iaN mWN) Q HkB (eq_trans runN_4_12_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_4_12_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_4_12_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_4_12_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_4_12_L (fst dN_4_12_L) (snd dN_4_12_L) false w0 sdN_4_12_L swfN_4_12_L _ _ (eq_sym EB) _).
      - cbn [fst dN_4_12_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_4_12_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_4_12_L LN_4_12_L (rho2 iaN mWN) Q HkB (eq_trans runN_4_12_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_4_12_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_4_12_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT1.

Module Mal_agrp_NT4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN4.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_8_14_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_8_14_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_8_14_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1Sb9A2SfG0S69A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_8_14_L)). Qed.
Lemma nfN_8_14_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S69A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_8_14_L : swf SN_8_14_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_8_14_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z8ZeS1bR1A1A3Ll;SafA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_8_14_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_8_14_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_8_14_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1SbaA2SfG0S6aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_8_14_Z)). Qed.
Lemma nfN_8_14_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S6aA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_8_14_Z : swf SN_8_14_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_8_14_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z8ZeS1bR1A1A3Ll;Sb0A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_9_3_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_9_3_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_9_3_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1SbdA2SfG0S6dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_9_3_L)). Qed.
Lemma nfN_9_3_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S6dA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_9_3_L : swf SN_9_3_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_9_3_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z9Z3S1bR1A1A3Ll;Sb3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_9_3_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_9_3_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_9_3_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1SbeA2SfG0S6eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_9_3_Z)). Qed.
Lemma nfN_9_3_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S6eA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_9_3_Z : swf SN_9_3_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_9_3_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z9Z3S1bR1A1A3Ll;Sb4A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_9_6_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_9_6_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_9_6_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1SbfA2SfG0S6fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_9_6_L)). Qed.
Lemma nfN_9_6_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S6fA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_9_6_L : swf SN_9_6_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_9_6_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z9Z6S1bR1A1A3Ll;Sb5A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_9_6_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_9_6_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_9_6_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1Sc0A2SfG0S70A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_9_6_Z)). Qed.
Lemma nfN_9_6_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S70A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_9_6_Z : swf SN_9_6_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_9_6_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z9Z6S1bR1A1A3Ll;Sb6A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_9_12_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_9_12_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_9_12_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1SbbA2SfG0S6bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_9_12_L)). Qed.
Lemma nfN_9_12_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S6bA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_9_12_L : swf SN_9_12_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_9_12_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z9ZcS1bR1A1A3Ll;Sb1A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_9_12_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_9_12_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_9_12_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1SbcA2SfG0S6cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_9_12_Z)). Qed.
Lemma nfN_9_12_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S6cA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_9_12_Z : swf SN_9_12_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_9_12_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29Z9ZcS1bR1A1A3Ll;Sb2A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_10_5_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_10_5_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_10_5_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1Sb7A2SfG0S67A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_10_5_L)). Qed.
Lemma nfN_10_5_L : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S67A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_10_5_L : swf SN_10_5_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_10_5_L : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29ZaZ5S1bR1A1A3Ll;SadA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_10_5_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_10_5_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_10_5_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1Sb8A2SfG0S68A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_10_5_Z)). Qed.
Lemma nfN_10_5_Z : ltac2:(tb__ "0|0|
S18SdS1cS4S4S1dS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S68A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_10_5_Z : swf SN_10_5_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_10_5_Z : ltac2:(tb__ "0|0|
S18SdS1cS1aS1aS29ZaZ5S1bR1A1A3Ll;SaeA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section NT.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S46S2aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S3cS3bS3dS32Via;A1S2cVia;A1A2S45A2S3eS44Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S41S35S31Via;A1A1S35S2fVia;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S27Via;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Local Abbreviation nidx := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx rhoK).
Let j : Z := ij ia.
Local Abbreviation nstrd := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd ia).
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Abbreviation nstrd_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd_range ia Hi Hnest Htier).
Local Abbreviation nidx_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx_range ia Hi Hnest Htier rhoK mdK A2 g amg NK).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S39S38S43S2aS22VrhoK;A1A2S48Q40A1ScL_;A2S3aS37A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Abbreviation HiN := (@U.Mal_agrp__G17.Mal_agrp_IN.HiN ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh).
Local Notation "§7§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zgm_range := (§7§ U.Mal_agrp__G17.Mal_agrp_IN.zgm_range).
Local Notation "§8§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg erv Herv) (at level 10, h__ global).
Local Abbreviation zeN170 := (§8§ U.Mal_agrp__G17.Mal_agrp_IN.zeN170).
Local Abbreviation zeN171 := (@U.Mal_agrp__G17.Mal_agrp_IN.zeN171 ia Hi Htier rhoK mdK A2 g amg erv Herv).
Local Abbreviation zeN178 := (§7§ U.Mal_agrp__G17.Mal_agrp_IN.zeN178).
Local Abbreviation zeN181 := (§8§ U.Mal_agrp__G17.Mal_agrp_IN.zeN181).
Local Abbreviation zp := (@U.Mal_agrp__G17.Mal_agrp_IN.zp ia rhoK A2 amg).
Local Abbreviation ze_pslot := (§7§ U.Mal_agrp__G17.Mal_agrp_IN.ze_pslot).
Local Abbreviation ze_cj := (§8§ U.Mal_agrp__G17.Mal_agrp_IN.ze_cj).
Local Abbreviation bzN := (@U.Mal_agrp__G17.Mal_agrp_IN.bzN amg).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S47Via;VX;VU;VA;Vrho0;A5").
Let Q : assn := ltac2:(tb__ "0|0|
S42S2aS37S36VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Lemma zsN170 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3PabA1A3S2cVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1eVz;S24Via;A1A3S18S1eS2bS2eS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2dG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
Proof using Herv Hi Hnest Htier NK. intros ->. exact (ze_pslotZ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv). Qed.

Local Ltac sem2 HagX := lazymatch goal with |- eval ?r ?e1 = eval ?r ?e2 =>
  rewrite (EVw _ _ r e1 HagX) by reflexivity; rewrite (EVw _ _ r e2 HagX) by reflexivity; f_equal end.
Local Ltac finN Esc Ecnt Ej := unfold isize, j, sc; cbn [ia_sc ia_req U.Mal_agrp__G17.Mal_agrp_IN.iaN]; unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd; rewrite ?Esc, ?Ecnt, ?Ej; try reflexivity; Z.to_euclidean_division_equations; lia.
Local Ltac pairsN HagR Esc Ecnt Ej :=
  unfold diffs_ok; repeat (apply Forall_cons; [cbn [fst snd];
    first [ solve_scratch
          | sem2 HagR; rewrite ?zsN_pslot; try (erewrite zsN_pslotZ by (unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd, j; rewrite Ej; reflexivity));
            zsimp constr:(iaN) constr:(HiN); rewrite ?zsN170, ?zsN171, ?zsN178, ?zsN181; rewrite ?zsN_cj by lia;
            rewrite ?(ze_alu iaN), ?zsN181, ?ze_lit; cbn [zalu]; finN Esc Ecnt Ej ] |]);
  apply Forall_nil.

Theorem nt_8_14 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z8A3S18S1eS2cVia;A1ZeA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_8_14_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_8_14_Z (fst dN_8_14_Z) (snd dN_8_14_Z) true w0 sdN_8_14_Z swfN_8_14_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_8_14_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_8_14_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_8_14_Z LN_8_14_Z (rho2 iaN mWN) Q HkB (eq_trans runN_8_14_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_8_14_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_8_14_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_8_14_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_8_14_L (fst dN_8_14_L) (snd dN_8_14_L) false w0 sdN_8_14_L swfN_8_14_L _ _ (eq_sym EB) _).
      - cbn [fst dN_8_14_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_8_14_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_8_14_L LN_8_14_L (rho2 iaN mWN) Q HkB (eq_trans runN_8_14_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_8_14_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_8_14_L | exact Hin | exact Hab].
Qed.

Theorem nt_9_3 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z9A3S18S1eS2cVia;A1Z3A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_9_3_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_9_3_Z (fst dN_9_3_Z) (snd dN_9_3_Z) true w0 sdN_9_3_Z swfN_9_3_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_9_3_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_9_3_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_9_3_Z LN_9_3_Z (rho2 iaN mWN) Q HkB (eq_trans runN_9_3_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_9_3_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_9_3_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_9_3_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_9_3_L (fst dN_9_3_L) (snd dN_9_3_L) false w0 sdN_9_3_L swfN_9_3_L _ _ (eq_sym EB) _).
      - cbn [fst dN_9_3_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_9_3_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_9_3_L LN_9_3_L (rho2 iaN mWN) Q HkB (eq_trans runN_9_3_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_9_3_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_9_3_L | exact Hin | exact Hab].
Qed.

Theorem nt_9_6 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z9A3S18S1eS2cVia;A1Z6A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_9_6_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_9_6_Z (fst dN_9_6_Z) (snd dN_9_6_Z) true w0 sdN_9_6_Z swfN_9_6_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_9_6_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_9_6_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_9_6_Z LN_9_6_Z (rho2 iaN mWN) Q HkB (eq_trans runN_9_6_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_9_6_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_9_6_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_9_6_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_9_6_L (fst dN_9_6_L) (snd dN_9_6_L) false w0 sdN_9_6_L swfN_9_6_L _ _ (eq_sym EB) _).
      - cbn [fst dN_9_6_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_9_6_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_9_6_L LN_9_6_L (rho2 iaN mWN) Q HkB (eq_trans runN_9_6_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_9_6_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_9_6_L | exact Hin | exact Hab].
Qed.

Theorem nt_9_12 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1Z9A3S18S1eS2cVia;A1ZcA3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_9_12_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_9_12_Z (fst dN_9_12_Z) (snd dN_9_12_Z) true w0 sdN_9_12_Z swfN_9_12_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_9_12_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_9_12_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_9_12_Z LN_9_12_Z (rho2 iaN mWN) Q HkB (eq_trans runN_9_12_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_9_12_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_9_12_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_9_12_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_9_12_L (fst dN_9_12_L) (snd dN_9_12_L) false w0 sdN_9_12_L swfN_9_12_L _ _ (eq_sym EB) _).
      - cbn [fst dN_9_12_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_9_12_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_9_12_L LN_9_12_L (rho2 iaN mWN) Q HkB (eq_trans runN_9_12_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_9_12_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_9_12_L | exact Hin | exact Hab].
Qed.

Theorem nt_10_5 : ltac2:(tb__ "0|1|
S18S1eS2fVia;A1ZaA3S18S1eS2cVia;A1Z5A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_10_5_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_10_5_Z (fst dN_10_5_Z) (snd dN_10_5_Z) true w0 sdN_10_5_Z swfN_10_5_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_10_5_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_10_5_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_10_5_Z LN_10_5_Z (rho2 iaN mWN) Q HkB (eq_trans runN_10_5_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_10_5_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_10_5_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_10_5_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_10_5_L (fst dN_10_5_L) (snd dN_10_5_L) false w0 sdN_10_5_L swfN_10_5_L _ _ (eq_sym EB) _).
      - cbn [fst dN_10_5_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_10_5_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_10_5_L LN_10_5_L (rho2 iaN mWN) Q HkB (eq_trans runN_10_5_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_10_5_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_10_5_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT4.
