(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SAlu"; "SVar"; "sprop"; "SMd"; "SPUle"; "sprop_eqb"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "true"; "bool"; "nil"; "Some"; "false"; "option"; "snd"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "ALU_AND"; "ALU_SRL"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3"; "SN3s"; "factsN3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN"; "iaN"; "mWN"; "bzN"; "nstrd"; "zp"; "nidx"; "nokR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs"; "leafN_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "zl2"; "zr2"; "icnt0"; "ia_sc"; "rho2"; "ij"; "isize"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "IEC_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_errno"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "div"; "lt"; "pow"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv"; "prov"; "@stdpp.bitvector.definitions"; "bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.Mal_agrp_NT5"; "dN_10_10_L"; "dN_10_10_Z"; "dN_11_2_L"; "dN_11_2_Z"; "dN_11_4_L"; "dN_11_4_Z"; "dN_11_8_L"; "dN_11_8_Z"; "dN_12_7_L"; "dN_12_7_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.Mal_agrp_NT6"; "dN_13_3_L"; "dN_13_3_Z"; "dN_13_6_L"; "dN_13_6_Z"; "dN_14_5_L"; "dN_14_5_Z"; "dN_15_2_L"; "dN_15_2_Z"; "dN_15_4_L"; "dN_15_4_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.Mal_agrp_NT7"; "dN_17_3_L"; "dN_17_3_Z"; "dN_19_2_L"; "dN_19_2_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rN5"; "LN_10_10_L"; "LN_10_10_Z"; "LN_11_2_L"; "LN_11_2_Z"; "LN_11_4_L"; "LN_11_4_Z"; "LN_11_8_L"; "LN_11_8_Z"; "LN_12_7_L"; "LN_12_7_Z"; "SN_10_10_L"; "SN_10_10_Z"; "SN_11_2_L"; "SN_11_2_Z"; "SN_11_4_L"; "SN_11_4_Z"; "SN_11_8_L"; "SN_11_8_Z"; "SN_12_7_L"; "SN_12_7_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rN7"; "LN_17_3_L"; "LN_17_3_Z"; "LN_19_2_L"; "LN_19_2_Z"; "SN_17_3_L"; "SN_17_3_Z"; "SN_19_2_L"; "SN_19_2_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN6"; "LN_13_3_L"; "LN_13_3_Z"; "LN_13_6_L"; "LN_13_6_Z"; "LN_14_5_L";
"LN_14_5_Z"; "LN_15_2_L"; "LN_15_2_Z"; "LN_15_4_L"; "LN_15_4_Z"; "SN_13_3_L"; "SN_13_3_Z"; "SN_13_6_L"; "SN_13_6_Z"; "SN_14_5_L"; "SN_14_5_Z"; "SN_15_2_L"; "SN_15_2_Z"; "SN_15_4_L"; "SN_15_4_Z"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_NT7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rN7.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_17_3_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_17_3_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_17_3_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S79A2SfG0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_17_3_L)). Qed.
Lemma nfN_17_3_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S5dA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_17_3_L : swf SN_17_3_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_17_3_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29Z11Z3S1cR1A1A3Ll;S75A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_17_3_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_17_3_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_17_3_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S7aA2SfG0S5eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_17_3_Z)). Qed.
Lemma nfN_17_3_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S5eA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_17_3_Z : swf SN_17_3_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_17_3_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29Z11Z3S1cR1A1A3Ll;S76A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_19_2_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_19_2_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_19_2_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S7bA2SfG0S5fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_19_2_L)). Qed.
Lemma nfN_19_2_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S5fA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_19_2_L : swf SN_19_2_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_19_2_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29Z13Z2S1cR1A1A3Ll;S77A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_19_2_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_19_2_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_19_2_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S7cA2SfG0S60A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_19_2_Z)). Qed.
Lemma nfN_19_2_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S60A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_19_2_Z : swf SN_19_2_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_19_2_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29Z13Z2S1cR1A1A3Ll;S78A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

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
S3cS3bS3dS32Via;A1S2eVia;A1A2S45A2S3eS44Z2A2A2").
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
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3PabA1A3S2eVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1aVz;S24Via;A1A3S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
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

Theorem nt_17_3 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1Z11A3S18S1aS2eVia;A1Z3A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_17_3_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_17_3_Z (fst dN_17_3_Z) (snd dN_17_3_Z) true w0 sdN_17_3_Z swfN_17_3_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_17_3_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_17_3_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_17_3_Z LN_17_3_Z (rho2 iaN mWN) Q HkB (eq_trans runN_17_3_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_17_3_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_17_3_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_17_3_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_17_3_L (fst dN_17_3_L) (snd dN_17_3_L) false w0 sdN_17_3_L swfN_17_3_L _ _ (eq_sym EB) _).
      - cbn [fst dN_17_3_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_17_3_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_17_3_L LN_17_3_L (rho2 iaN mWN) Q HkB (eq_trans runN_17_3_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_17_3_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_17_3_L | exact Hin | exact Hab].
Qed.

Theorem nt_19_2 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1Z13A3S18S1aS2eVia;A1Z2A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_19_2_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_19_2_Z (fst dN_19_2_Z) (snd dN_19_2_Z) true w0 sdN_19_2_Z swfN_19_2_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_19_2_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_19_2_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_19_2_Z LN_19_2_Z (rho2 iaN mWN) Q HkB (eq_trans runN_19_2_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_19_2_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_19_2_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_19_2_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_19_2_L (fst dN_19_2_L) (snd dN_19_2_L) false w0 sdN_19_2_L swfN_19_2_L _ _ (eq_sym EB) _).
      - cbn [fst dN_19_2_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_19_2_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_19_2_L LN_19_2_L (rho2 iaN mWN) Q HkB (eq_trans runN_19_2_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_19_2_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_19_2_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT7.

Module Mal_agrp_NT6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN6.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_13_3_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_13_3_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_13_3_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S87A2SfG0S53A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_13_3_L)). Qed.
Lemma nfN_13_3_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S53A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_13_3_L : swf SN_13_3_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_13_3_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZdZ3S1cR1A1A3Ll;S7dA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_13_3_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_13_3_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_13_3_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S88A2SfG0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_13_3_Z)). Qed.
Lemma nfN_13_3_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S54A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_13_3_Z : swf SN_13_3_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_13_3_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZdZ3S1cR1A1A3Ll;S7eA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_13_6_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_13_6_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_13_6_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S89A2SfG0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_13_6_L)). Qed.
Lemma nfN_13_6_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S55A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_13_6_L : swf SN_13_6_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_13_6_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZdZ6S1cR1A1A3Ll;S7fA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_13_6_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_13_6_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_13_6_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S8aA2SfG0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_13_6_Z)). Qed.
Lemma nfN_13_6_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S56A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_13_6_Z : swf SN_13_6_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_13_6_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZdZ6S1cR1A1A3Ll;S80A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_14_5_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_14_5_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_14_5_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S8bA2SfG0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_14_5_L)). Qed.
Lemma nfN_14_5_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S57A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_14_5_L : swf SN_14_5_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_14_5_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZeZ5S1cR1A1A3Ll;S81A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_14_5_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_14_5_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_14_5_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S8cA2SfG0S58A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_14_5_Z)). Qed.
Lemma nfN_14_5_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S58A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_14_5_Z : swf SN_14_5_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_14_5_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZeZ5S1cR1A1A3Ll;S82A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_15_2_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_15_2_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_15_2_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S8dA2SfG0S59A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_15_2_L)). Qed.
Lemma nfN_15_2_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S59A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_15_2_L : swf SN_15_2_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_15_2_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZfZ2S1cR1A1A3Ll;S83A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_15_2_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_15_2_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_15_2_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S8eA2SfG0S5aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_15_2_Z)). Qed.
Lemma nfN_15_2_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S5aA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_15_2_Z : swf SN_15_2_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_15_2_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZfZ2S1cR1A1A3Ll;S84A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_15_4_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_15_4_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_15_4_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S8fA2SfG0S5bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_15_4_L)). Qed.
Lemma nfN_15_4_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S5bA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_15_4_L : swf SN_15_4_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_15_4_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZfZ4S1cR1A1A3Ll;S85A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_15_4_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_15_4_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_15_4_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S90A2SfG0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_15_4_Z)). Qed.
Lemma nfN_15_4_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S5cA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_15_4_Z : swf SN_15_4_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_15_4_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZfZ4S1cR1A1A3Ll;S86A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

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
S3cS3bS3dS32Via;A1S2eVia;A1A2S45A2S3eS44Z2A2A2").
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
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3PabA1A3S2eVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1aVz;S24Via;A1A3S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
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

Theorem nt_13_3 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZdA3S18S1aS2eVia;A1Z3A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_13_3_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_13_3_Z (fst dN_13_3_Z) (snd dN_13_3_Z) true w0 sdN_13_3_Z swfN_13_3_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_13_3_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_13_3_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_13_3_Z LN_13_3_Z (rho2 iaN mWN) Q HkB (eq_trans runN_13_3_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_13_3_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_13_3_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_13_3_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_13_3_L (fst dN_13_3_L) (snd dN_13_3_L) false w0 sdN_13_3_L swfN_13_3_L _ _ (eq_sym EB) _).
      - cbn [fst dN_13_3_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_13_3_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_13_3_L LN_13_3_L (rho2 iaN mWN) Q HkB (eq_trans runN_13_3_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_13_3_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_13_3_L | exact Hin | exact Hab].
Qed.

Theorem nt_13_6 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZdA3S18S1aS2eVia;A1Z6A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_13_6_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_13_6_Z (fst dN_13_6_Z) (snd dN_13_6_Z) true w0 sdN_13_6_Z swfN_13_6_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_13_6_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_13_6_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_13_6_Z LN_13_6_Z (rho2 iaN mWN) Q HkB (eq_trans runN_13_6_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_13_6_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_13_6_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_13_6_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_13_6_L (fst dN_13_6_L) (snd dN_13_6_L) false w0 sdN_13_6_L swfN_13_6_L _ _ (eq_sym EB) _).
      - cbn [fst dN_13_6_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_13_6_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_13_6_L LN_13_6_L (rho2 iaN mWN) Q HkB (eq_trans runN_13_6_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_13_6_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_13_6_L | exact Hin | exact Hab].
Qed.

Theorem nt_14_5 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZeA3S18S1aS2eVia;A1Z5A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_14_5_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_14_5_Z (fst dN_14_5_Z) (snd dN_14_5_Z) true w0 sdN_14_5_Z swfN_14_5_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_14_5_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_14_5_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_14_5_Z LN_14_5_Z (rho2 iaN mWN) Q HkB (eq_trans runN_14_5_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_14_5_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_14_5_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_14_5_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_14_5_L (fst dN_14_5_L) (snd dN_14_5_L) false w0 sdN_14_5_L swfN_14_5_L _ _ (eq_sym EB) _).
      - cbn [fst dN_14_5_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_14_5_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_14_5_L LN_14_5_L (rho2 iaN mWN) Q HkB (eq_trans runN_14_5_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_14_5_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_14_5_L | exact Hin | exact Hab].
Qed.

Theorem nt_15_2 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZfA3S18S1aS2eVia;A1Z2A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_15_2_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_15_2_Z (fst dN_15_2_Z) (snd dN_15_2_Z) true w0 sdN_15_2_Z swfN_15_2_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_15_2_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_15_2_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_15_2_Z LN_15_2_Z (rho2 iaN mWN) Q HkB (eq_trans runN_15_2_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_15_2_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_15_2_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_15_2_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_15_2_L (fst dN_15_2_L) (snd dN_15_2_L) false w0 sdN_15_2_L swfN_15_2_L _ _ (eq_sym EB) _).
      - cbn [fst dN_15_2_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_15_2_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_15_2_L LN_15_2_L (rho2 iaN mWN) Q HkB (eq_trans runN_15_2_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_15_2_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_15_2_L | exact Hin | exact Hab].
Qed.

Theorem nt_15_4 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZfA3S18S1aS2eVia;A1Z4A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_15_4_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_15_4_Z (fst dN_15_4_Z) (snd dN_15_4_Z) true w0 sdN_15_4_Z swfN_15_4_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_15_4_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_15_4_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_15_4_Z LN_15_4_Z (rho2 iaN mWN) Q HkB (eq_trans runN_15_4_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_15_4_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_15_4_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_15_4_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_15_4_L (fst dN_15_4_L) (snd dN_15_4_L) false w0 sdN_15_4_L swfN_15_4_L _ _ (eq_sym EB) _).
      - cbn [fst dN_15_4_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_15_4_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_15_4_L LN_15_4_L (rho2 iaN mWN) Q HkB (eq_trans runN_15_4_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_15_4_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_15_4_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT6.

Module Mal_agrp_NT5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rN5.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_10_10_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_10_10_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_10_10_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S6bA2SfG0S49A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_10_10_L)). Qed.
Lemma nfN_10_10_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S49A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_10_10_L : swf SN_10_10_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_10_10_L : ltac2:(tb__ "0|1|
S18SdS1dS1bS1bS29ZaM0G0S1cR1A1A3Ll;S61A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_10_10_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_10_10_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_10_10_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S6cA2SfG0S4aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_10_10_Z)). Qed.
Lemma nfN_10_10_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S4aA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_10_10_Z : swf SN_10_10_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_10_10_Z : ltac2:(tb__ "0|1|
S18SdS1dS1bS1bS29ZaM0G0S1cR1A1A3Ll;S62A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_11_2_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_11_2_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_11_2_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S6dA2SfG0S4bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_11_2_L)). Qed.
Lemma nfN_11_2_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20ZfS10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S4bA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_11_2_L : swf SN_11_2_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_11_2_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZbZ2S1cR1A1A3Ll;S63A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_11_2_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_11_2_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_11_2_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S6eA2SfG0S4cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_11_2_Z)). Qed.
Lemma nfN_11_2_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20ZfScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S4cA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_11_2_Z : swf SN_11_2_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_11_2_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZbZ2S1cR1A1A3Ll;S64A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_11_4_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_11_4_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_11_4_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S6fA2SfG0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_11_4_L)). Qed.
Lemma nfN_11_4_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z13S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S4dA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_11_4_L : swf SN_11_4_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_11_4_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZbZ4S1cR1A1A3Ll;S65A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_11_4_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_11_4_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_11_4_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S70A2SfG0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_11_4_Z)). Qed.
Lemma nfN_11_4_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z13ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S4eA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_11_4_Z : swf SN_11_4_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_11_4_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZbZ4S1cR1A1A3Ll;S66A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_11_8_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_11_8_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_11_8_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S71A2SfG0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_11_8_L)). Qed.
Lemma nfN_11_8_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S4fA3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_11_8_L : swf SN_11_8_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_11_8_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZbZ8S1cR1A1A3Ll;S67A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_11_8_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_11_8_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_11_8_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S72A2SfG0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_11_8_Z)). Qed.
Lemma nfN_11_8_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S50A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_11_8_Z : swf SN_11_8_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_11_8_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZbZ8S1cR1A1A3Ll;S68A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_12_7_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_12_7_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_12_7_L : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fS10A1S73A2SfG0S51A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_12_7_L)). Qed.
Lemma nfN_12_7_L : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17S10A2A3Lp;S12SaSbS0S0A2A1SaS4A1S51A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_12_7_L : swf SN_12_7_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_12_7_L : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZcZ7S1cR1A1A3Ll;S69A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_12_7_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_12_7_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_12_7_Z : ltac2:(tb__ "0|1|
S18S11SbSaSbS0S0A2A1SaS4A1A2M0A1S28S1fScA1S74A2SfG0S52A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_12_7_Z)). Qed.
Lemma nfN_12_7_Z : ltac2:(tb__ "0|0|
S18SdS1dS4S4S1eS4S7R1A1S20Z17ScA2A3Lp;S12SaSbS0S0A2A1SaS4A1S52A3A3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_12_7_Z : swf SN_12_7_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_12_7_Z : ltac2:(tb__ "0|0|
S18SdS1dS1bS1bS29ZcZ7S1cR1A1A3Ll;S6aA3ScA3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

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
S3cS3bS3dS32Via;A1S2eVia;A1A2S45A2S3eS44Z2A2A2").
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
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3PabA1A3S2eVia;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3Pb2A1A3S26VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S3Pb5A1A3S24Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S19S3cZ0Vk;A2S3fVk;S40Z2Z20A2A2A2S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S15S3PaaA1S1Z3A1A3S1Vk;A1A3A3S3bS3dZ8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S13S3Pb4A1S5S14S3Pb5A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S18S1aVz;S24Via;A1A3S18S1aS2bS2dS21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S2cG0A1S2S13S2S13S3Pb4A1S5S14S1Vz;A1S3Pb2A1A3A3S1Z10A1A3A3S25Via;VrhoK;VA2;Vamg;A4A3F_;").
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

Theorem nt_10_10 : ltac2:(tb__ "0|2|
S18S1aS2fVia;A1ZaM0A3S18S1aS2eVia;A1G0A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M1A2S1fS23Vamg;A1A1S30G1S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_10_10_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_10_10_Z (fst dN_10_10_Z) (snd dN_10_10_Z) true w0 sdN_10_10_Z swfN_10_10_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_10_10_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_10_10_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_10_10_Z LN_10_10_Z (rho2 iaN mWN) Q HkB (eq_trans runN_10_10_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_10_10_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_10_10_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_10_10_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_10_10_L (fst dN_10_10_L) (snd dN_10_10_L) false w0 sdN_10_10_L swfN_10_10_L _ _ (eq_sym EB) _).
      - cbn [fst dN_10_10_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_10_10_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_10_10_L LN_10_10_L (rho2 iaN mWN) Q HkB (eq_trans runN_10_10_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_10_10_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_10_10_L | exact Hin | exact Hab].
Qed.

Theorem nt_11_2 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZbA3S18S1aS2eVia;A1Z2A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_11_2_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_11_2_Z (fst dN_11_2_Z) (snd dN_11_2_Z) true w0 sdN_11_2_Z swfN_11_2_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_11_2_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_11_2_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_11_2_Z LN_11_2_Z (rho2 iaN mWN) Q HkB (eq_trans runN_11_2_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_11_2_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_11_2_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_11_2_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_11_2_L (fst dN_11_2_L) (snd dN_11_2_L) false w0 sdN_11_2_L swfN_11_2_L _ _ (eq_sym EB) _).
      - cbn [fst dN_11_2_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_11_2_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_11_2_L LN_11_2_L (rho2 iaN mWN) Q HkB (eq_trans runN_11_2_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_11_2_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_11_2_L | exact Hin | exact Hab].
Qed.

Theorem nt_11_4 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZbA3S18S1aS2eVia;A1Z4A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_11_4_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_11_4_Z (fst dN_11_4_Z) (snd dN_11_4_Z) true w0 sdN_11_4_Z swfN_11_4_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_11_4_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_11_4_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_11_4_Z LN_11_4_Z (rho2 iaN mWN) Q HkB (eq_trans runN_11_4_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_11_4_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_11_4_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_11_4_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_11_4_L (fst dN_11_4_L) (snd dN_11_4_L) false w0 sdN_11_4_L swfN_11_4_L _ _ (eq_sym EB) _).
      - cbn [fst dN_11_4_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_11_4_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_11_4_L LN_11_4_L (rho2 iaN mWN) Q HkB (eq_trans runN_11_4_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_11_4_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_11_4_L | exact Hin | exact Hab].
Qed.

Theorem nt_11_8 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZbA3S18S1aS2eVia;A1Z8A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_11_8_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_11_8_Z (fst dN_11_8_Z) (snd dN_11_8_Z) true w0 sdN_11_8_Z swfN_11_8_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_11_8_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_11_8_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_11_8_Z LN_11_8_Z (rho2 iaN mWN) Q HkB (eq_trans runN_11_8_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_11_8_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_11_8_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_11_8_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_11_8_L (fst dN_11_8_L) (snd dN_11_8_L) false w0 sdN_11_8_L swfN_11_8_L _ _ (eq_sym EB) _).
      - cbn [fst dN_11_8_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_11_8_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_11_8_L LN_11_8_L (rho2 iaN mWN) Q HkB (eq_trans runN_11_8_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_11_8_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_11_8_L | exact Hin | exact Hab].
Qed.

Theorem nt_12_7 : ltac2:(tb__ "0|1|
S18S1aS2fVia;A1ZcA3S18S1aS2eVia;A1Z7A3VTR;VkB;S33S2aS34VKc;S21Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S1fS23Vamg;A1A1S30G0S22VrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_12_7_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_12_7_Z (fst dN_12_7_Z) (snd dN_12_7_Z) true w0 sdN_12_7_Z swfN_12_7_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_12_7_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_12_7_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_12_7_Z LN_12_7_Z (rho2 iaN mWN) Q HkB (eq_trans runN_12_7_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_12_7_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_12_7_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_12_7_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_12_7_L (fst dN_12_7_L) (snd dN_12_7_L) false w0 sdN_12_7_L swfN_12_7_L _ _ (eq_sym EB) _).
      - cbn [fst dN_12_7_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_12_7_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_12_7_L LN_12_7_L (rho2 iaN mWN) Q HkB (eq_trans runN_12_7_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_12_7_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_12_7_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT5.
