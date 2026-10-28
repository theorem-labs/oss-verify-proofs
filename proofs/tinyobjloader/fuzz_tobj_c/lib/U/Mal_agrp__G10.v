(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SCsym"; "SN2pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c33"; "LC_33_0"; "LC_33_1"; "LC_33_2"; "LC_33_3"; "dC_33"; "dL_33_0"; "dL_33_1"; "dL_33_2"; "dL_33_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c34"; "LC_34_0"; "LC_34_1"; "LC_34_2"; "dC_34"; "dL_34_0"; "dL_34_1"; "dL_34_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c36"; "LC_36_0"; "LC_36_1"; "LC_36_2"; "dC_36"; "dL_36_0"; "dL_36_1"; "dL_36_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c37"; "LC_37_0"; "LC_37_1"; "LC_37_2"; "LC_37_3"; "dC_37"; "dL_37_0"; "dL_37_1"; "dL_37_2"; "dL_37_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c38"; "LC_38_0"; "LC_38_1"; "LC_38_2"; "dC_38"; "dL_38_0"; "dL_38_1"; "dL_38_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_33"; "SC_34"; "SC_36"; "SC_37"; "SC_38"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_c33.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_33 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_33 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_33 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS56A2S10G0S33A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_33)). Qed.
Definition setsC_33 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_33)) in exact x).
Definition LC_33_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_33 0 SC_33) in exact x).
Definition dL_33_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z21A1S2PcA1M1A4SbG0ScS0S0S1Z2ab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ff00A1S2PacA1M4A4SbG0ScS0S0S1Z3ff10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a528A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2aa0A1G2A4SbG0ScS0S0S1Z160A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z168A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2e0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2e8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_33_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S2fS19A2S10G0S34A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_33_0)). Qed.
Definition setsL_33_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_33_0)) in exact x).
Definition LC_33_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_33 1 SC_33) in exact x).
Definition dL_33_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z21A1S2PcA1M1A4SbG0ScS0S0S1Z2ab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff80A1S2PacA1M4A4SbG0ScS0S0S1Z1ff90A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a528A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2aa0A1G2A4SbG0ScS0S0S1Z160A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z168A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2e0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2e8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_33_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S30S19A2S10G0S35A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_33_1)). Qed.
Definition setsL_33_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_33_1)) in exact x).
Definition LC_33_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_33 2 SC_33) in exact x).
Definition dL_33_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z21A1S2PcA1M1A4SbG0ScS0S0S1Z2ab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffc0A1S2PacA1M4A4SbG0ScS0S0S1Zffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a528A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2aa0A1G2A4SbG0ScS0S0S1Z160A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z168A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2e0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2e8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_33_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S31S19A2S10G0S36A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_33_2)). Qed.
Definition setsL_33_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_33_2)) in exact x).
Definition LC_33_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_33 3 SC_33) in exact x).
Definition dL_33_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z21A1S2PcA1M1A4SbG0ScS0S0S1Z2ab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fe0A1S2PacA1M4A4SbG0ScS0S0S1Z7ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a528A1S4S13S4S14G1G5A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d0A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2aa0A1G2A4SbG0ScS0S0S1Z160A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z168A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2e0A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2e8A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_33_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S32S19A2S10G0S37A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_33_3)). Qed.
Definition setsL_33_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_33_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 33.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_33 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_33 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_33 (setp rhoB setsC_33))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_33 w setsC_33 (fst dC_33) (snd dC_33)); [reflexivity | reflexivity | exact sdC_33 | | | exact HSP].
    - cbn [fst dC_33]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_33) (snd dC_33) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_33 LC_33 (setp rhoB setsC_33) Q HkB (eq_trans runC_33 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 33 3) med_cnt_tab) with 24. change (class_size 33) with 10912. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_33 0 SC_33) with LC_33_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_33_0 SM1pre setsL_33_0 (fst dL_33_0) (snd dL_33_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_33_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_33_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_33_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 33 3) med_cnt_tab) with 24. change (class_size 33) with 10912. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_33 1 SC_33) with LC_33_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_33_1 SM1pre setsL_33_1 (fst dL_33_1) (snd dL_33_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_33_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_33_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_33_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 33 3) med_cnt_tab) with 24. change (class_size 33) with 10912. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_33 2 SC_33) with LC_33_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_33_2 SM1pre setsL_33_2 (fst dL_33_2) (snd dL_33_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_33_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_33_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_33_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 33 3) med_cnt_tab) with 24. change (class_size 33) with 10912. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_33 3 SC_33) with LC_33_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_33_3 SM1pre setsL_33_3 (fst dL_33_3) (snd dL_33_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_33_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_33_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_33_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c33.

Module Mal_agrp_c34.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_34 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_34 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_34 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS57A2S10G0S3bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_34)). Qed.
Definition setsC_34 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_34)) in exact x).
Definition LC_34_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_34 0 SC_34) in exact x).
Definition dL_34_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z22A1S2PcA1M1A4SbG0ScS0S0S1Z3330A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fe80A1S2PacA1M4A4SbG0ScS0S0S1Z3fe90A1S4S13G4G3A3A4SbG0ScS0S0S1Z14A1S2PafA1M5A4SbG0ScS0S0S1Z5a530A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3320A1G2A4SbG0ScS0S0S1Z168A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z170A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2e8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_34_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S38S19A2S10G0S3cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_34_0)). Qed.
Definition setsL_34_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_34_0)) in exact x).
Definition LC_34_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_34 1 SC_34) in exact x).
Definition dL_34_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z22A1S2PcA1M1A4SbG0ScS0S0S1Z3330A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff40A1S2PacA1M4A4SbG0ScS0S0S1Z1ff50A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a530A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3320A1G2A4SbG0ScS0S0S1Z168A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z170A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2e8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_34_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S39S19A2S10G0S3dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_34_1)). Qed.
Definition setsL_34_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_34_1)) in exact x).
Definition LC_34_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_34 2 SC_34) in exact x).
Definition dL_34_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z22A1S2PcA1M1A4SbG0ScS0S0S1Z3330A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffa0A1S2PacA1M4A4SbG0ScS0S0S1Zffb0A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S2PafA1M5A4SbG0ScS0S0S1Z5a530A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4d8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3320A1G2A4SbG0ScS0S0S1Z168A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z170A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2e8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_34_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S3aS19A2S10G0S3eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_34_2)). Qed.
Definition setsL_34_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_34_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 34.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_34 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_34 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_34 (setp rhoB setsC_34))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_34 w setsC_34 (fst dC_34) (snd dC_34)); [reflexivity | reflexivity | exact sdC_34 | | | exact HSP].
    - cbn [fst dC_34]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_34) (snd dC_34) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_34 LC_34 (setp rhoB setsC_34) Q HkB (eq_trans runC_34 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 34 3) med_cnt_tab) with 20. change (class_size 34) with 13088. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_34 0 SC_34) with LC_34_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_34_0 SM1pre setsL_34_0 (fst dL_34_0) (snd dL_34_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_34_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_34_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_34_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 34 3) med_cnt_tab) with 20. change (class_size 34) with 13088. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_34 1 SC_34) with LC_34_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_34_1 SM1pre setsL_34_1 (fst dL_34_1) (snd dL_34_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_34_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_34_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_34_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 34 3) med_cnt_tab) with 20. change (class_size 34) with 13088. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_34 2 SC_34) with LC_34_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_34_2 SM1pre setsL_34_2 (fst dL_34_2) (snd dL_34_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_34_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_34_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_34_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c34.

Module Mal_agrp_c36.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_36 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_36 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_36 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS58A2S10G0S42A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_36)). Qed.
Definition setsC_36 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_36)) in exact x).
Definition LC_36_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_36 0 SC_36) in exact x).
Definition dL_36_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z24A1S2PcA1M1A4SbG0ScS0S0S1Z4920A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fdc0A1S2PacA1M4A4SbG0ScS0S0S1Z7fdd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z1cA1S2PafA1M5A4SbG0ScS0S0S1Z5a540A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z4910A1G2A4SbG0ScS0S0S1Z178A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z180A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z300A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_36_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S3fS19A2S10G0S43A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_36_0)). Qed.
Definition setsL_36_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_36_0)) in exact x).
Definition LC_36_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_36 1 SC_36) in exact x).
Definition dL_36_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z24A1S2PcA1M1A4SbG0ScS0S0S1Z4920A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fee0A1S2PacA1M4A4SbG0ScS0S0S1Z3fef0A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S2PafA1M5A4SbG0ScS0S0S1Z5a540A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z4910A1G2A4SbG0ScS0S0S1Z178A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z180A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z300A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_36_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S40S19A2S10G0S44A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_36_1)). Qed.
Definition setsL_36_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_36_1)) in exact x).
Definition LC_36_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_36 2 SC_36) in exact x).
Definition dL_36_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z24A1S2PcA1M1A4SbG0ScS0S0S1Z4920A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff70A1S2PacA1M4A4SbG0ScS0S0S1Z1ff80A1S4S13G4G3A3A4SbG0ScS0S0S1Z7A1S2PafA1M5A4SbG0ScS0S0S1Z5a540A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z4910A1G2A4SbG0ScS0S0S1Z178A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z180A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z300A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_36_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S41S19A2S10G0S45A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_36_2)). Qed.
Definition setsL_36_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_36_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 36.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_36 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_36 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_36 (setp rhoB setsC_36))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_36 w setsC_36 (fst dC_36) (snd dC_36)); [reflexivity | reflexivity | exact sdC_36 | | | exact HSP].
    - cbn [fst dC_36]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_36) (snd dC_36) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_36 LC_36 (setp rhoB setsC_36) Q HkB (eq_trans runC_36 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 28).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 36 3) med_cnt_tab) with 28. change (class_size 36) with 18704. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_36 0 SC_36) with LC_36_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_36_0 SM1pre setsL_36_0 (fst dL_36_0) (snd dL_36_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_36_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_36_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_36_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 36 3) med_cnt_tab) with 28. change (class_size 36) with 18704. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_36 1 SC_36) with LC_36_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_36_1 SM1pre setsL_36_1 (fst dL_36_1) (snd dL_36_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_36_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_36_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_36_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 36 3) med_cnt_tab) with 28. change (class_size 36) with 18704. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_36 2 SC_36) with LC_36_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_36_2 SM1pre setsL_36_2 (fst dL_36_2) (snd dL_36_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_36_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_36_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_36_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c36.

Module Mal_agrp_c38.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_38 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_38 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_38 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS5aA2S10G0S52A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_38)). Qed.
Definition setsC_38 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_38)) in exact x).
Definition LC_38_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_38 0 SC_38) in exact x).
Definition dL_38_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z26A1S2PcA1M1A4SbG0ScS0S0S1Z6660A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fe40A1S2PacA1M4A4SbG0ScS0S0S1Z7fe50A1S4S13G4G3A3A4SbG0ScS0S0S1Z14A1S2PafA1M5A4SbG0ScS0S0S1Z5a550A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z6650A1G2A4SbG0ScS0S0S1Z188A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z190A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z308A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z310A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_38_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4fS19A2S10G0S53A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_38_0)). Qed.
Definition setsL_38_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_38_0)) in exact x).
Definition LC_38_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_38 1 SC_38) in exact x).
Definition dL_38_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z26A1S2PcA1M1A4SbG0ScS0S0S1Z6660A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ff20A1S2PacA1M4A4SbG0ScS0S0S1Z3ff30A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a550A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z6650A1G2A4SbG0ScS0S0S1Z188A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z190A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z308A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z310A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_38_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S50S19A2S10G0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_38_1)). Qed.
Definition setsL_38_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_38_1)) in exact x).
Definition LC_38_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_38 2 SC_38) in exact x).
Definition dL_38_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z26A1S2PcA1M1A4SbG0ScS0S0S1Z6660A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff90A1S2PacA1M4A4SbG0ScS0S0S1Z1ffa0A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S2PafA1M5A4SbG0ScS0S0S1Z5a550A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z6650A1G2A4SbG0ScS0S0S1Z188A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z190A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z308A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z310A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_38_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S51S19A2S10G0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_38_2)). Qed.
Definition setsL_38_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_38_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 38.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_38 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_38 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_38 (setp rhoB setsC_38))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_38 w setsC_38 (fst dC_38) (snd dC_38)); [reflexivity | reflexivity | exact sdC_38 | | | exact HSP].
    - cbn [fst dC_38]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_38) (snd dC_38) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_38 LC_38 (setp rhoB setsC_38) Q HkB (eq_trans runC_38 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 38 3) med_cnt_tab) with 20. change (class_size 38) with 26192. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_38 0 SC_38) with LC_38_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_38_0 SM1pre setsL_38_0 (fst dL_38_0) (snd dL_38_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_38_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_38_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_38_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 38 3) med_cnt_tab) with 20. change (class_size 38) with 26192. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_38 1 SC_38) with LC_38_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_38_1 SM1pre setsL_38_1 (fst dL_38_1) (snd dL_38_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_38_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_38_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_38_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 38 3) med_cnt_tab) with 20. change (class_size 38) with 26192. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_38 2 SC_38) with LC_38_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_38_2 SM1pre setsL_38_2 (fst dL_38_2) (snd dL_38_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_38_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_38_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_38_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c38.

Module Mal_agrp_c37.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_37 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_37 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_37 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS59A2S10G0S4aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_37)). Qed.
Definition setsC_37 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_37)) in exact x).
Definition LC_37_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_37 0 SC_37) in exact x).
Definition dL_37_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z25A1S2PcA1M1A4SbG0ScS0S0S1Z5550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fe00A1S2PacA1M4A4SbG0ScS0S0S1Z7fe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a548A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z5540A1G2A4SbG0ScS0S0S1Z180A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z188A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z300A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z308A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_37_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S46S19A2S10G0S4bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_37_0)). Qed.
Definition setsL_37_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_37_0)) in exact x).
Definition LC_37_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_37 1 SC_37) in exact x).
Definition dL_37_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z25A1S2PcA1M1A4SbG0ScS0S0S1Z5550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ff00A1S2PacA1M4A4SbG0ScS0S0S1Z3ff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a548A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z5540A1G2A4SbG0ScS0S0S1Z180A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z188A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z300A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z308A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_37_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S47S19A2S10G0S4cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_37_1)). Qed.
Definition setsL_37_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_37_1)) in exact x).
Definition LC_37_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_37 2 SC_37) in exact x).
Definition dL_37_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z25A1S2PcA1M1A4SbG0ScS0S0S1Z5550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff80A1S2PacA1M4A4SbG0ScS0S0S1Z1ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a548A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z5540A1G2A4SbG0ScS0S0S1Z180A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z188A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z300A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z308A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_37_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S48S19A2S10G0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_37_2)). Qed.
Definition setsL_37_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_37_2)) in exact x).
Definition LC_37_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_37 3 SC_37) in exact x).
Definition dL_37_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z25A1S2PcA1M1A4SbG0ScS0S0S1Z5550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffc0A1S2PacA1M4A4SbG0ScS0S0S1Zffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a548A1S4S13S4S14G1G5A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4f0A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z5540A1G2A4SbG0ScS0S0S1Z180A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z188A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z300A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z308A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_37_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S49S19A2S10G0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_37_3)). Qed.
Definition setsL_37_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_37_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 37.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_37 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_37 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_37 (setp rhoB setsC_37))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_37 w setsC_37 (fst dC_37) (snd dC_37)); [reflexivity | reflexivity | exact sdC_37 | | | exact HSP].
    - cbn [fst dC_37]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_37) (snd dC_37) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_37 LC_37 (setp rhoB setsC_37) Q HkB (eq_trans runC_37 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 37 3) med_cnt_tab) with 24. change (class_size 37) with 21824. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_37 0 SC_37) with LC_37_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_37_0 SM1pre setsL_37_0 (fst dL_37_0) (snd dL_37_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_37_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_37_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_37_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 37 3) med_cnt_tab) with 24. change (class_size 37) with 21824. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_37 1 SC_37) with LC_37_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_37_1 SM1pre setsL_37_1 (fst dL_37_1) (snd dL_37_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_37_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_37_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_37_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 37 3) med_cnt_tab) with 24. change (class_size 37) with 21824. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_37 2 SC_37) with LC_37_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_37_2 SM1pre setsL_37_2 (fst dL_37_2) (snd dL_37_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_37_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_37_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_37_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 37 3) med_cnt_tab) with 24. change (class_size 37) with 21824. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_37 3 SC_37) with LC_37_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_37_3 SM1pre setsL_37_3 (fst dL_37_3) (snd dL_37_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_37_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_37_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_37_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c37.
