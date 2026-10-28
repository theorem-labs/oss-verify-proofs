(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SCsym"; "SN2pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_27"; "SC_29"; "SC_3"; "SC_31"; "SC_32"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c27"; "LC_27_0"; "LC_27_1"; "LC_27_2"; "LC_27_3"; "LC_27_4"; "LC_27_5"; "dC_27"; "dL_27_0"; "dL_27_1"; "dL_27_2"; "dL_27_3"; "dL_27_4"; "dL_27_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c29"; "LC_29_0"; "LC_29_1"; "LC_29_2"; "LC_29_3"; "dC_29"; "dL_29_0"; "dL_29_1"; "dL_29_2"; "dL_29_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c3"; "LC_3_0"; "LC_3_1"; "LC_3_2"; "dC_3"; "dL_3_0"; "dL_3_1"; "dL_3_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c31"; "LC_31_0"; "LC_31_1"; "LC_31_2"; "LC_31_3"; "LC_31_4"; "LC_31_5"; "dC_31"; "dL_31_0"; "dL_31_1"; "dL_31_2"; "dL_31_3"; "dL_31_4"; "dL_31_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c32"; "LC_32_0"; "LC_32_1"; "LC_32_2"; "dC_32"; "dL_32_0"; "dL_32_1"; "dL_32_2"].
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

Module Mal_agrp_c29.

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

Definition dC_29 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_29 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_29 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS30A2S10G0S45A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_29)). Qed.
Definition setsC_29 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_29)) in exact x).
Definition LC_29_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_29 0 SC_29) in exact x).
Definition dL_29_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1dA1S2PcA1M1A4SbG0ScS0S0S1Z1550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1fe00A1S2PacA1M4A4SbG0ScS0S0S1Z1fe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a508A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1540A1G2A4SbG0ScS0S0S1Z140A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z148A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2c0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2c8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_29_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S41S19A2S10G0S46A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_29_0)). Qed.
Definition setsL_29_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_29_0)) in exact x).
Definition LC_29_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_29 1 SC_29) in exact x).
Definition dL_29_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1dA1S2PcA1M1A4SbG0ScS0S0S1Z1550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff00A1S2PacA1M4A4SbG0ScS0S0S1Zff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a508A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1540A1G2A4SbG0ScS0S0S1Z140A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z148A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2c0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2c8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_29_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S42S19A2S10G0S47A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_29_1)). Qed.
Definition setsL_29_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_29_1)) in exact x).
Definition LC_29_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_29 2 SC_29) in exact x).
Definition dL_29_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1dA1S2PcA1M1A4SbG0ScS0S0S1Z1550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7f80A1S2PacA1M4A4SbG0ScS0S0S1Z7f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a508A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1540A1G2A4SbG0ScS0S0S1Z140A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z148A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2c0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2c8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_29_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S43S19A2S10G0S48A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_29_2)). Qed.
Definition setsL_29_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_29_2)) in exact x).
Definition LC_29_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_29 3 SC_29) in exact x).
Definition dL_29_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1dA1S2PcA1M1A4SbG0ScS0S0S1Z1550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fc0A1S2PacA1M4A4SbG0ScS0S0S1Z3fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a508A1S4S13S4S14G1G5A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b0A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1540A1G2A4SbG0ScS0S0S1Z140A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z148A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2c0A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2c8A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_29_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S44S19A2S10G0S49A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_29_3)). Qed.
Definition setsL_29_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_29_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 29.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_29 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_29 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_29 (setp rhoB setsC_29))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_29 w setsC_29 (fst dC_29) (snd dC_29)); [reflexivity | reflexivity | exact sdC_29 | | | exact HSP].
    - cbn [fst dC_29]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_29) (snd dC_29) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_29 LC_29 (setp rhoB setsC_29) Q HkB (eq_trans runC_29 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 29 3) med_cnt_tab) with 24. change (class_size 29) with 5440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_29 0 SC_29) with LC_29_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_29_0 SM1pre setsL_29_0 (fst dL_29_0) (snd dL_29_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_29_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_29_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_29_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 29 3) med_cnt_tab) with 24. change (class_size 29) with 5440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_29 1 SC_29) with LC_29_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_29_1 SM1pre setsL_29_1 (fst dL_29_1) (snd dL_29_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_29_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_29_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_29_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 29 3) med_cnt_tab) with 24. change (class_size 29) with 5440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_29 2 SC_29) with LC_29_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_29_2 SM1pre setsL_29_2 (fst dL_29_2) (snd dL_29_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_29_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_29_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_29_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 29 3) med_cnt_tab) with 24. change (class_size 29) with 5440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_29 3 SC_29) with LC_29_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_29_3 SM1pre setsL_29_3 (fst dL_29_3) (snd dL_29_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_29_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_29_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_29_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c29.

Module Mal_agrp_c27.

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

Definition dC_27 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_27 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_27 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS2fA2S10G0S3aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_27)). Qed.
Definition setsC_27 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_27)) in exact x).
Definition LC_27_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_27 0 SC_27) in exact x).
Definition dL_27_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1bA1S2PcA1M1A4SbG0ScS0S0S1Z1000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1fe00A1S2PacA1M4A4SbG0ScS0S0S1Z1fe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a4f8A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a0A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Zff0A1G2A4SbG0ScS0S0S1Z130A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z138A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2b0A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2b8A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G5A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_27_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S34S19A2S10G0S3bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_27_0)). Qed.
Definition setsL_27_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_27_0)) in exact x).
Definition LC_27_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_27 1 SC_27) in exact x).
Definition dL_27_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1bA1S2PcA1M1A4SbG0ScS0S0S1Z1000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff00A1S2PacA1M4A4SbG0ScS0S0S1Zff10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a4f8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zff0A1G2A4SbG0ScS0S0S1Z130A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z138A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_27_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S35S19A2S10G0S3cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_27_1)). Qed.
Definition setsL_27_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_27_1)) in exact x).
Definition LC_27_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_27 2 SC_27) in exact x).
Definition dL_27_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1bA1S2PcA1M1A4SbG0ScS0S0S1Z1000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7f80A1S2PacA1M4A4SbG0ScS0S0S1Z7f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S2PafA1M5A4SbG0ScS0S0S1Z5a4f8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zff0A1G2A4SbG0ScS0S0S1Z130A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z138A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_27_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S36S19A2S10G0S3dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_27_2)). Qed.
Definition setsL_27_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_27_2)) in exact x).
Definition LC_27_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_27 3 SC_27) in exact x).
Definition dL_27_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1bA1S2PcA1M1A4SbG0ScS0S0S1Z1000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fc0A1S2PacA1M4A4SbG0ScS0S0S1Z3fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S2PafA1M5A4SbG0ScS0S0S1Z5a4f8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zff0A1G2A4SbG0ScS0S0S1Z130A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z138A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_27_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S37S19A2S10G0S3eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_27_3)). Qed.
Definition setsL_27_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_27_3)) in exact x).
Definition LC_27_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_27 4 SC_27) in exact x).
Definition dL_27_4 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1bA1S2PcA1M1A4SbG0ScS0S0S1Z1000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1fe0A1S2PacA1M4A4SbG0ScS0S0S1Z1ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S2PafA1M5A4SbG0ScS0S0S1Z5a4f8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zff0A1G2A4SbG0ScS0S0S1Z130A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z138A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_27_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S38S19A2S10G0S3fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_27_4)). Qed.
Definition setsL_27_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_27_4)) in exact x).
Definition LC_27_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_27 5 SC_27) in exact x).
Definition dL_27_5 : list (sv * sv) * list sprop := ltac2:(tb__ "0|c|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1bA1S2PcA1M1A4SbG0ScS0S0S1Z1000A1M2S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Zff0A1M5S2PacA1M6A4SbG0ScS0S0G2S4S13G6G4A3A4SbG0ScS0S0S1Z1A1M7S2PafA1M8A4SbG0ScS0S0S1Z5a4f8A1S4S13S4S14G1S1Z3A1A3M9S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a0A1S4S13G9S1Z5a3c8A1A3A4SbG0ScS0S0G5G3A4SbG0ScS0S0S1Z130A1S4S13G9S1Z58A1A3A4MaSbG0ScS0S0S1Z138A1S4S13G9S1Z60A1A3A4SbG0GaSbG0ScS0S0S1Z2b0A1S4S13G9S1Z1d8A1A3A4MbSbG0ScS0S0S1Z2b8A1S4S13G9S1Z1e0A1A3A4SbG0GbSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G8S1Z20A1A2SbS3S5G7G8A2SbS3S5G6S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_27_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S39S19A2S10G0S40A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_27_5)). Qed.
Definition setsL_27_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_27_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 27.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_27 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_27 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_27 (setp rhoB setsC_27))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_27 w setsC_27 (fst dC_27) (snd dC_27)); [reflexivity | reflexivity | exact sdC_27 | | | exact HSP].
    - cbn [fst dC_27]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_27) (snd dC_27) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_27 LC_27 (setp rhoB setsC_27) Q HkB (eq_trans runC_27 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 27 3) med_cnt_tab) with 32. change (class_size 27) with 4080. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_27 0 SC_27) with LC_27_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_27_0 SM1pre setsL_27_0 (fst dL_27_0) (snd dL_27_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_27_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_27_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_27_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 27 3) med_cnt_tab) with 32. change (class_size 27) with 4080. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_27 1 SC_27) with LC_27_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_27_1 SM1pre setsL_27_1 (fst dL_27_1) (snd dL_27_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_27_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_27_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_27_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 27 3) med_cnt_tab) with 32. change (class_size 27) with 4080. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_27 2 SC_27) with LC_27_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_27_2 SM1pre setsL_27_2 (fst dL_27_2) (snd dL_27_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_27_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_27_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_27_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 27 3) med_cnt_tab) with 32. change (class_size 27) with 4080. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_27 3 SC_27) with LC_27_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_27_3 SM1pre setsL_27_3 (fst dL_27_3) (snd dL_27_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_27_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_27_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_27_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 27 3) med_cnt_tab) with 32. change (class_size 27) with 4080. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_27 4 SC_27) with LC_27_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_27_4 SM1pre setsL_27_4 (fst dL_27_4) (snd dL_27_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_27_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_27_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_27_4) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 1).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 27 3) med_cnt_tab) with 32. change (class_size 27) with 4080. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_27 5 SC_27) with LC_27_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_27_5 SM1pre setsL_27_5 (fst dL_27_5) (snd dL_27_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_27_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_27_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_27_5) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c27.

Module Mal_agrp_c3.

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

Definition dC_3 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_3 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS31A2S10G0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_3)). Qed.
Definition setsC_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_3)) in exact x).
Definition LC_3_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_3 0 SC_3) in exact x).
Definition dL_3_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_3_0 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_3_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4aS1bA2S10G0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_3_0)). Qed.
Definition setsL_3_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_3_0)) in exact x).
Definition LC_3_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_3 1 SC_3) in exact x).
Definition dL_3_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_3_1 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_3_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4bS1bA2S10G0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_3_1)). Qed.
Definition setsL_3_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_3_1)) in exact x).
Definition LC_3_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_3 2 SC_3) in exact x).
Definition dL_3_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_3_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_3_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4cS1bA2S10G0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_3_2)). Qed.
Definition setsL_3_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_3_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 3.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_3 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_3 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_3 (setp rhoB setsC_3))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_3 w setsC_3 (fst dC_3) (snd dC_3)); [reflexivity | reflexivity | exact sdC_3 | | | exact HSP].
    - cbn [fst dC_3]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_3) (snd dC_3) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_3 LC_3 (setp rhoB setsC_3) Q HkB (eq_trans runC_3 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 124 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 124)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 31).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 3 (usg ia) 31 15 7) by reflexivity.
      change (class_size 3) with 64. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 1996) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_3 0 SC_3) with LC_3_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_3_0 SN2pre setsL_3_0 (fst dL_3_0) (snd dL_3_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_3_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_3_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_3_0) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 1996 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 60 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 60)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 124 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 124))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 15).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 3 (usg ia) 31 15 7) by reflexivity.
      change (class_size 3) with 64. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 972) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_3 1 SC_3) with LC_3_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_3_1 SN2pre setsL_3_1 (fst dL_3_1) (snd dL_3_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_3_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_3_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_3_1) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 972 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 60 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 60))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 124 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 124))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 3 (usg ia) 31 15 7) by reflexivity.
      change (class_size 3) with 64. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 460) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_3 2 SC_3) with LC_3_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_3_2 SN2pre setsL_3_2 (fst dL_3_2) (snd dL_3_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_3_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_3_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_3_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 460 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c3.

Module Mal_agrp_c32.

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

Definition dC_32 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_32 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_32 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS33A2S10G0S61A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_32)). Qed.
Definition setsC_32 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_32)) in exact x).
Definition LC_32_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_32 0 SC_32) in exact x).
Definition dL_32_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z20A1M1S2PcA1M2A4SbG0ScS0S0S1Z2490A1S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Z3fe00A1S2PacA1M5A4SbG0ScS0S0S1Z3fe10A1S4S13G5G4A3A4SbG0ScS0S0S1Z1cA1S2PafA1M6A4SbG0ScS0S0S1Z5a520A1S4S13S4S14G2S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c8A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2480A1G3A4SbG0ScS0S0S1Z158A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z160A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2d8A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2e0A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G1A2SbS3S5S1Z1A1G6A2SbS3S5G5S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G2S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_32_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S5eS19A2S10G0S62A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_32_0)). Qed.
Definition setsL_32_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_32_0)) in exact x).
Definition LC_32_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_32 1 SC_32) in exact x).
Definition dL_32_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z20A1M1S2PcA1M2A4SbG0ScS0S0S1Z2490A1S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Z1ff00A1S2PacA1M5A4SbG0ScS0S0S1Z1ff10A1S4S13G5G4A3A4SbG0ScS0S0S1ZeA1S2PafA1M6A4SbG0ScS0S0S1Z5a520A1S4S13S4S14G2S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c8A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2480A1G3A4SbG0ScS0S0S1Z158A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z160A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2d8A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2e0A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G1A2SbS3S5S1Z1A1G6A2SbS3S5G5S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G2S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_32_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S5fS19A2S10G0S63A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_32_1)). Qed.
Definition setsL_32_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_32_1)) in exact x).
Definition LC_32_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_32 2 SC_32) in exact x).
Definition dL_32_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z20A1M1S2PcA1M2A4SbG0ScS0S0S1Z2490A1S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Zff80A1S2PacA1M5A4SbG0ScS0S0S1Zff90A1S4S13G5G4A3A4SbG0ScS0S0S1Z7A1S2PafA1M6A4SbG0ScS0S0S1Z5a520A1S4S13S4S14G2S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c8A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2480A1G3A4SbG0ScS0S0S1Z158A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z160A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2d8A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2e0A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G1A2SbS3S5S1Z1A1G6A2SbS3S5G5S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G2S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_32_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S60S19A2S10G0S64A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_32_2)). Qed.
Definition setsL_32_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_32_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 32.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_32 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_32 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_32 (setp rhoB setsC_32))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_32 w setsC_32 (fst dC_32) (snd dC_32)); [reflexivity | reflexivity | exact sdC_32 | | | exact HSP].
    - cbn [fst dC_32]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_32) (snd dC_32) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_32 LC_32 (setp rhoB setsC_32) Q HkB (eq_trans runC_32 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 28).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 32 3) med_cnt_tab) with 28. change (class_size 32) with 9344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_32 0 SC_32) with LC_32_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_32_0 SM1pre setsL_32_0 (fst dL_32_0) (snd dL_32_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_32_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_32_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_32_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 32 3) med_cnt_tab) with 28. change (class_size 32) with 9344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_32 1 SC_32) with LC_32_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_32_1 SM1pre setsL_32_1 (fst dL_32_1) (snd dL_32_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_32_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_32_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_32_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 32 3) med_cnt_tab) with 28. change (class_size 32) with 9344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_32 2 SC_32) with LC_32_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_32_2 SM1pre setsL_32_2 (fst dL_32_2) (snd dL_32_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_32_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_32_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_32_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c32.

Module Mal_agrp_c31.

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

Definition dC_31 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_31 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_31 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS32A2S10G0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_31)). Qed.
Definition setsC_31 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_31)) in exact x).
Definition LC_31_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_31 0 SC_31) in exact x).
Definition dL_31_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1fA1S2PcA1M1A4SbG0ScS0S0S1Z2000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fe00A1S2PacA1M4A4SbG0ScS0S0S1Z3fe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a518A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c0A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1ff0A1G2A4SbG0ScS0S0S1Z150A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z158A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2d0A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2d8A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G5A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_31_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S51S19A2S10G0S58A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_31_0)). Qed.
Definition setsL_31_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_31_0)) in exact x).
Definition LC_31_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_31 1 SC_31) in exact x).
Definition dL_31_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1fA1S2PcA1M1A4SbG0ScS0S0S1Z2000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff00A1S2PacA1M4A4SbG0ScS0S0S1Z1ff10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a518A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1ff0A1G2A4SbG0ScS0S0S1Z150A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z158A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_31_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S52S19A2S10G0S59A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_31_1)). Qed.
Definition setsL_31_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_31_1)) in exact x).
Definition LC_31_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_31 2 SC_31) in exact x).
Definition dL_31_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1fA1S2PcA1M1A4SbG0ScS0S0S1Z2000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff80A1S2PacA1M4A4SbG0ScS0S0S1Zff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S2PafA1M5A4SbG0ScS0S0S1Z5a518A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1ff0A1G2A4SbG0ScS0S0S1Z150A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z158A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_31_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S53S19A2S10G0S5aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_31_2)). Qed.
Definition setsL_31_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_31_2)) in exact x).
Definition LC_31_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_31 3 SC_31) in exact x).
Definition dL_31_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1fA1S2PcA1M1A4SbG0ScS0S0S1Z2000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fc0A1S2PacA1M4A4SbG0ScS0S0S1Z7fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S2PafA1M5A4SbG0ScS0S0S1Z5a518A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1ff0A1G2A4SbG0ScS0S0S1Z150A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z158A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_31_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S54S19A2S10G0S5bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_31_3)). Qed.
Definition setsL_31_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_31_3)) in exact x).
Definition LC_31_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_31 4 SC_31) in exact x).
Definition dL_31_4 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1fA1S2PcA1M1A4SbG0ScS0S0S1Z2000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fe0A1S2PacA1M4A4SbG0ScS0S0S1Z3ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S2PafA1M5A4SbG0ScS0S0S1Z5a518A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1ff0A1G2A4SbG0ScS0S0S1Z150A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z158A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_31_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S55S19A2S10G0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_31_4)). Qed.
Definition setsL_31_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_31_4)) in exact x).
Definition LC_31_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_31 5 SC_31) in exact x).
Definition dL_31_5 : list (sv * sv) * list sprop := ltac2:(tb__ "0|c|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1fA1S2PcA1M1A4SbG0ScS0S0S1Z2000A1M2S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Z1ff0A1M5S2PacA1M6A4SbG0ScS0S0G2S4S13G6G4A3A4SbG0ScS0S0S1Z1A1M7S2PafA1M8A4SbG0ScS0S0S1Z5a518A1S4S13S4S14G1S1Z3A1A3M9S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4c0A1S4S13G9S1Z5a3c8A1A3A4SbG0ScS0S0G5G3A4SbG0ScS0S0S1Z150A1S4S13G9S1Z58A1A3A4MaSbG0ScS0S0S1Z158A1S4S13G9S1Z60A1A3A4SbG0GaSbG0ScS0S0S1Z2d0A1S4S13G9S1Z1d8A1A3A4MbSbG0ScS0S0S1Z2d8A1S4S13G9S1Z1e0A1A3A4SbG0GbSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G8S1Z20A1A2SbS3S5G7G8A2SbS3S5G6S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_31_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S56S19A2S10G0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_31_5)). Qed.
Definition setsL_31_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_31_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 31.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_31 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_31 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_31 (setp rhoB setsC_31))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_31 w setsC_31 (fst dC_31) (snd dC_31)); [reflexivity | reflexivity | exact sdC_31 | | | exact HSP].
    - cbn [fst dC_31]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_31) (snd dC_31) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_31 LC_31 (setp rhoB setsC_31) Q HkB (eq_trans runC_31 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 31 3) med_cnt_tab) with 32. change (class_size 31) with 8176. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_31 0 SC_31) with LC_31_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_31_0 SM1pre setsL_31_0 (fst dL_31_0) (snd dL_31_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_31_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_31_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_31_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 31 3) med_cnt_tab) with 32. change (class_size 31) with 8176. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_31 1 SC_31) with LC_31_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_31_1 SM1pre setsL_31_1 (fst dL_31_1) (snd dL_31_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_31_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_31_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_31_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 31 3) med_cnt_tab) with 32. change (class_size 31) with 8176. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_31 2 SC_31) with LC_31_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_31_2 SM1pre setsL_31_2 (fst dL_31_2) (snd dL_31_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_31_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_31_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_31_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 31 3) med_cnt_tab) with 32. change (class_size 31) with 8176. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_31 3 SC_31) with LC_31_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_31_3 SM1pre setsL_31_3 (fst dL_31_3) (snd dL_31_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_31_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_31_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_31_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 31 3) med_cnt_tab) with 32. change (class_size 31) with 8176. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_31 4 SC_31) with LC_31_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_31_4 SM1pre setsL_31_4 (fst dL_31_4) (snd dL_31_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_31_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_31_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_31_4) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 1).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 31 3) med_cnt_tab) with 32. change (class_size 31) with 8176. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_31 5 SC_31) with LC_31_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_31_5 SM1pre setsL_31_5 (fst dL_31_5) (snd dL_31_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_31_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_31_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_31_5) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c31.
