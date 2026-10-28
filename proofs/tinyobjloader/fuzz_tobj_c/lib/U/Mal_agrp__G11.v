(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SCsym"; "SN2pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c35"; "LC_35_0"; "LC_35_1"; "LC_35_2"; "LC_35_3"; "LC_35_4"; "LC_35_5"; "dC_35"; "dL_35_0"; "dL_35_1"; "dL_35_2"; "dL_35_3"; "dL_35_4"; "dL_35_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c39"; "LC_39_0"; "LC_39_1"; "LC_39_2"; "LC_39_3"; "LC_39_4"; "LC_39_5"; "dC_39"; "dL_39_0"; "dL_39_1"; "dL_39_2"; "dL_39_3"; "dL_39_4"; "dL_39_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c40"; "LC_40_0"; "LC_40_1"; "LC_40_2"; "dC_40"; "dL_40_0"; "dL_40_1"; "dL_40_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c41"; "LC_41_0"; "LC_41_1"; "LC_41_2"; "LC_41_3"; "dC_41"; "dL_41_0"; "dL_41_1"; "dL_41_2"; "dL_41_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c42"; "LC_42_0"; "LC_42_1"; "LC_42_2"; "dC_42"; "dL_42_0"; "dL_42_1"; "dL_42_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_35"; "SC_39"; "SC_40"; "SC_41"; "SC_42"].
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

Module Mal_agrp_c35.

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

Definition dC_35 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_35 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_35 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S1aS60A2S10G0S35A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_35)). Qed.
Definition setsC_35 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_35)) in exact x).
Definition LC_35_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_35 0 SC_35) in exact x).
Definition dL_35_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z23A1S3PcA1M1A4SbG0ScS0S0S1Z4000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fe00A1S3PacA1M4A4SbG0ScS0S0S1Z7fe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S3PafA1M6A4SbG0ScS0S0S1Z5a538A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e0A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3ff0A1G2A4SbG0ScS0S0S1Z170A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z178A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2f0A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2f8A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G6G5A2SbS2S5S1Z1A1G6A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_35_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S2fS19A2S10G0S36A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_35_0)). Qed.
Definition setsL_35_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_35_0)) in exact x).
Definition LC_35_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_35 1 SC_35) in exact x).
Definition dL_35_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z23A1S3PcA1M1A4SbG0ScS0S0S1Z4000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ff00A1S3PacA1M4A4SbG0ScS0S0S1Z3ff10A1S4S13G4G3A3A4SbG0ScS0S0G3S3PafA1M5A4SbG0ScS0S0S1Z5a538A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3ff0A1G2A4SbG0ScS0S0S1Z170A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z178A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_35_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S30S19A2S10G0S37A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_35_1)). Qed.
Definition setsL_35_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_35_1)) in exact x).
Definition LC_35_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_35 2 SC_35) in exact x).
Definition dL_35_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z23A1S3PcA1M1A4SbG0ScS0S0S1Z4000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff80A1S3PacA1M4A4SbG0ScS0S0S1Z1ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S3PafA1M5A4SbG0ScS0S0S1Z5a538A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3ff0A1G2A4SbG0ScS0S0S1Z170A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z178A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_35_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S31S19A2S10G0S38A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_35_2)). Qed.
Definition setsL_35_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_35_2)) in exact x).
Definition LC_35_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_35 3 SC_35) in exact x).
Definition dL_35_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z23A1S3PcA1M1A4SbG0ScS0S0S1Z4000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffc0A1S3PacA1M4A4SbG0ScS0S0S1Zffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S3PafA1M5A4SbG0ScS0S0S1Z5a538A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3ff0A1G2A4SbG0ScS0S0S1Z170A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z178A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_35_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S32S19A2S10G0S39A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_35_3)). Qed.
Definition setsL_35_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_35_3)) in exact x).
Definition LC_35_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_35 4 SC_35) in exact x).
Definition dL_35_4 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z23A1S3PcA1M1A4SbG0ScS0S0S1Z4000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fe0A1S3PacA1M4A4SbG0ScS0S0S1Z7ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S3PafA1M5A4SbG0ScS0S0S1Z5a538A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e0A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3ff0A1G2A4SbG0ScS0S0S1Z170A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z178A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2f0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2f8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_35_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S33S19A2S10G0S3aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_35_4)). Qed.
Definition setsL_35_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_35_4)) in exact x).
Definition LC_35_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_35 5 SC_35) in exact x).
Definition dL_35_5 : list (sv * sv) * list sprop := ltac2:(tb__ "0|c|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z23A1S3PcA1M1A4SbG0ScS0S0S1Z4000A1M2S4S13S3PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Z3ff0A1M5S3PacA1M6A4SbG0ScS0S0G2S4S13G6G4A3A4SbG0ScS0S0S1Z1A1M7S3PafA1M8A4SbG0ScS0S0S1Z5a538A1S4S13S4S14G1S1Z3A1A3M9S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4e0A1S4S13G9S1Z5a3c8A1A3A4SbG0ScS0S0G5G3A4SbG0ScS0S0S1Z170A1S4S13G9S1Z58A1A3A4MaSbG0ScS0S0S1Z178A1S4S13G9S1Z60A1A3A4SbG0GaSbG0ScS0S0S1Z2f0A1S4S13G9S1Z1d8A1A3A4MbSbG0ScS0S0S1Z2f8A1S4S13G9S1Z1e0A1A3A4SbG0GbSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G8S1Z20A1A2SbS2S5G7G8A2SbS2S5G6S1Z800000A1A2SbS2S5G4G3A2SbS2S5G3S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_35_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S34S19A2S10G0S3bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_35_5)). Qed.
Definition setsL_35_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_35_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 35.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_35 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_35 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_35 (setp rhoB setsC_35))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_35 w setsC_35 (fst dC_35) (snd dC_35)); [reflexivity | reflexivity | exact sdC_35 | | | exact HSP].
    - cbn [fst dC_35]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_35) (snd dC_35) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_35 LC_35 (setp rhoB setsC_35) Q HkB (eq_trans runC_35 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 35 3) med_cnt_tab) with 32. change (class_size 35) with 16368. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_35 0 SC_35) with LC_35_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_35_0 SM1pre setsL_35_0 (fst dL_35_0) (snd dL_35_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_35_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_35_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_35_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 35 3) med_cnt_tab) with 32. change (class_size 35) with 16368. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_35 1 SC_35) with LC_35_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_35_1 SM1pre setsL_35_1 (fst dL_35_1) (snd dL_35_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_35_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_35_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_35_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 35 3) med_cnt_tab) with 32. change (class_size 35) with 16368. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_35 2 SC_35) with LC_35_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_35_2 SM1pre setsL_35_2 (fst dL_35_2) (snd dL_35_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_35_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_35_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_35_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 35 3) med_cnt_tab) with 32. change (class_size 35) with 16368. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_35 3 SC_35) with LC_35_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_35_3 SM1pre setsL_35_3 (fst dL_35_3) (snd dL_35_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_35_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_35_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_35_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 35 3) med_cnt_tab) with 32. change (class_size 35) with 16368. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_35 4 SC_35) with LC_35_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_35_4 SM1pre setsL_35_4 (fst dL_35_4) (snd dL_35_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_35_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_35_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_35_4) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 1).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 35 3) med_cnt_tab) with 32. change (class_size 35) with 16368. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_35 5 SC_35) with LC_35_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_35_5 SM1pre setsL_35_5 (fst dL_35_5) (snd dL_35_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_35_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_35_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_35_5) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c35.

Module Mal_agrp_c40.

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

Definition dC_40 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_40 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_40 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S1aS62A2S10G0S4cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_40)). Qed.
Definition setsC_40 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_40)) in exact x).
Definition LC_40_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_40 0 SC_40) in exact x).
Definition dL_40_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z28A1S3PcA1M1A4SbG0ScS0S0S1Z9250A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S3PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1Z1cA1S3PafA1M5A4SbG0ScS0S0S1Z5a560A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a508A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z9240A1G2A4SbG0ScS0S0S1Z198A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1a0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z318A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z320A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_40_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S49S19A2S10G0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_40_0)). Qed.
Definition setsL_40_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_40_0)) in exact x).
Definition LC_40_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_40 1 SC_40) in exact x).
Definition dL_40_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z28A1S3PcA1M1A4SbG0ScS0S0S1Z9250A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S3PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S3PafA1M5A4SbG0ScS0S0S1Z5a560A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a508A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z9240A1G2A4SbG0ScS0S0S1Z198A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1a0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z318A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z320A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_40_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S4aS19A2S10G0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_40_1)). Qed.
Definition setsL_40_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_40_1)) in exact x).
Definition LC_40_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_40 2 SC_40) in exact x).
Definition dL_40_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z28A1S3PcA1M1A4SbG0ScS0S0S1Z9250A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ffc0A1S3PacA1M4A4SbG0ScS0S0S1Z3ffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z7A1S3PafA1M5A4SbG0ScS0S0S1Z5a560A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a508A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z9240A1G2A4SbG0ScS0S0S1Z198A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1a0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z318A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z320A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_40_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S4bS19A2S10G0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_40_2)). Qed.
Definition setsL_40_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_40_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 40.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_40 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_40 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_40 (setp rhoB setsC_40))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_40 w setsC_40 (fst dC_40) (snd dC_40)); [reflexivity | reflexivity | exact sdC_40 | | | exact HSP].
    - cbn [fst dC_40]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_40) (snd dC_40) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_40 LC_40 (setp rhoB setsC_40) Q HkB (eq_trans runC_40 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 28).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 40 3) med_cnt_tab) with 28. change (class_size 40) with 37440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_40 0 SC_40) with LC_40_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_40_0 SM1pre setsL_40_0 (fst dL_40_0) (snd dL_40_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_40_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_40_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_40_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 40 3) med_cnt_tab) with 28. change (class_size 40) with 37440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_40 1 SC_40) with LC_40_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_40_1 SM1pre setsL_40_1 (fst dL_40_1) (snd dL_40_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_40_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_40_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_40_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 40 3) med_cnt_tab) with 28. change (class_size 40) with 37440. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_40 2 SC_40) with LC_40_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_40_2 SM1pre setsL_40_2 (fst dL_40_2) (snd dL_40_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_40_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_40_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_40_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c40.

Module Mal_agrp_c42.

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

Definition dC_42 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_42 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_42 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S1aS64A2S10G0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_42)). Qed.
Definition setsC_42 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_42)) in exact x).
Definition LC_42_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_42 0 SC_42) in exact x).
Definition dL_42_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z2aA1S3PcA1M1A4SbG0ScS0S0S1Zccd0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S3PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1Z14A1S3PafA1M5A4SbG0ScS0S0S1Z5a570A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a518A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zccc0A1G2A4SbG0ScS0S0S1Z1a8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z328A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z330A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_42_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S59S19A2S10G0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_42_0)). Qed.
Definition setsL_42_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_42_0)) in exact x).
Definition LC_42_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_42 1 SC_42) in exact x).
Definition dL_42_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z2aA1S3PcA1M1A4SbG0ScS0S0S1Zccd0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S3PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S3PafA1M5A4SbG0ScS0S0S1Z5a570A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a518A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zccc0A1G2A4SbG0ScS0S0S1Z1a8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z328A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z330A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_42_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S5aS19A2S10G0S5eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_42_1)). Qed.
Definition setsL_42_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_42_1)) in exact x).
Definition LC_42_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_42 2 SC_42) in exact x).
Definition dL_42_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z2aA1S3PcA1M1A4SbG0ScS0S0S1Zccd0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ffc0A1S3PacA1M4A4SbG0ScS0S0S1Z3ffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S3PafA1M5A4SbG0ScS0S0S1Z5a570A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a518A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zccc0A1G2A4SbG0ScS0S0S1Z1a8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z328A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z330A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_42_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S5bS19A2S10G0S5fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_42_2)). Qed.
Definition setsL_42_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_42_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 42.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_42 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_42 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_42 (setp rhoB setsC_42))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_42 w setsC_42 (fst dC_42) (snd dC_42)); [reflexivity | reflexivity | exact sdC_42 | | | exact HSP].
    - cbn [fst dC_42]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_42) (snd dC_42) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_42 LC_42 (setp rhoB setsC_42) Q HkB (eq_trans runC_42 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 42 3) med_cnt_tab) with 20. change (class_size 42) with 52416. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_42 0 SC_42) with LC_42_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_42_0 SM1pre setsL_42_0 (fst dL_42_0) (snd dL_42_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_42_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_42_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_42_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 42 3) med_cnt_tab) with 20. change (class_size 42) with 52416. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_42 1 SC_42) with LC_42_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_42_1 SM1pre setsL_42_1 (fst dL_42_1) (snd dL_42_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_42_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_42_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_42_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 42 3) med_cnt_tab) with 20. change (class_size 42) with 52416. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_42 2 SC_42) with LC_42_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_42_2 SM1pre setsL_42_2 (fst dL_42_2) (snd dL_42_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_42_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_42_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_42_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c42.

Module Mal_agrp_c39.

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

Definition dC_39 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_39 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_39 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S1aS61A2S10G0S42A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_39)). Qed.
Definition setsC_39 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_39)) in exact x).
Definition LC_39_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_39 0 SC_39) in exact x).
Definition dL_39_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z27A1S3PcA1M1A4SbG0ScS0S0S1Z8000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffe00A1S3PacA1M4A4SbG0ScS0S0S1Zffe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S3PafA1M6A4SbG0ScS0S0S1Z5a558A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a500A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7ff0A1G2A4SbG0ScS0S0S1Z190A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z198A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z310A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z318A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G6G5A2SbS2S5S1Z1A1G6A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_39_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S3cS19A2S10G0S43A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_39_0)). Qed.
Definition setsL_39_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_39_0)) in exact x).
Definition LC_39_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_39 1 SC_39) in exact x).
Definition dL_39_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z27A1S3PcA1M1A4SbG0ScS0S0S1Z8000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff00A1S3PacA1M4A4SbG0ScS0S0S1Z7ff10A1S4S13G4G3A3A4SbG0ScS0S0G3S3PafA1M5A4SbG0ScS0S0S1Z5a558A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a500A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7ff0A1G2A4SbG0ScS0S0S1Z190A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z198A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z310A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z318A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_39_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S3dS19A2S10G0S44A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_39_1)). Qed.
Definition setsL_39_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_39_1)) in exact x).
Definition LC_39_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_39 2 SC_39) in exact x).
Definition dL_39_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z27A1S3PcA1M1A4SbG0ScS0S0S1Z8000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ff80A1S3PacA1M4A4SbG0ScS0S0S1Z3ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S3PafA1M5A4SbG0ScS0S0S1Z5a558A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a500A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7ff0A1G2A4SbG0ScS0S0S1Z190A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z198A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z310A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z318A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_39_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S3eS19A2S10G0S45A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_39_2)). Qed.
Definition setsL_39_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_39_2)) in exact x).
Definition LC_39_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_39 3 SC_39) in exact x).
Definition dL_39_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z27A1S3PcA1M1A4SbG0ScS0S0S1Z8000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ffc0A1S3PacA1M4A4SbG0ScS0S0S1Z1ffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S3PafA1M5A4SbG0ScS0S0S1Z5a558A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a500A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7ff0A1G2A4SbG0ScS0S0S1Z190A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z198A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z310A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z318A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_39_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S3fS19A2S10G0S46A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_39_3)). Qed.
Definition setsL_39_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_39_3)) in exact x).
Definition LC_39_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_39 4 SC_39) in exact x).
Definition dL_39_4 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z27A1S3PcA1M1A4SbG0ScS0S0S1Z8000A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffe0A1S3PacA1M4A4SbG0ScS0S0S1Zfff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S3PafA1M5A4SbG0ScS0S0S1Z5a558A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a500A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7ff0A1G2A4SbG0ScS0S0S1Z190A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z198A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z310A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z318A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_39_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S40S19A2S10G0S47A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_39_4)). Qed.
Definition setsL_39_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_39_4)) in exact x).
Definition LC_39_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_39 5 SC_39) in exact x).
Definition dL_39_5 : list (sv * sv) * list sprop := ltac2:(tb__ "0|c|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z27A1S3PcA1M1A4SbG0ScS0S0S1Z8000A1M2S4S13S3PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Z7ff0A1M5S3PacA1M6A4SbG0ScS0S0G2S4S13G6G4A3A4SbG0ScS0S0S1Z1A1M7S3PafA1M8A4SbG0ScS0S0S1Z5a558A1S4S13S4S14G1S1Z3A1A3M9S1Z5a420A1A3A4SbG0ScS0S0S1Z5a500A1S4S13G9S1Z5a3c8A1A3A4SbG0ScS0S0G5G3A4SbG0ScS0S0S1Z190A1S4S13G9S1Z58A1A3A4MaSbG0ScS0S0S1Z198A1S4S13G9S1Z60A1A3A4SbG0GaSbG0ScS0S0S1Z310A1S4S13G9S1Z1d8A1A3A4MbSbG0ScS0S0S1Z318A1S4S13G9S1Z1e0A1A3A4SbG0GbSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G8S1Z20A1A2SbS2S5G7G8A2SbS2S5G6S1Z800000A1A2SbS2S5G4G3A2SbS2S5G3S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_39_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S41S19A2S10G0S48A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_39_5)). Qed.
Definition setsL_39_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_39_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 39.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_39 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_39 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_39 (setp rhoB setsC_39))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_39 w setsC_39 (fst dC_39) (snd dC_39)); [reflexivity | reflexivity | exact sdC_39 | | | exact HSP].
    - cbn [fst dC_39]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_39) (snd dC_39) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_39 LC_39 (setp rhoB setsC_39) Q HkB (eq_trans runC_39 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 39 3) med_cnt_tab) with 32. change (class_size 39) with 32752. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_39 0 SC_39) with LC_39_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_39_0 SM1pre setsL_39_0 (fst dL_39_0) (snd dL_39_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_39_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_39_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_39_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 39 3) med_cnt_tab) with 32. change (class_size 39) with 32752. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_39 1 SC_39) with LC_39_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_39_1 SM1pre setsL_39_1 (fst dL_39_1) (snd dL_39_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_39_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_39_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_39_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 39 3) med_cnt_tab) with 32. change (class_size 39) with 32752. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_39 2 SC_39) with LC_39_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_39_2 SM1pre setsL_39_2 (fst dL_39_2) (snd dL_39_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_39_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_39_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_39_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 39 3) med_cnt_tab) with 32. change (class_size 39) with 32752. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_39 3 SC_39) with LC_39_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_39_3 SM1pre setsL_39_3 (fst dL_39_3) (snd dL_39_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_39_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_39_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_39_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 39 3) med_cnt_tab) with 32. change (class_size 39) with 32752. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_39 4 SC_39) with LC_39_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_39_4 SM1pre setsL_39_4 (fst dL_39_4) (snd dL_39_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_39_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_39_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_39_4) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 1).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 39 3) med_cnt_tab) with 32. change (class_size 39) with 32752. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_39 5 SC_39) with LC_39_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_39_5 SM1pre setsL_39_5 (fst dL_39_5) (snd dL_39_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_39_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_39_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_39_5) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c39.

Module Mal_agrp_c41.

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

Definition dC_41 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_41 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_41 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S1aS63A2S10G0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_41)). Qed.
Definition setsC_41 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_41)) in exact x).
Definition LC_41_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_41 0 SC_41) in exact x).
Definition dL_41_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z29A1S3PcA1M1A4SbG0ScS0S0S1Zaab0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S3PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S3PafA1M5A4SbG0ScS0S0S1Z5a568A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a510A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaaa0A1G2A4SbG0ScS0S0S1Z1a0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1a8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z320A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z328A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_41_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S50S19A2S10G0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_41_0)). Qed.
Definition setsL_41_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_41_0)) in exact x).
Definition LC_41_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_41 1 SC_41) in exact x).
Definition dL_41_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z29A1S3PcA1M1A4SbG0ScS0S0S1Zaab0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S3PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S3PafA1M5A4SbG0ScS0S0S1Z5a568A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a510A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaaa0A1G2A4SbG0ScS0S0S1Z1a0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1a8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z320A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z328A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_41_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S51S19A2S10G0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_41_1)). Qed.
Definition setsL_41_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_41_1)) in exact x).
Definition LC_41_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_41 2 SC_41) in exact x).
Definition dL_41_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z29A1S3PcA1M1A4SbG0ScS0S0S1Zaab0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ffc0A1S3PacA1M4A4SbG0ScS0S0S1Z3ffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S3PafA1M5A4SbG0ScS0S0S1Z5a568A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a510A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaaa0A1G2A4SbG0ScS0S0S1Z1a0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1a8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z320A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z328A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G5S1Z20A1A2SbS2S5S1Z1A1G5A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2S1Z1fff0A1A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_41_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S52S19A2S10G0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_41_2)). Qed.
Definition setsL_41_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_41_2)) in exact x).
Definition LC_41_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_41 3 SC_41) in exact x).
Definition dL_41_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|b|
ScSdSeS0S0A2M0A1SdS2A1SbG0ScS0S0S1Z29A1S3PcA1M1A4SbG0ScS0S0S1Zaab0A1S4S13S3PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ffe0A1S3PacA1M4A4SbG0ScS0S0S1Z1fff0A1M5S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M6S3PafA1M7A4SbG0ScS0S0S1Z5a568A1S4S13S4S14G1G6A3M8S1Z5a420A1A3A4SbG0ScS0S0S1Z5a510A1S4S13G8S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaaa0A1G2A4SbG0ScS0S0S1Z1a0A1S4S13G8S1Z58A1A3A4M9SbG0ScS0S0S1Z1a8A1S4S13G8S1Z60A1A3A4SbG0G9SbG0ScS0S0S1Z320A1S4S13G8S1Z1d8A1A3A4MaSbG0ScS0S0S1Z328A1S4S13G8S1Z1e0A1A3A4SbG0GaSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS2S5G7S1Z20A1A2SbS2S5S1Z1A1G7A2SbS2S5G4S1Z800000A1A2SbS2S5G3G2A2SbS2S5G2G5A2SbS2S5G1S1Z2fA1A2SfS2A1A3A3A3A3A3A3A4").
Lemma sdL_41_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS2A1A2M0A1S18S53S19A2S10G0S58A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_41_3)). Qed.
Definition setsL_41_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_41_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 41.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_41 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_41 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_41 (setp rhoB setsC_41))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_41 w setsC_41 (fst dC_41) (snd dC_41)); [reflexivity | reflexivity | exact sdC_41 | | | exact HSP].
    - cbn [fst dC_41]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_41) (snd dC_41) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_41 LC_41 (setp rhoB setsC_41) Q HkB (eq_trans runC_41 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 41 3) med_cnt_tab) with 24. change (class_size 41) with 43680. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_41 0 SC_41) with LC_41_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_41_0 SM1pre setsL_41_0 (fst dL_41_0) (snd dL_41_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_41_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_41_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_41_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 41 3) med_cnt_tab) with 24. change (class_size 41) with 43680. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_41 1 SC_41) with LC_41_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_41_1 SM1pre setsL_41_1 (fst dL_41_1) (snd dL_41_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_41_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_41_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_41_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 41 3) med_cnt_tab) with 24. change (class_size 41) with 43680. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_41 2 SC_41) with LC_41_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_41_2 SM1pre setsL_41_2 (fst dL_41_2) (snd dL_41_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_41_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_41_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_41_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 41 3) med_cnt_tab) with 24. change (class_size 41) with 43680. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_41 3 SC_41) with LC_41_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_41_3 SM1pre setsL_41_3 (fst dL_41_3) (snd dL_41_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_41_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_41_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_41_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c41.
