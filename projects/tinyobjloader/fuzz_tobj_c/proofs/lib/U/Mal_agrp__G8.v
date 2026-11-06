(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SCsym"; "SN2pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_23"; "SC_25"; "SC_26"; "SC_28"; "SC_30"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c23"; "LC_23_0"; "LC_23_1"; "LC_23_2"; "LC_23_3"; "LC_23_4"; "LC_23_5"; "dC_23"; "dL_23_0"; "dL_23_1"; "dL_23_2"; "dL_23_3"; "dL_23_4"; "dL_23_5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c25"; "LC_25_0"; "LC_25_1"; "LC_25_2"; "LC_25_3"; "dC_25"; "dL_25_0"; "dL_25_1"; "dL_25_2"; "dL_25_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c26"; "LC_26_0"; "LC_26_1"; "LC_26_2"; "dC_26"; "dL_26_0"; "dL_26_1"; "dL_26_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c28"; "LC_28_0"; "LC_28_1"; "LC_28_2"; "dC_28"; "dL_28_0"; "dL_28_1"; "dL_28_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c30"; "LC_30_0"; "LC_30_1"; "LC_30_2"; "dC_30"; "dL_30_0"; "dL_30_1"; "dL_30_2"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_c23.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_23 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_23 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_23 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS2fA2S10G0S3aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_23)). Qed.
Definition setsC_23 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_23)) in exact x).
Definition LC_23_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_23 0 SC_23) in exact x).
Definition dL_23_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z17A1S2PcA1M1A4SbG0ScS0S0S1Z800A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfe00A1S2PacA1M4A4SbG0ScS0S0S1Zfe10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a4d8A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a480A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7f0A1G2A4SbG0ScS0S0S1Z110A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z118A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z290A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z298A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G5A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_23_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S34S19A2S10G0S3bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_23_0)). Qed.
Definition setsL_23_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_23_0)) in exact x).
Definition LC_23_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_23 1 SC_23) in exact x).
Definition dL_23_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z17A1S2PcA1M1A4SbG0ScS0S0S1Z800A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7f00A1S2PacA1M4A4SbG0ScS0S0S1Z7f10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a4d8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a480A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7f0A1G2A4SbG0ScS0S0S1Z110A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z118A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z290A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z298A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_23_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S35S19A2S10G0S3cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_23_1)). Qed.
Definition setsL_23_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_23_1)) in exact x).
Definition LC_23_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_23 2 SC_23) in exact x).
Definition dL_23_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z17A1S2PcA1M1A4SbG0ScS0S0S1Z800A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3f80A1S2PacA1M4A4SbG0ScS0S0S1Z3f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S2PafA1M5A4SbG0ScS0S0S1Z5a4d8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a480A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7f0A1G2A4SbG0ScS0S0S1Z110A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z118A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z290A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z298A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_23_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S36S19A2S10G0S3dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_23_2)). Qed.
Definition setsL_23_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_23_2)) in exact x).
Definition LC_23_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_23 3 SC_23) in exact x).
Definition dL_23_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z17A1S2PcA1M1A4SbG0ScS0S0S1Z800A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1fc0A1S2PacA1M4A4SbG0ScS0S0S1Z1fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S2PafA1M5A4SbG0ScS0S0S1Z5a4d8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a480A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7f0A1G2A4SbG0ScS0S0S1Z110A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z118A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z290A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z298A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_23_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S37S19A2S10G0S3eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_23_3)). Qed.
Definition setsL_23_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_23_3)) in exact x).
Definition LC_23_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_23 4 SC_23) in exact x).
Definition dL_23_4 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z17A1S2PcA1M1A4SbG0ScS0S0S1Z800A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfe0A1S2PacA1M4A4SbG0ScS0S0S1Zff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S2PafA1M5A4SbG0ScS0S0S1Z5a4d8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a480A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7f0A1G2A4SbG0ScS0S0S1Z110A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z118A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z290A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z298A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_23_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S38S19A2S10G0S3fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_23_4)). Qed.
Definition setsL_23_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_23_4)) in exact x).
Definition LC_23_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_23 5 SC_23) in exact x).
Definition dL_23_5 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z17A1S2PcA1M1A4SbG0ScS0S0S1Z800A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfe0A1S2PacA1M4A4SbG0ScS0S0S1Zff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S2PafA1M5A4SbG0ScS0S0S1Z5a4d8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a480A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z7f0A1G2A4SbG0ScS0S0S1Z110A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z118A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z290A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z298A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_23_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S39S19A2S10G0S40A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_23_5)). Qed.
Definition setsL_23_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_23_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 23.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_23 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_23 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_23 (setp rhoB setsC_23))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_23 w setsC_23 (fst dC_23) (snd dC_23)); [reflexivity | reflexivity | exact sdC_23 | | | exact HSP].
    - cbn [fst dC_23]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_23) (snd dC_23) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_23 LC_23 (setp rhoB setsC_23) Q HkB (eq_trans runC_23 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 23 3) med_cnt_tab) with 32. change (class_size 23) with 2032. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_23 0 SC_23) with LC_23_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_23_0 SM1pre setsL_23_0 (fst dL_23_0) (snd dL_23_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_23_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_23_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_23_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 23 3) med_cnt_tab) with 32. change (class_size 23) with 2032. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_23 1 SC_23) with LC_23_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_23_1 SM1pre setsL_23_1 (fst dL_23_1) (snd dL_23_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_23_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_23_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_23_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 23 3) med_cnt_tab) with 32. change (class_size 23) with 2032. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_23 2 SC_23) with LC_23_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_23_2 SM1pre setsL_23_2 (fst dL_23_2) (snd dL_23_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_23_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_23_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_23_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 23 3) med_cnt_tab) with 32. change (class_size 23) with 2032. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_23 3 SC_23) with LC_23_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_23_3 SM1pre setsL_23_3 (fst dL_23_3) (snd dL_23_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_23_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_23_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_23_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 23 3) med_cnt_tab) with 32. change (class_size 23) with 2032. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_23 4 SC_23) with LC_23_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_23_4 SM1pre setsL_23_4 (fst dL_23_4) (snd dL_23_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_23_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_23_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_23_4) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 23 3) med_cnt_tab) with 32. change (class_size 23) with 2032. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_23 5 SC_23) with LC_23_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_23_5 SM1pre setsL_23_5 (fst dL_23_5) (snd dL_23_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_23_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_23_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_23_5) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c23.

Module Mal_agrp_c26.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_26 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_26 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_26 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS31A2S10G0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_26)). Qed.
Definition setsC_26 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_26)) in exact x).
Definition LC_26_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_26 0 SC_26) in exact x).
Definition dL_26_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1aA1S2PcA1M1A4SbG0ScS0S0S1Zcd0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff00A1S2PacA1M4A4SbG0ScS0S0S1Zff10A1S4S13G4G3A3A4SbG0ScS0S0S1Z14A1S2PafA1M5A4SbG0ScS0S0S1Z5a4f0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a498A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zcc0A1G2A4SbG0ScS0S0S1Z128A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z130A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2a8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_26_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4aS19A2S10G0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_26_0)). Qed.
Definition setsL_26_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_26_0)) in exact x).
Definition LC_26_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_26 1 SC_26) in exact x).
Definition dL_26_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1aA1S2PcA1M1A4SbG0ScS0S0S1Zcd0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7f80A1S2PacA1M4A4SbG0ScS0S0S1Z7f90A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a4f0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a498A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zcc0A1G2A4SbG0ScS0S0S1Z128A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z130A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2a8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_26_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4bS19A2S10G0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_26_1)). Qed.
Definition setsL_26_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_26_1)) in exact x).
Definition LC_26_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_26 2 SC_26) in exact x).
Definition dL_26_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1aA1S2PcA1M1A4SbG0ScS0S0S1Zcd0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fc0A1S2PacA1M4A4SbG0ScS0S0S1Z3fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S2PafA1M5A4SbG0ScS0S0S1Z5a4f0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a498A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zcc0A1G2A4SbG0ScS0S0S1Z128A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z130A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2a8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2b0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_26_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4cS19A2S10G0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_26_2)). Qed.
Definition setsL_26_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_26_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 26.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_26 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_26 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_26 (setp rhoB setsC_26))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_26 w setsC_26 (fst dC_26) (snd dC_26)); [reflexivity | reflexivity | exact sdC_26 | | | exact HSP].
    - cbn [fst dC_26]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_26) (snd dC_26) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_26 LC_26 (setp rhoB setsC_26) Q HkB (eq_trans runC_26 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 26 3) med_cnt_tab) with 20. change (class_size 26) with 3264. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_26 0 SC_26) with LC_26_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_26_0 SM1pre setsL_26_0 (fst dL_26_0) (snd dL_26_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_26_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_26_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_26_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 26 3) med_cnt_tab) with 20. change (class_size 26) with 3264. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_26 1 SC_26) with LC_26_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_26_1 SM1pre setsL_26_1 (fst dL_26_1) (snd dL_26_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_26_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_26_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_26_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 26 3) med_cnt_tab) with 20. change (class_size 26) with 3264. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_26 2 SC_26) with LC_26_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_26_2 SM1pre setsL_26_2 (fst dL_26_2) (snd dL_26_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_26_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_26_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_26_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c26.

Module Mal_agrp_c25.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_25 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_25 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_25 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS30A2S10G0S45A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_25)). Qed.
Definition setsC_25 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_25)) in exact x).
Definition LC_25_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_25 0 SC_25) in exact x).
Definition dL_25_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z19A1S2PcA1M1A4SbG0ScS0S0S1Zab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff00A1S2PacA1M4A4SbG0ScS0S0S1Zff10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a4e8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a490A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaa0A1G2A4SbG0ScS0S0S1Z120A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z128A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2a0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2a8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_25_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S41S19A2S10G0S46A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_25_0)). Qed.
Definition setsL_25_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_25_0)) in exact x).
Definition LC_25_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_25 1 SC_25) in exact x).
Definition dL_25_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z19A1S2PcA1M1A4SbG0ScS0S0S1Zab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7f80A1S2PacA1M4A4SbG0ScS0S0S1Z7f90A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a4e8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a490A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaa0A1G2A4SbG0ScS0S0S1Z120A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z128A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2a0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2a8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_25_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S42S19A2S10G0S47A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_25_1)). Qed.
Definition setsL_25_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_25_1)) in exact x).
Definition LC_25_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_25 2 SC_25) in exact x).
Definition dL_25_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z19A1S2PcA1M1A4SbG0ScS0S0S1Zab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fc0A1S2PacA1M4A4SbG0ScS0S0S1Z3fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a4e8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a490A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaa0A1G2A4SbG0ScS0S0S1Z120A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z128A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2a0A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2a8A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_25_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S43S19A2S10G0S48A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_25_2)). Qed.
Definition setsL_25_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_25_2)) in exact x).
Definition LC_25_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_25 3 SC_25) in exact x).
Definition dL_25_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z19A1S2PcA1M1A4SbG0ScS0S0S1Zab0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1fe0A1S2PacA1M4A4SbG0ScS0S0S1Z1ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a4e8A1S4S13S4S14G1G5A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a490A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Zaa0A1G2A4SbG0ScS0S0S1Z120A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z128A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2a0A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2a8A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_25_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S44S19A2S10G0S49A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_25_3)). Qed.
Definition setsL_25_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_25_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 25.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_25 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_25 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_25 (setp rhoB setsC_25))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_25 w setsC_25 (fst dC_25) (snd dC_25)); [reflexivity | reflexivity | exact sdC_25 | | | exact HSP].
    - cbn [fst dC_25]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_25) (snd dC_25) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_25 LC_25 (setp rhoB setsC_25) Q HkB (eq_trans runC_25 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 25 3) med_cnt_tab) with 24. change (class_size 25) with 2720. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_25 0 SC_25) with LC_25_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_25_0 SM1pre setsL_25_0 (fst dL_25_0) (snd dL_25_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_25_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_25_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_25_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 25 3) med_cnt_tab) with 24. change (class_size 25) with 2720. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_25 1 SC_25) with LC_25_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_25_1 SM1pre setsL_25_1 (fst dL_25_1) (snd dL_25_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_25_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_25_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_25_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 25 3) med_cnt_tab) with 24. change (class_size 25) with 2720. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_25 2 SC_25) with LC_25_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_25_2 SM1pre setsL_25_2 (fst dL_25_2) (snd dL_25_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_25_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_25_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_25_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 25 3) med_cnt_tab) with 24. change (class_size 25) with 2720. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_25 3 SC_25) with LC_25_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_25_3 SM1pre setsL_25_3 (fst dL_25_3) (snd dL_25_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_25_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_25_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_25_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c25.

Module Mal_agrp_c28.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_28 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_28 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_28 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS32A2S10G0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_28)). Qed.
Definition setsC_28 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_28)) in exact x).
Definition LC_28_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_28 0 SC_28) in exact x).
Definition dL_28_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1cA1M1S2PcA1M2A4SbG0ScS0S0S1Z1250A1S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Z1ff00A1S2PacA1M5A4SbG0ScS0S0S1Z1ff10A1S4S13G5G4A3A4SbG0ScS0S0G1S2PafA1M6A4SbG0ScS0S0S1Z5a500A1S4S13S4S14G2S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a8A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1240A1G3A4SbG0ScS0S0S1Z138A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z140A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z2b8A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z2c0A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G5S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G2S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_28_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S51S19A2S10G0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_28_0)). Qed.
Definition setsL_28_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_28_0)) in exact x).
Definition LC_28_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_28 1 SC_28) in exact x).
Definition dL_28_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1cA1S2PcA1M1A4SbG0ScS0S0S1Z1250A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff80A1S2PacA1M4A4SbG0ScS0S0S1Zff90A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S2PafA1M5A4SbG0ScS0S0S1Z5a500A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1240A1G2A4SbG0ScS0S0S1Z138A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z140A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2b8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2c0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_28_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S52S19A2S10G0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_28_1)). Qed.
Definition setsL_28_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_28_1)) in exact x).
Definition LC_28_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_28 2 SC_28) in exact x).
Definition dL_28_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1cA1S2PcA1M1A4SbG0ScS0S0S1Z1250A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fc0A1S2PacA1M4A4SbG0ScS0S0S1Z7fd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z7A1S2PafA1M5A4SbG0ScS0S0S1Z5a500A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4a8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1240A1G2A4SbG0ScS0S0S1Z138A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z140A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2b8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2c0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_28_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S53S19A2S10G0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_28_2)). Qed.
Definition setsL_28_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_28_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 28.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_28 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_28 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_28 (setp rhoB setsC_28))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_28 w setsC_28 (fst dC_28) (snd dC_28)); [reflexivity | reflexivity | exact sdC_28 | | | exact HSP].
    - cbn [fst dC_28]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_28) (snd dC_28) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_28 LC_28 (setp rhoB setsC_28) Q HkB (eq_trans runC_28 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 28).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 28 3) med_cnt_tab) with 28. change (class_size 28) with 4672. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_28 0 SC_28) with LC_28_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_28_0 SM1pre setsL_28_0 (fst dL_28_0) (snd dL_28_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_28_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_28_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_28_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 28 3) med_cnt_tab) with 28. change (class_size 28) with 4672. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_28 1 SC_28) with LC_28_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_28_1 SM1pre setsL_28_1 (fst dL_28_1) (snd dL_28_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_28_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_28_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_28_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 28 3) med_cnt_tab) with 28. change (class_size 28) with 4672. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_28 2 SC_28) with LC_28_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_28_2 SM1pre setsL_28_2 (fst dL_28_2) (snd dL_28_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_28_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_28_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_28_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c28.

Module Mal_agrp_c30.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_30 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_30 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_30 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS33A2S10G0S5bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_30)). Qed.
Definition setsC_30 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_30)) in exact x).
Definition LC_30_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_30 0 SC_30) in exact x).
Definition dL_30_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1eA1S2PcA1M1A4SbG0ScS0S0S1Z19a0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ff40A1S2PacA1M4A4SbG0ScS0S0S1Z1ff50A1S4S13G4G3A3A4SbG0ScS0S0S1Z14A1S2PafA1M5A4SbG0ScS0S0S1Z5a510A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1990A1G2A4SbG0ScS0S0S1Z148A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z150A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2c8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_30_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S58S19A2S10G0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_30_0)). Qed.
Definition setsL_30_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_30_0)) in exact x).
Definition LC_30_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_30 1 SC_30) in exact x).
Definition dL_30_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1eA1S2PcA1M1A4SbG0ScS0S0S1Z19a0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zffa0A1S2PacA1M4A4SbG0ScS0S0S1Zffb0A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a510A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1990A1G2A4SbG0ScS0S0S1Z148A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z150A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2c8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_30_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S59S19A2S10G0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_30_1)). Qed.
Definition setsL_30_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_30_1)) in exact x).
Definition LC_30_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_30 2 SC_30) in exact x).
Definition dL_30_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z1eA1S2PcA1M1A4SbG0ScS0S0S1Z19a0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fd0A1S2PacA1M4A4SbG0ScS0S0S1Z7fe0A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S2PafA1M5A4SbG0ScS0S0S1Z5a510A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a4b8A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1990A1G2A4SbG0ScS0S0S1Z148A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z150A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z2c8A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2d0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_30_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S5aS19A2S10G0S5eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_30_2)). Qed.
Definition setsL_30_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_30_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 30.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_30 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_30 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_30 (setp rhoB setsC_30))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_30 w setsC_30 (fst dC_30) (snd dC_30)); [reflexivity | reflexivity | exact sdC_30 | | | exact HSP].
    - cbn [fst dC_30]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_30) (snd dC_30) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_30 LC_30 (setp rhoB setsC_30) Q HkB (eq_trans runC_30 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 30 3) med_cnt_tab) with 20. change (class_size 30) with 6544. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_30 0 SC_30) with LC_30_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_30_0 SM1pre setsL_30_0 (fst dL_30_0) (snd dL_30_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_30_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_30_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_30_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 30 3) med_cnt_tab) with 20. change (class_size 30) with 6544. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_30 1 SC_30) with LC_30_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_30_1 SM1pre setsL_30_1 (fst dL_30_1) (snd dL_30_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_30_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_30_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_30_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 30 3) med_cnt_tab) with 20. change (class_size 30) with 6544. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_30 2 SC_30) with LC_30_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_30_2 SM1pre setsL_30_2 (fst dL_30_2) (snd dL_30_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_30_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_30_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_30_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c30.
