(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SN2pre"; "SCsym"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_11"; "SC_13"; "SC_15"; "SC_17"; "SC_20"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c11"; "LC_11_0"; "LC_11_1"; "LC_11_2"; "LC_11_3"; "LC_11_4"; "LC_11_5"; "dC_11"; "dL_11_0"; "dL_11_1"; "dL_11_2"; "dL_11_3"; "dL_11_4"; "dL_11_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c13"; "LC_13_0"; "LC_13_1"; "LC_13_2"; "LC_13_3"; "dC_13"; "dL_13_0"; "dL_13_1"; "dL_13_2"; "dL_13_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c15"; "LC_15_0"; "LC_15_1"; "LC_15_2"; "LC_15_3"; "LC_15_4"; "LC_15_5"; "dC_15"; "dL_15_0"; "dL_15_1"; "dL_15_2"; "dL_15_3"; "dL_15_4"; "dL_15_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c17"; "LC_17_0"; "LC_17_1"; "LC_17_2"; "LC_17_3"; "dC_17"; "dL_17_0"; "dL_17_1"; "dL_17_2"; "dL_17_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c20"; "LC_20_0"; "LC_20_1"; "LC_20_2"; "dC_20"; "dL_20_0"; "dL_20_1"; "dL_20_2"].
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

Module Mal_agrp_c11.

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

Definition dC_11 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_11 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_11 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1cS2fA2S10G0S3aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_11)). Qed.
Definition setsC_11 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_11)) in exact x).
Definition LC_11_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_11 0 SC_11) in exact x).
Definition dL_11_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|b|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZbA1S2PcA1M1A4SbG0ScS0S0S1Z100A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1e00A1S2PacA1M4A4SbG0ScS0S0S1Z1e10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a478A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1M8A3A4SbG0ScS0S0G8S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Zf0A1G2A4SbG0ScS0S0S1Zb0A1S4S13G7S1Z58A1A3A4M9SbG0ScS0S0S1Zb8A1S4S13G7S1Z60A1A3A4SbG0G9SbG0ScS0S0S1Z230A1S4S13G7S1Z1d8A1A3A4MaSbG0ScS0S0S1Z238A1S4S13G7S1Z1e0A1A3A4SbG0GaSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G5A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_11_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S34S1aA2S10G0S3bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_11_0)). Qed.
Definition setsL_11_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_11_0)) in exact x).
Definition LC_11_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_11 1 SC_11) in exact x).
Definition dL_11_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZbA1S2PcA1M1A4SbG0ScS0S0S1Z100A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zf00A1S2PacA1M4A4SbG0ScS0S0S1Zf10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a478A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1M7A3A4SbG0ScS0S0G7S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zf0A1G2A4SbG0ScS0S0S1Zb0A1S4S13G6S1Z58A1A3A4M8SbG0ScS0S0S1Zb8A1S4S13G6S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z230A1S4S13G6S1Z1d8A1A3A4M9SbG0ScS0S0S1Z238A1S4S13G6S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_11_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S35S1aA2S10G0S3cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_11_1)). Qed.
Definition setsL_11_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_11_1)) in exact x).
Definition LC_11_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_11 2 SC_11) in exact x).
Definition dL_11_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_11_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_11_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S36S1bA2S10G0S3dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_11_2)). Qed.
Definition setsL_11_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_11_2)) in exact x).
Definition LC_11_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_11 3 SC_11) in exact x).
Definition dL_11_3 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_11_3 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_11_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S37S1bA2S10G0S3eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_11_3)). Qed.
Definition setsL_11_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_11_3)) in exact x).
Definition LC_11_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_11 4 SC_11) in exact x).
Definition dL_11_4 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_11_4 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_11_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S38S1bA2S10G0S3fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_11_4)). Qed.
Definition setsL_11_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_11_4)) in exact x).
Definition LC_11_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_11 5 SC_11) in exact x).
Definition dL_11_5 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_11_5 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_11_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S39S1bA2S10G0S40A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_11_5)). Qed.
Definition setsL_11_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_11_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 11.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_11 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_11 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_11 (setp rhoB setsC_11))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_11 w setsC_11 (fst dC_11) (snd dC_11)); [reflexivity | reflexivity | exact sdC_11 | | | exact HSP].
    - cbn [fst dC_11]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_11) (snd dC_11) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_11 LC_11 (setp rhoB setsC_11) Q HkB (eq_trans runC_11 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 11 3) med_cnt_tab) with 32. change (class_size 11) with 240. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_11 0 SC_11) with LC_11_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_11_0 SM1pre setsL_11_0 (fst dL_11_0) (snd dL_11_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_11_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_11_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_11_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 11 3) med_cnt_tab) with 32. change (class_size 11) with 240. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_11 1 SC_11) with LC_11_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_11_1 SM1pre setsL_11_1 (fst dL_11_1) (snd dL_11_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_11_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_11_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_11_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 11 3) med_cnt_tab) with 32. change (class_size 11) with 240. icnt_decide. }
    assert (Htot : itotal ia = 1932) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_11 2 SC_11) with LC_11_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_11_2 SN2pre setsL_11_2 (fst dL_11_2) (snd dL_11_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_11_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_11_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_11_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 1932 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 11 3) med_cnt_tab) with 32. change (class_size 11) with 240. icnt_decide. }
    assert (Htot : itotal ia = 972) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_11 3 SC_11) with LC_11_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_11_3 SN2pre setsL_11_3 (fst dL_11_3) (snd dL_11_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_11_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_11_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_11_3) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 972 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 11 3) med_cnt_tab) with 32. change (class_size 11) with 240. icnt_decide. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_11 4 SC_11) with LC_11_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_11_4 SN2pre setsL_11_4 (fst dL_11_4) (snd dL_11_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_11_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_11_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_11_4) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 11 3) med_cnt_tab) with 32. change (class_size 11) with 240. icnt_decide. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_11 5 SC_11) with LC_11_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_11_5 SN2pre setsL_11_5 (fst dL_11_5) (snd dL_11_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_11_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_11_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_11_5) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c11.

Module Mal_agrp_c13.

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

Definition dC_13 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_13 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_13 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1cS30A2S10G0S45A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_13)). Qed.
Definition setsC_13 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_13)) in exact x).
Definition LC_13_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_13 0 SC_13) in exact x).
Definition dL_13_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZdA1S2PcA1M1A4SbG0ScS0S0S1Z150A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1e00A1S2PacA1M4A4SbG0ScS0S0S1Z1e10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a488A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a430A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z140A1G2A4SbG0ScS0S0S1Zc0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zc8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z240A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z248A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_13_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S41S1aA2S10G0S46A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_13_0)). Qed.
Definition setsL_13_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_13_0)) in exact x).
Definition LC_13_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_13 1 SC_13) in exact x).
Definition dL_13_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZdA1S2PcA1M1A4SbG0ScS0S0S1Z150A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zf00A1S2PacA1M4A4SbG0ScS0S0S1Zf10A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a488A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a430A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z140A1G2A4SbG0ScS0S0S1Zc0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zc8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z240A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z248A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_13_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S42S1aA2S10G0S47A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_13_1)). Qed.
Definition setsL_13_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_13_1)) in exact x).
Definition LC_13_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_13 2 SC_13) in exact x).
Definition dL_13_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_13_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_13_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S43S1bA2S10G0S48A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_13_2)). Qed.
Definition setsL_13_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_13_2)) in exact x).
Definition LC_13_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_13 3 SC_13) in exact x).
Definition dL_13_3 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_13_3 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_13_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S44S1bA2S10G0S49A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_13_3)). Qed.
Definition setsL_13_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_13_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 13.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_13 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_13 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_13 (setp rhoB setsC_13))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_13 w setsC_13 (fst dC_13) (snd dC_13)); [reflexivity | reflexivity | exact sdC_13 | | | exact HSP].
    - cbn [fst dC_13]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_13) (snd dC_13) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_13 LC_13 (setp rhoB setsC_13) Q HkB (eq_trans runC_13 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 13 3) med_cnt_tab) with 24. change (class_size 13) with 320. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_13 0 SC_13) with LC_13_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_13_0 SM1pre setsL_13_0 (fst dL_13_0) (snd dL_13_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_13_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_13_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_13_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 13 3) med_cnt_tab) with 24. change (class_size 13) with 320. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_13 1 SC_13) with LC_13_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_13_1 SM1pre setsL_13_1 (fst dL_13_1) (snd dL_13_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_13_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_13_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_13_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 13 3) med_cnt_tab) with 24. change (class_size 13) with 320. icnt_decide. }
    assert (Htot : itotal ia = 1932) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_13 2 SC_13) with LC_13_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_13_2 SN2pre setsL_13_2 (fst dL_13_2) (snd dL_13_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_13_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_13_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_13_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 1932 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 13 3) med_cnt_tab) with 24. change (class_size 13) with 320. icnt_decide. }
    assert (Htot : itotal ia = 972) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_13 3 SC_13) with LC_13_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_13_3 SN2pre setsL_13_3 (fst dL_13_3) (snd dL_13_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_13_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_13_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_13_3) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 972 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c13.

Module Mal_agrp_c17.

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

Definition dC_17 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_17 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_17 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1cS32A2S10G0S5bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_17)). Qed.
Definition setsC_17 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_17)) in exact x).
Definition LC_17_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_17 0 SC_17) in exact x).
Definition dL_17_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z11A1S2PcA1M1A4SbG0ScS0S0S1Z2b0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3f00A1S2PacA1M4A4SbG0ScS0S0S1Z3f10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a4a8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a450A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2a0A1G2A4SbG0ScS0S0S1Ze0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Ze8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z260A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z268A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_17_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S57S1aA2S10G0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_17_0)). Qed.
Definition setsL_17_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_17_0)) in exact x).
Definition LC_17_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_17 1 SC_17) in exact x).
Definition dL_17_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z11A1S2PcA1M1A4SbG0ScS0S0S1Z2b0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1f80A1S2PacA1M4A4SbG0ScS0S0S1Z1f90A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a4a8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a450A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2a0A1G2A4SbG0ScS0S0S1Ze0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Ze8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z260A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z268A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_17_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S58S1aA2S10G0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_17_1)). Qed.
Definition setsL_17_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_17_1)) in exact x).
Definition LC_17_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_17 2 SC_17) in exact x).
Definition dL_17_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z11A1S2PcA1M1A4SbG0ScS0S0S1Z2b0A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfc0A1S2PacA1M4A4SbG0ScS0S0S1Zfd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a4a8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a450A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z2a0A1G2A4SbG0ScS0S0S1Ze0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Ze8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z260A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z268A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_17_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S59S1aA2S10G0S5eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_17_2)). Qed.
Definition setsL_17_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_17_2)) in exact x).
Definition LC_17_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_17 3 SC_17) in exact x).
Definition dL_17_3 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_17_3 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_17_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S5aS1bA2S10G0S5fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_17_3)). Qed.
Definition setsL_17_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_17_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 17.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_17 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_17 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_17 (setp rhoB setsC_17))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_17 w setsC_17 (fst dC_17) (snd dC_17)); [reflexivity | reflexivity | exact sdC_17 | | | exact HSP].
    - cbn [fst dC_17]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_17) (snd dC_17) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_17 LC_17 (setp rhoB setsC_17) Q HkB (eq_trans runC_17 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 17 3) med_cnt_tab) with 24. change (class_size 17) with 672. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_17 0 SC_17) with LC_17_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_17_0 SM1pre setsL_17_0 (fst dL_17_0) (snd dL_17_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_17_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_17_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_17_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 17 3) med_cnt_tab) with 24. change (class_size 17) with 672. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_17 1 SC_17) with LC_17_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_17_1 SM1pre setsL_17_1 (fst dL_17_1) (snd dL_17_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_17_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_17_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_17_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 17 3) med_cnt_tab) with 24. change (class_size 17) with 672. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_17 2 SC_17) with LC_17_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_17_2 SM1pre setsL_17_2 (fst dL_17_2) (snd dL_17_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_17_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_17_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_17_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 17 3) med_cnt_tab) with 24. change (class_size 17) with 672. icnt_decide. }
    assert (Htot : itotal ia = 2028) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_17 3 SC_17) with LC_17_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_17_3 SN2pre setsL_17_3 (fst dL_17_3) (snd dL_17_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_17_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_17_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_17_3) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 2028 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c17.

Module Mal_agrp_c15.

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

Definition dC_15 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_15 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_15 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1cS31A2S10G0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_15)). Qed.
Definition setsC_15 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_15)) in exact x).
Definition LC_15_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_15 0 SC_15) in exact x).
Definition dL_15_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZfA1S2PcA1M1A4SbG0ScS0S0S1Z200A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3e00A1S2PacA1M4A4SbG0ScS0S0S1Z3e10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a498A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a440A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1f0A1G2A4SbG0ScS0S0S1Zd0A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Zd8A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z250A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z258A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G5A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_15_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4aS1aA2S10G0S51A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_15_0)). Qed.
Definition setsL_15_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_15_0)) in exact x).
Definition LC_15_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_15 1 SC_15) in exact x).
Definition dL_15_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZfA1S2PcA1M1A4SbG0ScS0S0S1Z200A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1f00A1S2PacA1M4A4SbG0ScS0S0S1Z1f10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a498A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a440A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1f0A1G2A4SbG0ScS0S0S1Zd0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zd8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z250A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z258A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_15_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4bS1aA2S10G0S52A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_15_1)). Qed.
Definition setsL_15_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_15_1)) in exact x).
Definition LC_15_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_15 2 SC_15) in exact x).
Definition dL_15_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1ZfA1S2PcA1M1A4SbG0ScS0S0S1Z200A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zf80A1S2PacA1M4A4SbG0ScS0S0S1Zf90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S2PafA1M5A4SbG0ScS0S0S1Z5a498A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a440A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z1f0A1G2A4SbG0ScS0S0S1Zd0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zd8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z250A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z258A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_15_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4cS1aA2S10G0S53A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_15_2)). Qed.
Definition setsL_15_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_15_2)) in exact x).
Definition LC_15_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_15 3 SC_15) in exact x).
Definition dL_15_3 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_15_3 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_15_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4dS1bA2S10G0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_15_3)). Qed.
Definition setsL_15_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_15_3)) in exact x).
Definition LC_15_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_15 4 SC_15) in exact x).
Definition dL_15_4 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_15_4 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_15_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4eS1bA2S10G0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_15_4)). Qed.
Definition setsL_15_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_15_4)) in exact x).
Definition LC_15_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_15 5 SC_15) in exact x).
Definition dL_15_5 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_15_5 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_15_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4fS1bA2S10G0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_15_5)). Qed.
Definition setsL_15_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_15_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 15.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_15 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_15 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_15 (setp rhoB setsC_15))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_15 w setsC_15 (fst dC_15) (snd dC_15)); [reflexivity | reflexivity | exact sdC_15 | | | exact HSP].
    - cbn [fst dC_15]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_15) (snd dC_15) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_15 LC_15 (setp rhoB setsC_15) Q HkB (eq_trans runC_15 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 15 3) med_cnt_tab) with 32. change (class_size 15) with 496. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_15 0 SC_15) with LC_15_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_15_0 SM1pre setsL_15_0 (fst dL_15_0) (snd dL_15_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_15_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_15_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_15_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 15 3) med_cnt_tab) with 32. change (class_size 15) with 496. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_15 1 SC_15) with LC_15_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_15_1 SM1pre setsL_15_1 (fst dL_15_1) (snd dL_15_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_15_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_15_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_15_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 15 3) med_cnt_tab) with 32. change (class_size 15) with 496. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_15 2 SC_15) with LC_15_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_15_2 SM1pre setsL_15_2 (fst dL_15_2) (snd dL_15_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_15_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_15_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_15_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 15 3) med_cnt_tab) with 32. change (class_size 15) with 496. icnt_decide. }
    assert (Htot : itotal ia = 1996) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_15 3 SC_15) with LC_15_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_15_3 SN2pre setsL_15_3 (fst dL_15_3) (snd dL_15_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_15_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_15_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_15_3) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 1996 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 15 3) med_cnt_tab) with 32. change (class_size 15) with 496. icnt_decide. }
    assert (Htot : itotal ia = 1004) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_15 4 SC_15) with LC_15_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_15_4 SN2pre setsL_15_4 (fst dL_15_4) (snd dL_15_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_15_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_15_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_15_4) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 1004 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 15 3) med_cnt_tab) with 32. change (class_size 15) with 496. icnt_decide. }
    assert (Htot : itotal ia = 1004) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_15 5 SC_15) with LC_15_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_15_5 SN2pre setsL_15_5 (fst dL_15_5) (snd dL_15_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_15_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_15_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_15_5) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 1004 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c15.

Module Mal_agrp_c20.

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

Definition dC_20 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_20 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_20 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1cS33A2S10G0S63A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_20)). Qed.
Definition setsC_20 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_20)) in exact x).
Definition LC_20_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_20 0 SC_20) in exact x).
Definition dL_20_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z14A1S2PcA1M1A4SbG0ScS0S0S1Z490A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7e00A1S2PacA1M4A4SbG0ScS0S0S1Z7e10A1S4S13G4G3A3A4SbG0ScS0S0S1Z1cA1S2PafA1M5A4SbG0ScS0S0S1Z5a4c0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a468A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z480A1G2A4SbG0ScS0S0S1Zf8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z100A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z278A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z280A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_20_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S60S1aA2S10G0S64A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_20_0)). Qed.
Definition setsL_20_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_20_0)) in exact x).
Definition LC_20_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_20 1 SC_20) in exact x).
Definition dL_20_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z14A1S2PcA1M1A4SbG0ScS0S0S1Z490A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3f00A1S2PacA1M4A4SbG0ScS0S0S1Z3f10A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S2PafA1M5A4SbG0ScS0S0S1Z5a4c0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a468A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z480A1G2A4SbG0ScS0S0S1Zf8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z100A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z278A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z280A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_20_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S61S1aA2S10G0S65A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_20_1)). Qed.
Definition setsL_20_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_20_1)) in exact x).
Definition LC_20_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_20 2 SC_20) in exact x).
Definition dL_20_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z14A1S2PcA1M1A4SbG0ScS0S0S1Z490A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1f80A1S2PacA1M4A4SbG0ScS0S0S1Z1f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z7A1S2PafA1M5A4SbG0ScS0S0S1Z5a4c0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a468A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z480A1G2A4SbG0ScS0S0S1Zf8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z100A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z278A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z280A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_20_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S62S1aA2S10G0S66A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_20_2)). Qed.
Definition setsL_20_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_20_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 20.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_20 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_20 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_20 (setp rhoB setsC_20))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_20 w setsC_20 (fst dC_20) (snd dC_20)); [reflexivity | reflexivity | exact sdC_20 | | | exact HSP].
    - cbn [fst dC_20]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_20) (snd dC_20) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_20 LC_20 (setp rhoB setsC_20) Q HkB (eq_trans runC_20 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 28).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 20 3) med_cnt_tab) with 28. change (class_size 20) with 1152. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_20 0 SC_20) with LC_20_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_20_0 SM1pre setsL_20_0 (fst dL_20_0) (snd dL_20_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_20_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_20_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_20_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 20 3) med_cnt_tab) with 28. change (class_size 20) with 1152. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_20 1 SC_20) with LC_20_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_20_1 SM1pre setsL_20_1 (fst dL_20_1) (snd dL_20_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_20_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_20_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_20_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 20 3) med_cnt_tab) with 28. change (class_size 20) with 1152. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_20 2 SC_20) with LC_20_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_20_2 SM1pre setsL_20_2 (fst dL_20_2) (snd dL_20_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_20_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_20_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_20_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c20.
