(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SCsym"; "SN2pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_19"; "SC_2"; "SC_21"; "SC_22"; "SC_24"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c19"; "LC_19_0"; "LC_19_1"; "LC_19_2"; "LC_19_3"; "LC_19_4"; "LC_19_5"; "dC_19"; "dL_19_0"; "dL_19_1"; "dL_19_2"; "dL_19_3"; "dL_19_4"; "dL_19_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c2"; "LC_2_0"; "LC_2_1"; "LC_2_2"; "dC_2"; "dL_2_0"; "dL_2_1"; "dL_2_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c21"; "LC_21_0"; "LC_21_1"; "LC_21_2"; "LC_21_3"; "dC_21"; "dL_21_0"; "dL_21_1"; "dL_21_2"; "dL_21_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c22"; "LC_22_0"; "LC_22_1"; "LC_22_2"; "dC_22"; "dL_22_0"; "dL_22_1"; "dL_22_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c24"; "LC_24_0"; "LC_24_1"; "LC_24_2"; "dC_24"; "dL_24_0"; "dL_24_1"; "dL_24_2"].
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

Module Mal_agrp_c22.

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

Definition dC_22 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_22 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_22 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1bS32A2S10G0S54A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_22)). Qed.
Definition setsC_22 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_22)) in exact x).
Definition LC_22_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_22 0 SC_22) in exact x).
Definition dL_22_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z16A1S2PcA1M1A4SbG0ScS0S0S1Z670A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7f80A1S2PacA1M4A4SbG0ScS0S0S1Z7f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z14A1S2PafA1M5A4SbG0ScS0S0S1Z5a4d0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a478A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z660A1G2A4SbG0ScS0S0S1Z108A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z110A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z288A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z290A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_22_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S51S1aA2S10G0S55A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_22_0)). Qed.
Definition setsL_22_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_22_0)) in exact x).
Definition LC_22_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_22 1 SC_22) in exact x).
Definition dL_22_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z16A1S2PcA1M1A4SbG0ScS0S0S1Z670A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fc0A1S2PacA1M4A4SbG0ScS0S0S1Z3fd0A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a4d0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a478A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z660A1G2A4SbG0ScS0S0S1Z108A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z110A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z288A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z290A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_22_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S52S1aA2S10G0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_22_1)). Qed.
Definition setsL_22_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_22_1)) in exact x).
Definition LC_22_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_22 2 SC_22) in exact x).
Definition dL_22_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z16A1S2PcA1M1A4SbG0ScS0S0S1Z670A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1fe0A1S2PacA1M4A4SbG0ScS0S0S1Z1ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S2PafA1M5A4SbG0ScS0S0S1Z5a4d0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a478A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z660A1G2A4SbG0ScS0S0S1Z108A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z110A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z288A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z290A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_22_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S53S1aA2S10G0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_22_2)). Qed.
Definition setsL_22_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_22_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 22.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3F_;F_;F_;").

Theorem cls_22 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_22 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_22 (setp rhoB setsC_22))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_22 w setsC_22 (fst dC_22) (snd dC_22)); [reflexivity | reflexivity | exact sdC_22 | | | exact HSP].
    - cbn [fst dC_22]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_22) (snd dC_22) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_22 LC_22 (setp rhoB setsC_22) Q HkB (eq_trans runC_22 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 22 3) med_cnt_tab) with 20. change (class_size 22) with 1632. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_22 0 SC_22) with LC_22_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_22_0 SM1pre setsL_22_0 (fst dL_22_0) (snd dL_22_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_22_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_22_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_22_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 22 3) med_cnt_tab) with 20. change (class_size 22) with 1632. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_22 1 SC_22) with LC_22_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_22_1 SM1pre setsL_22_1 (fst dL_22_1) (snd dL_22_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_22_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_22_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_22_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 22 3) med_cnt_tab) with 20. change (class_size 22) with 1632. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_22 2 SC_22) with LC_22_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_22_2 SM1pre setsL_22_2 (fst dL_22_2) (snd dL_22_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_22_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_22_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_22_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c22.

Module Mal_agrp_c2.

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

Definition dC_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_2 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1bS30A2S10G0S44A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_2)). Qed.
Definition setsC_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_2)) in exact x).
Definition LC_2_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_2 0 SC_2) in exact x).
Definition dL_2_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_2_0 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_2_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S41S1cA2S10G0S45A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_2_0)). Qed.
Definition setsL_2_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_2_0)) in exact x).
Definition LC_2_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_2 1 SC_2) in exact x).
Definition dL_2_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_2_1 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_2_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S42S1cA2S10G0S46A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_2_1)). Qed.
Definition setsL_2_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_2_1)) in exact x).
Definition LC_2_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_2 2 SC_2) in exact x).
Definition dL_2_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_2_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_2_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S43S1cA2S10G0S47A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_2_2)). Qed.
Definition setsL_2_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_2_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 2.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3F_;F_;F_;").

Theorem cls_2 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3").
Proof using CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_2 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_2 (setp rhoB setsC_2))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_2 w setsC_2 (fst dC_2) (snd dC_2)); [reflexivity | reflexivity | exact sdC_2 | | | exact HSP].
    - cbn [fst dC_2]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_2) (snd dC_2) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_2 LC_2 (setp rhoB setsC_2) Q HkB (eq_trans runC_2 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 20).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 2 (usg ia) 20 10 10) by reflexivity.
      change (class_size 2) with 48. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 972) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_2 0 SC_2) with LC_2_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_2_0 SN2pre setsL_2_0 (fst dL_2_0) (snd dL_2_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_2_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_2_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_2_0) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 972 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 2 (usg ia) 20 10 10) by reflexivity.
      change (class_size 2) with 48. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_2 1 SC_2) with LC_2_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_2_1 SN2pre setsL_2_1 (fst dL_2_1) (snd dL_2_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_2_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_2_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_2_1) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 2 (usg ia) 20 10 10) by reflexivity.
      change (class_size 2) with 48. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_2 2 SC_2) with LC_2_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_2_2 SN2pre setsL_2_2 (fst dL_2_2) (snd dL_2_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_2_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_2_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_2_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c2.

Module Mal_agrp_c21.

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

Definition dC_21 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_21 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_21 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1bS31A2S10G0S4cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_21)). Qed.
Definition setsC_21 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_21)) in exact x).
Definition LC_21_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_21 0 SC_21) in exact x).
Definition dL_21_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z15A1S2PcA1M1A4SbG0ScS0S0S1Z550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7e00A1S2PacA1M4A4SbG0ScS0S0S1Z7e10A1S4S13G4G3A3A4SbG0ScS0S0S1Z18A1S2PafA1M5A4SbG0ScS0S0S1Z5a4c8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a470A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z540A1G2A4SbG0ScS0S0S1Z100A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z108A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z280A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z288A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_21_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S48S1aA2S10G0S4dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_21_0)). Qed.
Definition setsL_21_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_21_0)) in exact x).
Definition LC_21_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_21 1 SC_21) in exact x).
Definition dL_21_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z15A1S2PcA1M1A4SbG0ScS0S0S1Z550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3f00A1S2PacA1M4A4SbG0ScS0S0S1Z3f10A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a4c8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a470A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z540A1G2A4SbG0ScS0S0S1Z100A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z108A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z280A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z288A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_21_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S49S1aA2S10G0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_21_1)). Qed.
Definition setsL_21_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_21_1)) in exact x).
Definition LC_21_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_21 2 SC_21) in exact x).
Definition dL_21_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z15A1S2PcA1M1A4SbG0ScS0S0S1Z550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1f80A1S2PacA1M4A4SbG0ScS0S0S1Z1f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a4c8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a470A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z540A1G2A4SbG0ScS0S0S1Z100A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z108A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z280A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z288A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_21_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4aS1aA2S10G0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_21_2)). Qed.
Definition setsL_21_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_21_2)) in exact x).
Definition LC_21_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_21 3 SC_21) in exact x).
Definition dL_21_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z15A1S2PcA1M1A4SbG0ScS0S0S1Z550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfc0A1S2PacA1M4A4SbG0ScS0S0S1Zfd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a4c8A1S4S13S4S14G1G5A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a470A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z540A1G2A4SbG0ScS0S0S1Z100A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z108A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z280A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z288A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_21_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4bS1aA2S10G0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_21_3)). Qed.
Definition setsL_21_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_21_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 21.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3F_;F_;F_;").

Theorem cls_21 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_21 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_21 (setp rhoB setsC_21))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_21 w setsC_21 (fst dC_21) (snd dC_21)); [reflexivity | reflexivity | exact sdC_21 | | | exact HSP].
    - cbn [fst dC_21]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_21) (snd dC_21) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_21 LC_21 (setp rhoB setsC_21) Q HkB (eq_trans runC_21 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 24).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 21 3) med_cnt_tab) with 24. change (class_size 21) with 1344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_21 0 SC_21) with LC_21_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_21_0 SM1pre setsL_21_0 (fst dL_21_0) (snd dL_21_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_21_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_21_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_21_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 21 3) med_cnt_tab) with 24. change (class_size 21) with 1344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_21 1 SC_21) with LC_21_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_21_1 SM1pre setsL_21_1 (fst dL_21_1) (snd dL_21_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_21_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_21_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_21_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 21 3) med_cnt_tab) with 24. change (class_size 21) with 1344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_21 2 SC_21) with LC_21_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_21_2 SM1pre setsL_21_2 (fst dL_21_2) (snd dL_21_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_21_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_21_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_21_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 21 3) med_cnt_tab) with 24. change (class_size 21) with 1344. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_21 3 SC_21) with LC_21_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_21_3 SM1pre setsL_21_3 (fst dL_21_3) (snd dL_21_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_21_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_21_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_21_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c21.

Module Mal_agrp_c24.

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

Definition dC_24 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_24 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_24 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1bS33A2S10G0S5bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_24)). Qed.
Definition setsC_24 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_24)) in exact x).
Definition LC_24_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_24 0 SC_24) in exact x).
Definition dL_24_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z18A1S2PcA1M1A4SbG0ScS0S0S1Z930A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zff80A1S2PacA1M4A4SbG0ScS0S0S1Zff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z1cA1S2PafA1M5A4SbG0ScS0S0S1Z5a4e0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a488A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z920A1G2A4SbG0ScS0S0S1Z118A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z120A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z298A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2a0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_24_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S58S1aA2S10G0S5cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_24_0)). Qed.
Definition setsL_24_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_24_0)) in exact x).
Definition LC_24_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_24 1 SC_24) in exact x).
Definition dL_24_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z18A1S2PcA1M1A4SbG0ScS0S0S1Z930A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7fc0A1S2PacA1M4A4SbG0ScS0S0S1Z7fd0A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S2PafA1M5A4SbG0ScS0S0S1Z5a4e0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a488A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z920A1G2A4SbG0ScS0S0S1Z118A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z120A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z298A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2a0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_24_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S59S1aA2S10G0S5dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_24_1)). Qed.
Definition setsL_24_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_24_1)) in exact x).
Definition LC_24_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_24 2 SC_24) in exact x).
Definition dL_24_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z18A1S2PcA1M1A4SbG0ScS0S0S1Z930A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3fe0A1S2PacA1M4A4SbG0ScS0S0S1Z3ff0A1S4S13G4G3A3A4SbG0ScS0S0S1Z7A1S2PafA1M5A4SbG0ScS0S0S1Z5a4e0A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a488A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z920A1G2A4SbG0ScS0S0S1Z118A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z120A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z298A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z2a0A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_24_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S5aS1aA2S10G0S5eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_24_2)). Qed.
Definition setsL_24_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_24_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 24.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3F_;F_;F_;").

Theorem cls_24 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_24 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_24 (setp rhoB setsC_24))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_24 w setsC_24 (fst dC_24) (snd dC_24)); [reflexivity | reflexivity | exact sdC_24 | | | exact HSP].
    - cbn [fst dC_24]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_24) (snd dC_24) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_24 LC_24 (setp rhoB setsC_24) Q HkB (eq_trans runC_24 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 28).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 24 3) med_cnt_tab) with 28. change (class_size 24) with 2336. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_24 0 SC_24) with LC_24_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_24_0 SM1pre setsL_24_0 (fst dL_24_0) (snd dL_24_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_24_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_24_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_24_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 24 3) med_cnt_tab) with 28. change (class_size 24) with 2336. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_24 1 SC_24) with LC_24_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_24_1 SM1pre setsL_24_1 (fst dL_24_1) (snd dL_24_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_24_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_24_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_24_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 24 3) med_cnt_tab) with 28. change (class_size 24) with 2336. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_24 2 SC_24) with LC_24_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_24_2 SM1pre setsL_24_2 (fst dL_24_2) (snd dL_24_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_24_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_24_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_24_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c24.

Module Mal_agrp_c19.

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

Definition dC_19 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_19 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_19 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1bS2fA2S10G0S3aA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_19)). Qed.
Definition setsC_19 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_19)) in exact x).
Definition LC_19_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_19 0 SC_19) in exact x).
Definition dL_19_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z13A1S2PcA1M1A4SbG0ScS0S0S1Z400A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7e00A1S2PacA1M4A4SbG0ScS0S0S1Z7e10A1S4S13G4G3A3A4SbG0ScS0S0S1Z20A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a4b8A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a460A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3f0A1G2A4SbG0ScS0S0S1Zf0A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Zf8A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z270A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z278A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6G5A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_19_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S34S1aA2S10G0S3bA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_19_0)). Qed.
Definition setsL_19_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_19_0)) in exact x).
Definition LC_19_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_19 1 SC_19) in exact x).
Definition dL_19_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z13A1S2PcA1M1A4SbG0ScS0S0S1Z400A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3f00A1S2PacA1M4A4SbG0ScS0S0S1Z3f10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a4b8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a460A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3f0A1G2A4SbG0ScS0S0S1Zf0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zf8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z270A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z278A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_19_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S35S1aA2S10G0S3cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_19_1)). Qed.
Definition setsL_19_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_19_1)) in exact x).
Definition LC_19_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_19 2 SC_19) in exact x).
Definition dL_19_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z13A1S2PcA1M1A4SbG0ScS0S0S1Z400A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1f80A1S2PacA1M4A4SbG0ScS0S0S1Z1f90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S2PafA1M5A4SbG0ScS0S0S1Z5a4b8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a460A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3f0A1G2A4SbG0ScS0S0S1Zf0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zf8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z270A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z278A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_19_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S36S1aA2S10G0S3dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_19_2)). Qed.
Definition setsL_19_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_19_2)) in exact x).
Definition LC_19_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_19 3 SC_19) in exact x).
Definition dL_19_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z13A1S2PcA1M1A4SbG0ScS0S0S1Z400A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfc0A1S2PacA1M4A4SbG0ScS0S0S1Zfd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S2PafA1M5A4SbG0ScS0S0S1Z5a4b8A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a460A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z3f0A1G2A4SbG0ScS0S0S1Zf0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Zf8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z270A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z278A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_19_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S37S1aA2S10G0S3eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_19_3)). Qed.
Definition setsL_19_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_19_3)) in exact x).
Definition LC_19_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_19 4 SC_19) in exact x).
Definition dL_19_4 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_19_4 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_19_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S38S1cA2S10G0S3fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_19_4)). Qed.
Definition setsL_19_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_19_4)) in exact x).
Definition LC_19_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_19 5 SC_19) in exact x).
Definition dL_19_5 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_19_5 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_19_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S39S1cA2S10G0S40A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_19_5)). Qed.
Definition setsL_19_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_19_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS19VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 19.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1aA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1cA4VQ;A3F_;F_;F_;").

Theorem cls_19 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS19VK;S24Via;S1eVia;A1A2S1bA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_19 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_19 (setp rhoB setsC_19))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_19 w setsC_19 (fst dC_19) (snd dC_19)); [reflexivity | reflexivity | exact sdC_19 | | | exact HSP].
    - cbn [fst dC_19]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_19) (snd dC_19) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_19 LC_19 (setp rhoB setsC_19) Q HkB (eq_trans runC_19 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 32).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 19 3) med_cnt_tab) with 32. change (class_size 19) with 1008. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_19 0 SC_19) with LC_19_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_19_0 SM1pre setsL_19_0 (fst dL_19_0) (snd dL_19_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_19_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_19_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_19_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 19 3) med_cnt_tab) with 32. change (class_size 19) with 1008. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_19 1 SC_19) with LC_19_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_19_1 SM1pre setsL_19_1 (fst dL_19_1) (snd dL_19_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_19_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_19_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_19_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 19 3) med_cnt_tab) with 32. change (class_size 19) with 1008. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_19 2 SC_19) with LC_19_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_19_2 SM1pre setsL_19_2 (fst dL_19_2) (snd dL_19_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_19_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_19_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_19_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 19 3) med_cnt_tab) with 32. change (class_size 19) with 1008. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_19 3 SC_19) with LC_19_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_19_3 SM1pre setsL_19_3 (fst dL_19_3) (snd dL_19_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_19_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_19_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_19_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 19 3) med_cnt_tab) with 32. change (class_size 19) with 1008. icnt_decide. }
    assert (Htot : itotal ia = 2028) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_19 4 SC_19) with LC_19_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_19_4 SN2pre setsL_19_4 (fst dL_19_4) (snd dL_19_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_19_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_19_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_19_4) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 2028 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 19 3) med_cnt_tab) with 32. change (class_size 19) with 1008. icnt_decide. }
    assert (Htot : itotal ia = 2028) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_19 5 SC_19) with LC_19_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_19_5 SN2pre setsL_19_5 (fst dL_19_5) (snd dL_19_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_19_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_19_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_19_5) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 2028 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c19.
