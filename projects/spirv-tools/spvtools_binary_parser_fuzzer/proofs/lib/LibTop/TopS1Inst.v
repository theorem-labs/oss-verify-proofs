(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocIfaceStmt.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.DrvLibContract.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1TargetConsts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG2.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_65e6c_65f2c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65e6c : bv 32 := 0xff010113.
Lemma F_65e6c : fetch_word Plain.M.loaded_segments (0x65eac : word) = Some W_65e6c.
Proof. vm_refl. Qed.
Lemma D_65e6c : decode_any W_65e6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e70 : bv 32 := 0x00113423.
Lemma F_65e70 : fetch_word Plain.M.loaded_segments (0x65eb0 : word) = Some W_65e70.
Proof. vm_refl. Qed.
Lemma D_65e70 : decode_any W_65e70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e74 : bv 32 := 0x00813023.
Lemma F_65e74 : fetch_word Plain.M.loaded_segments (0x65eb4 : word) = Some W_65e74.
Proof. vm_refl. Qed.
Lemma D_65e74 : decode_any W_65e74 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e78 : bv 32 := 0x01300593.
Lemma F_65e78 : fetch_word Plain.M.loaded_segments (0x65eb8 : word) = Some W_65e78.
Proof. vm_refl. Qed.
Lemma D_65e78 : decode_any W_65e78 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e7c : bv 32 := 0x00050413.
Lemma F_65e7c : fetch_word Plain.M.loaded_segments (0x65ebc : word) = Some W_65e7c.
Proof. vm_refl. Qed.
Lemma D_65e7c : decode_any W_65e7c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e80 : bv 32 := 0x00b56863.
Lemma F_65e80 : fetch_word Plain.M.loaded_segments (0x65ec0 : word) = Some W_65e80.
Proof. vm_refl. Qed.
Lemma D_65e80 : decode_any W_65e80 = Some (Branch BC_LTU 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e84 : bv 32 := 0xfec40513.
Lemma F_65e84 : fetch_word Plain.M.loaded_segments (0x65ec4 : word) = Some W_65e84.
Proof. vm_refl. Qed.
Lemma D_65e84 : decode_any W_65e84 = Some (OpImm ALU_ADD 10 8 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e88 : bv 32 := 0x00600593.
Lemma F_65e88 : fetch_word Plain.M.loaded_segments (0x65ec8 : word) = Some W_65e88.
Proof. vm_refl. Qed.
Lemma D_65e88 : decode_any W_65e88 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e8c : bv 32 := 0x02a5e263.
Lemma F_65e8c : fetch_word Plain.M.loaded_segments (0x65ecc : word) = Some W_65e8c.
Proof. vm_refl. Qed.
Lemma D_65e8c : decode_any W_65e8c = Some (Branch BC_LTU 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e90 : bv 32 := 0x04000513.
Lemma F_65e90 : fetch_word Plain.M.loaded_segments (0x65ed0 : word) = Some W_65e90.
Proof. vm_refl. Qed.
Lemma D_65e90 : decode_any W_65e90 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e94 : bv 32 := 0x7097f0ef.
Lemma F_65e94 : fetch_word Plain.M.loaded_segments (0x65ed4 : word) = Some W_65e94.
Proof. vm_refl. Qed.
Lemma D_65e94 : decode_any W_65e94 = Some (Jal 1 524040, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e98 : bv 32 := 0x00852023.
Lemma F_65e98 : fetch_word Plain.M.loaded_segments (0x65ed8 : word) = Some W_65e98.
Proof. vm_refl. Qed.
Lemma D_65e98 : decode_any W_65e98 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e9c : bv 32 := 0x02053823.
Lemma F_65e9c : fetch_word Plain.M.loaded_segments (0x65edc : word) = Some W_65e9c.
Proof. vm_refl. Qed.
Lemma D_65e9c : decode_any W_65e9c = Some (Store SZ8 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ea0 : bv 32 := 0x00813083.
Lemma F_65ea0 : fetch_word Plain.M.loaded_segments (0x65ee0 : word) = Some W_65ea0.
Proof. vm_refl. Qed.
Lemma D_65ea0 : decode_any W_65ea0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ea4 : bv 32 := 0x00013403.
Lemma F_65ea4 : fetch_word Plain.M.loaded_segments (0x65ee4 : word) = Some W_65ea4.
Proof. vm_refl. Qed.
Lemma D_65ea4 : decode_any W_65ea4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ea8 : bv 32 := 0x01010113.
Lemma F_65ea8 : fetch_word Plain.M.loaded_segments (0x65ee8 : word) = Some W_65ea8.
Proof. vm_refl. Qed.
Lemma D_65ea8 : decode_any W_65ea8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eac : bv 32 := 0x00008067.
Lemma F_65eac : fetch_word Plain.M.loaded_segments (0x65eec : word) = Some W_65eac.
Proof. vm_refl. Qed.
Lemma D_65eac : decode_any W_65eac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ec4 : bv 32 := 0x02050863.
Lemma F_65ec4 : fetch_word Plain.M.loaded_segments (0x65f04 : word) = Some W_65ec4.
Proof. vm_refl. Qed.
Lemma D_65ec4 : decode_any W_65ec4 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ec8 : bv 32 := 0xff010113.
Lemma F_65ec8 : fetch_word Plain.M.loaded_segments (0x65f08 : word) = Some W_65ec8.
Proof. vm_refl. Qed.
Lemma D_65ec8 : decode_any W_65ec8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ecc : bv 32 := 0x00113423.
Lemma F_65ecc : fetch_word Plain.M.loaded_segments (0x65f0c : word) = Some W_65ecc.
Proof. vm_refl. Qed.
Lemma D_65ecc : decode_any W_65ecc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ed0 : bv 32 := 0x00813023.
Lemma F_65ed0 : fetch_word Plain.M.loaded_segments (0x65f10 : word) = Some W_65ed0.
Proof. vm_refl. Qed.
Lemma D_65ed0 : decode_any W_65ed0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ed4 : bv 32 := 0x00050613.
Lemma F_65ed4 : fetch_word Plain.M.loaded_segments (0x65f14 : word) = Some W_65ed4.
Proof. vm_refl. Qed.
Lemma D_65ed4 : decode_any W_65ed4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ed8 : bv 32 := 0x03053503.
Lemma F_65ed8 : fetch_word Plain.M.loaded_segments (0x65f18 : word) = Some W_65ed8.
Proof. vm_refl. Qed.
Lemma D_65ed8 : decode_any W_65ed8 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65edc : bv 32 := 0x01060593.
Lemma F_65edc : fetch_word Plain.M.loaded_segments (0x65f1c : word) = Some W_65edc.
Proof. vm_refl. Qed.
Lemma D_65edc : decode_any W_65edc = Some (OpImm ALU_ADD 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee0 : bv 32 := 0x00b50c63.
Lemma F_65ee0 : fetch_word Plain.M.loaded_segments (0x65f20 : word) = Some W_65ee0.
Proof. vm_refl. Qed.
Lemma D_65ee0 : decode_any W_65ee0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee4 : bv 32 := 0x02050863.
Lemma F_65ee4 : fetch_word Plain.M.loaded_segments (0x65f24 : word) = Some W_65ee4.
Proof. vm_refl. Qed.
Lemma D_65ee4 : decode_any W_65ee4 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee8 : bv 32 := 0x00060413.

Definition W_65eec : bv 32 := 0x02800593.

Definition W_65ef0 : bv 32 := 0x0100006f.

Definition W_65ef4 : bv 32 := 0x00008067.

Definition W_65ef8 : bv 32 := 0x00060413.

Definition W_65efc : bv 32 := 0x02000593.

Definition W_65f00 : bv 32 := 0x00053603.

Definition W_65f04 : bv 32 := 0x00b605b3.

Definition W_65f08 : bv 32 := 0x0005b583.

Definition W_65f0c : bv 32 := 0x000580e7.

Definition W_65f10 : bv 32 := 0x00040613.

Definition W_65f14 : bv 32 := 0x04000593.
Lemma F_65f14 : fetch_word Plain.M.loaded_segments (0x65f54 : word) = Some W_65f14.
Proof. vm_refl. Qed.
Lemma D_65f14 : decode_any W_65f14 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f18 : bv 32 := 0x00060513.
Lemma F_65f18 : fetch_word Plain.M.loaded_segments (0x65f58 : word) = Some W_65f18.
Proof. vm_refl. Qed.
Lemma D_65f18 : decode_any W_65f18 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f1c : bv 32 := 0x00813083.
Lemma F_65f1c : fetch_word Plain.M.loaded_segments (0x65f5c : word) = Some W_65f1c.
Proof. vm_refl. Qed.
Lemma D_65f1c : decode_any W_65f1c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f20 : bv 32 := 0x00013403.
Lemma F_65f20 : fetch_word Plain.M.loaded_segments (0x65f60 : word) = Some W_65f20.
Proof. vm_refl. Qed.
Lemma D_65f20 : decode_any W_65f20 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f24 : bv 32 := 0x01010113.
Lemma F_65f24 : fetch_word Plain.M.loaded_segments (0x65f64 : word) = Some W_65f24.
Proof. vm_refl. Qed.
Lemma D_65f24 : decode_any W_65f24 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f28 : bv 32 := 0x40d0706f.
Lemma F_65f28 : fetch_word Plain.M.loaded_segments (0x65f68 : word) = Some W_65f28.
Proof. vm_refl. Qed.
Lemma D_65f28 : decode_any W_65f28 = Some (Jal 0 31756, 4%Z).
Proof. vm_refl. Qed.
End S1_code_65e6c_65f2c.

Module Lib_Ctx.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Cxx_OperatorDelete OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.S1_code_65e6c_65f2c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac b2z8 := apply bytes_le_to_Z_8.

Ltac msteps_close :=
  lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
    unify r' r; replace pc' with pc by (apply bv_eq; vm_compute; reflexivity);
    replace m' with m by reflexivity; apply mst_refl end.
Ltac rdW a' :=
  lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with a' by lia end;
  peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia.

Section Ctx.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition cS1 : ctx_consts := {| cc_create := 0x65eac; cc_destroy := 0x65f04; cc_stack := 16 |}.

  Theorem ctx_create_65e08_spec : ctx_create_stmt SEGS Ly.L MI ST cS1.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret env K.
    cbn [cc_create cc_stack cS1]. lazy zeta.
    intros CB Ha0 ENV ROOM HNMAX CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (16 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. unfold CTX_SZ in *.
    unfold env_valid in ENV. assert (Henv : 0 <= env <= 26) by lia.
    assert (WIN : forall a, sp - (16 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (16 + (16 + MALLOC_STACK MI))) (16 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    set (M1 := wslots M sp [getr R 8%bv; Z_to_bv 64 ret]).
    assert (ST1 : stores_in (zwin (sp - 16) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp [getr R 8%bv; Z_to_bv 64 ret]); unfold Zlen; cbn; lia. }
    assert (SL1 : rdn SEGS M1 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
    { unfold M1. rewrite (wslots_read SEGS M sp _ 1) by (unfold Zlen; cbn; lia). reflexivity. }
    assert (SL2 : rdn SEGS M1 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))).
    { unfold M1. rewrite (wslots_read SEGS M sp _ 2) by (unfold Zlen; cbn; lia). reflexivity. }

    assert (B1 : exists Rn,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x65eac) M (seg_rom SEGS))
                  (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) M1 (seg_rom SEGS))
      /\ getr Rn 10%bv = Z_to_bv 64 64 /\ getr Rn 1%bv = Z_to_bv 64 0x65ed8
      /\ getr Rn 2%bv = Z_to_bv 64 (sp - 16) /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
      /\ getr Rn 8%bv = Z_to_bv 64 env
      /\ (forall r, In r [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r)).
    { destruct (Z.lt_ge_cases env 19) as [Hlt|Hge].
      - eexists. split.
        + norm_pc.
          sv F_65e6c D_65e6c (Z_to_bv 64 (sp - 16)).
          stw F_65e70 D_65e70 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
          stw F_65e74 D_65e74 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
          sv F_65e78 D_65e78 (Z_to_bv 64 19).
          sv F_65e7c D_65e7c (Z_to_bv 64 env).
          stepb_tk F_65e80 D_65e80 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          sv F_65e90 D_65e90 (Z_to_bv 64 64).
          stepj F_65e94 D_65e94.
          unfold M1. msteps_close.
        + gres. repeat split; try reflexivity; try assumption.
          intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
      - eexists. split.
        + norm_pc.
          sv F_65e6c D_65e6c (Z_to_bv 64 (sp - 16)).
          stw F_65e70 D_65e70 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
          stw F_65e74 D_65e74 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
          sv F_65e78 D_65e78 (Z_to_bv 64 19).
          sv F_65e7c D_65e7c (Z_to_bv 64 env).
          stepb_ft F_65e80 D_65e80 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_65e84 D_65e84 (Z_to_bv 64 (env - 20)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          sv F_65e88 D_65e88 (Z_to_bv 64 6).
          stepb_ft F_65e8c D_65e8c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          sv F_65e90 D_65e90 (Z_to_bv 64 64).
          stepj F_65e94 D_65e94.
          unfold M1. msteps_close.
        + gres. repeat split; try reflexivity; try assumption.
          intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    destruct B1 as (Rn & RUN1 & Rn10 & Rn1 & Rn2 & Rn3 & Rn4 & Rn8 & RnS).
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN1 | ].
    eapply (NEW fx A s Rn M1 model 64 (sp - 16) 0x65ed8 K).
    - eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
    - exact MS.
    - eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
    - eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
      intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
    - exact SXH.
    - constructor.
      + exact Rn1. + unfold ret_ok. apply bv_eq. vm_compute. reflexivity. + lia. + exact Rn2.
      + replace (sp - 16) with (sp - 16 * 1) by lia. apply mod16_sub. exact Hsp16.
      + lia. + rewrite Rn3. exact Hgp. + rewrite Rn4. exact Htp.
    - exact Rn10.
    - lia.
    - lia.
    - unfold stack_room. replace (sp - 16 - (16 + MALLOC_STACK MI)) with (sp - (16 + (16 + MALLOC_STACK MI))) by lia.
      apply (mdef_store_ok SEGS M1 _ (16 + (16 + MALLOC_STACK MI))); [eapply stores_in_mdef; [exact ST1 | exact HDW] | lia | lia | lia].
    - intros a Ha. apply Hwin. unfold zwin in *. lia.
    - exact Hown_sx.
    - exact Herr_sx.
    - rewrite new_size_id by lia. eapply (roomL_room_for SEGS Ly.L MI); [exact AI | lia | exact ROOM].
    -
      intros A1 R2 M2 model1 p AI1 MS1 Hfs1 Hfds1 SX1 KEPT2 R2a0 Hp LADD CAPS1 BIGC1 NEWT1 FR1 DEF1.
      rewrite new_size_id in LADD, FR1 by lia.
      assert (HinP : In (p, 64) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
      destruct (live_range SEGS Ly.L MI A1 M2 model1 p 64 AI1 HinP) as (_ & Hpal & _ & Hpce).
      assert (HDp : mdef M2 p 64) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
      assert (Hpown : forall a, p <= a < p + 64 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
      { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
      assert (WIN1 : forall a, sp - (16 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
      { intros a Ha. apply (stack_sep A1 M2 model1 a AI1). lia. }
      assert (PRES2 : forall a, sp - 16 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. apply FR1. rewrite u64_of_Z by lia. intros [Ho|[Hblk|[Hw|He]]].
        - exact (proj1 (WIN1 a ltac:(lia)) Ho).
        - lia.
        - unfold zwin in Hw. lia.
        - pose proof (ly_errno_img a He) as Hi. rewrite ly_img_iff in Hi. lia. }
      assert (SL1' : rdn SEGS M2 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
      { rewrite (rdn_agree_win SEGS M1 M2); [exact SL1 | lia | cbn; lia | intros a Ha; apply PRES2; unfold zwin in Ha; cbn in Ha; lia]. }
      assert (SL2' : rdn SEGS M2 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))).
      { rewrite (rdn_agree_win SEGS M1 M2); [exact SL2 | lia | cbn; lia | intros a Ha; apply PRES2; unfold zwin in Ha; cbn in Ha; lia]. }
      assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
      assert (R2_8 : getr R2 8%bv = Z_to_bv 64 env) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
      set (M3 := wbytes (wbytes M2 (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 env)))
                        (Z_to_bv 64 (p + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      assert (ST23 : stores_in (zwin p (p + 64)) M2 M3).
      { unfold M3. eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |]; rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin; lia. }

      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
      { norm_pc.
        stw F_65e98 D_65e98 (Z_to_bv 64 p) (Z_to_bv 64 env) ltac:(ok_mdef HDp).
        stw F_65e9c D_65e9c (Z_to_bv 64 (p + 48)) (Z_to_bv 64 0) ltac:(ok_mdef HDp).
        ld_step F_65ea0 D_65ea0 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(peel; rdn_fix SL1') ltac:(b2z8).
        ld_step F_65ea4 D_65ea4 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(peel; rdn_fix SL2') ltac:(b2z8).
        sv F_65ea8 D_65ea8 (Z_to_bv 64 sp).
        stepjr F_65eac D_65eac (Z_to_bv 64 ret) ltac:(gres; reflexivity).
        apply mst_refl. }
      fold M3.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 ret) by (symmetry; exact Hret) end.
      eapply (CONT A1 _ M3 model1 p).
      + constructor.
        * eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST23 |]. intros a Ha. apply Hpown. unfold zwin in Ha. lia.
        * exact MS1. * exact Hfs1. * exact Hfds1.
        * eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST23 |].
          intros a Ha. destruct (offimg_sep a (proj2 (Hpown a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
        * intros r Hr; unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption
                    | rewrite (KEPT2 _) by in_cs; first [rewrite Rn3; reflexivity | rewrite Rn4; reflexivity | apply RnS; in_cs] ] |]).
          destruct Hr.
      + gres. exact R2a0.
      + unfold CRep.ctx_rep, CTX_SZ. split; [lia|]. split; [exact Hpal|]. split; [lia|]. split; [exact HinP|].
        split.
        * unfold fld, M3. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
          apply rdn_wbytes_hit4. rewrite u64_of_Z by lia. lia.
        * unfold fld, M3. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
      + cbn. exists (live MI A1). split; [exact LADD | reflexivity].
      + unfold CTX_SZ. eapply eff_weaken.
        * eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of in Ha; cbn in Ha; lia].
          -- eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of in Ha; cbn in Ha; lia].
             ++ apply (eff_store MI A M M1 (sp - (16 + (16 + MALLOC_STACK MI)), sp) (zwin p (p + 64))); [| exact (proj2 ST1)].
                intros a HF HW. apply (proj1 ST1). intros Hz. apply HW. unfold W_of, zwin in *. cbn. lia.
             ++ eapply (eff_of_new MI A A1 M1 M2 model1 _ (zwin p (p + 64)) p 64); try eassumption.
                ** intros a Ha. unfold W_of, zwin in *. cbn. lia.
                ** intros a Ha. unfold zwin. lia.
          -- apply (eff_store MI A1 M2 M3 _ (zwin p (p + 64))); [| exact (proj2 ST23)].
             intros a HF HW. apply (proj1 ST23). exact HF.
        * intros a [[H|H]|H]; exact H.
  Qed.

  Theorem ctx_destroy_65e60_spec : ctx_destroy_stmt SEGS Ly.L MI ST cS1.
  Proof using AC MI ST MALLOC_STACK_pos.
    intros fx A s R M model sp ret q env K.
    cbn [cc_destroy cc_stack cS1]. lazy zeta.
    intros CB Ha0 CTX CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    pose proof ac_bounds_lit as Hceilv.
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (16 + MALLOC_STACK MI)) by (lia).
    destruct CTX as (Hq0 & Hqal & Hq1 & HIn & Fenv & Ff). unfold CTX_SZ in *. unfold fld in Fenv, Ff.
    assert (WIN : forall a, sp - (16 + MALLOC_STACK MI) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (16 + MALLOC_STACK MI)) (16 + MALLOC_STACK MI)).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    destruct (live_range SEGS Ly.L MI A M model q 64 AI HIn) as (_ & _ & _ & Hqce).
    set (M1 := wslots M sp [getr R 8%bv; Z_to_bv 64 ret]).
    assert (ST1 : stores_in (zwin (sp - 16) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp [getr R 8%bv; Z_to_bv 64 ret]); unfold Zlen; cbn; lia. }
    assert (SL1 : rdn SEGS M1 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
    { unfold M1. rewrite (wslots_read SEGS M sp _ 1) by (unfold Zlen; cbn; lia). reflexivity. }
    assert (SL2 : rdn SEGS M1 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))).
    { unfold M1. rewrite (wslots_read SEGS M sp _ 2) by (unfold Zlen; cbn; lia). reflexivity. }
    assert (Ff' : rdn SEGS M1 (Z_to_bv 64 (q + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { rewrite (rdn_agree_win SEGS M M1); [exact Ff | lia | cbn; lia |].
      eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *; cbn in Ha. lia. }

    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
    { norm_pc.
      stepb_ft F_65ec4 D_65ec4 ltac:(rewrite Ha0; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
      sv F_65ec8 D_65ec8 (Z_to_bv 64 (sp - 16)).
      stw F_65ecc D_65ecc (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_65ed0 D_65ed0 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
      sv F_65ed4 D_65ed4 (Z_to_bv 64 q).
      ld_step F_65ed8 D_65ed8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix Ff') ltac:(b2z8).
      stepiv F_65edc D_65edc (Z_to_bv 64 (q + 16)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      stepb_ft F_65ee0 D_65ee0 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
      stepb_tk F_65ee4 D_65ee4 ltac:(apply c_eq_refl).
      sv F_65f14 D_65f14 (Z_to_bv 64 64).
      sv F_65f18 D_65f18 (Z_to_bv 64 q).
      ld_step F_65f1c D_65f1c (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdW (sp - 8)) ltac:(b2z8).
      ld_step F_65f20 D_65f20 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(rdW (sp - 16)) ltac:(b2z8).
      sv F_65f24 D_65f24 (Z_to_bv 64 sp).
      stepj F_65f28 D_65f28.
      apply mst_refl. }
    fold M1.
    lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
      replace pc with (Z_to_bv 64 DEL1) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
    eapply (op_delete1_spec MI fx A R5 M1 model q 64 sp ret K).
    - eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
    - exact MS.
    - eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
    - constructor; unfold R5; gres; try assumption; reflexivity.
    - unfold R5; gres; reflexivity.
    - right. exact HIn.
    - lia.
    - unfold stack_room. replace (sp - MALLOC_STACK MI) with (sp - (16 + MALLOC_STACK MI) + 16) by lia.
      apply (mdef_store_ok_off SEGS M1 _ _ 16 _ (stores_in_mdef _ _ _ _ _ ST1 HDW)); lia.
    - intros a Ha. apply WIN. unfold zwin in Ha. lia.
    - intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 KEPT6 LDEL CAPS2 BIGC2 OWN2 FR2 DEF2.
      eapply (CONT A2 R6 M6 model2).
      + constructor.
        * exact AI2. * exact MS2. * exact Hfs2. * exact Hfds2.
        * eapply (sx_through SEGS Ly.L ST); [ | exact FR2 | ].
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
             intros a Ha. apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). apply WIN. unfold zwin in Ha. lia.
          -- intros a [Ho|[Hblk|[Hw|He]]].
             ++ eapply (owned_not_sx SEGS Ly.L MI ST ly_relro_img ly_rw_not_relro); [exact AI | exact Hown_sx | exact Ho].
             ++ apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). eapply (live_offimg SEGS Ly.L MI); [exact AI | exact HIn | exact Hblk].
             ++ apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). apply WIN. unfold zwin in Hw. lia.
             ++ split; [exact (Herr_sx a He) | intros Hr; exact (ly_rw_not_relro a (ly_errno_rw a He) Hr)].
        * intros r Hr. rewrite (KEPT6 r Hr). unfold R5. pose proof Hr as Hr'. unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption] |]). destruct Hr.
      + cbn. exists (live MI A2). split; [exact LDEL | reflexivity].
      + eapply eff_weaken.
        * eapply (eff_trans MI); [ | | intros a Ha; apply (stack_sep A2 M6 model2 a AI2); unfold W_of in Ha; cbn in Ha; lia].
          -- apply (eff_store MI A M M1 (sp - (16 + MALLOC_STACK MI), sp) (zwin q (q + 64))); [| exact (proj2 ST1)].
             intros a HF HW. apply (proj1 ST1). intros Hz. apply HW. unfold W_of, zwin in *. cbn. lia.
          -- eapply (eff_of_del MI A A2 M1 M6 _ (zwin q (q + 64)) q 64); try eassumption.
             ++ intros a Ha. unfold W_of, zwin in *. cbn. lia.
             ++ intros a Ha. unfold zwin. lia.
             ++ intros a Ha. eapply (live_offimg SEGS Ly.L MI); [exact AI | exact HIn | exact Ha].
        * intros a [H|H]; exact H.
  Qed.
End Ctx.
End Lib_Ctx.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemset.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_65b90_65d64.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65b90 : bv 32 := 0x00053603.
Lemma F_65b90 : fetch_word Plain.M.loaded_segments (0x65bd0 : word) = Some W_65b90.
Proof. vm_refl. Qed.
Lemma D_65b90 : decode_any W_65b90 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b94 : bv 32 := 0x00853683.
Lemma F_65b94 : fetch_word Plain.M.loaded_segments (0x65bd4 : word) = Some W_65b94.
Proof. vm_refl. Qed.
Lemma D_65b94 : decode_any W_65b94 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b98 : bv 32 := 0x40c686b3.
Lemma F_65b98 : fetch_word Plain.M.loaded_segments (0x65bd8 : word) = Some W_65b98.
Proof. vm_refl. Qed.
Lemma D_65b98 : decode_any W_65b98 = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b9c : bv 32 := 0x4026d693.
Lemma F_65b9c : fetch_word Plain.M.loaded_segments (0x65bdc : word) = Some W_65b9c.
Proof. vm_refl. Qed.
Lemma D_65b9c : decode_any W_65b9c = Some (ShiftImm ALU_SRA 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ba0 : bv 32 := 0x00b6f663.
Lemma F_65ba0 : fetch_word Plain.M.loaded_segments (0x65be0 : word) = Some W_65ba0.
Proof. vm_refl. Qed.
Lemma D_65ba0 : decode_any W_65ba0 = Some (Branch BC_GEU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ba4 : bv 32 := 0x40d585b3.
Lemma F_65ba4 : fetch_word Plain.M.loaded_segments (0x65be4 : word) = Some W_65ba4.
Proof. vm_refl. Qed.
Lemma D_65ba4 : decode_any W_65ba4 = Some (Op ALU_SUB 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ba8 : bv 32 := 0x0180006f.
Lemma F_65ba8 : fetch_word Plain.M.loaded_segments (0x65be8 : word) = Some W_65ba8.
Proof. vm_refl. Qed.
Lemma D_65ba8 : decode_any W_65ba8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bac : bv 32 := 0x00d5f863.
Lemma F_65bac : fetch_word Plain.M.loaded_segments (0x65bec : word) = Some W_65bac.
Proof. vm_refl. Qed.
Lemma D_65bac : decode_any W_65bac = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bbc : bv 32 := 0x00008067.
Lemma F_65bbc : fetch_word Plain.M.loaded_segments (0x65bfc : word) = Some W_65bbc.
Proof. vm_refl. Qed.
Lemma D_65bbc : decode_any W_65bbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bc0 : bv 32 := 0xf9010113.
Lemma F_65bc0 : fetch_word Plain.M.loaded_segments (0x65c00 : word) = Some W_65bc0.
Proof. vm_refl. Qed.
Lemma D_65bc0 : decode_any W_65bc0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bc4 : bv 32 := 0x06113423.
Lemma F_65bc4 : fetch_word Plain.M.loaded_segments (0x65c04 : word) = Some W_65bc4.
Proof. vm_refl. Qed.
Lemma D_65bc4 : decode_any W_65bc4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bc8 : bv 32 := 0x06813023.
Lemma F_65bc8 : fetch_word Plain.M.loaded_segments (0x65c08 : word) = Some W_65bc8.
Proof. vm_refl. Qed.
Lemma D_65bc8 : decode_any W_65bc8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bcc : bv 32 := 0x04913c23.
Lemma F_65bcc : fetch_word Plain.M.loaded_segments (0x65c0c : word) = Some W_65bcc.
Proof. vm_refl. Qed.
Lemma D_65bcc : decode_any W_65bcc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bd0 : bv 32 := 0x05213823.
Lemma F_65bd0 : fetch_word Plain.M.loaded_segments (0x65c10 : word) = Some W_65bd0.
Proof. vm_refl. Qed.
Lemma D_65bd0 : decode_any W_65bd0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bd4 : bv 32 := 0x05313423.
Lemma F_65bd4 : fetch_word Plain.M.loaded_segments (0x65c14 : word) = Some W_65bd4.
Proof. vm_refl. Qed.
Lemma D_65bd4 : decode_any W_65bd4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bd8 : bv 32 := 0x05413023.
Lemma F_65bd8 : fetch_word Plain.M.loaded_segments (0x65c18 : word) = Some W_65bd8.
Proof. vm_refl. Qed.
Lemma D_65bd8 : decode_any W_65bd8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bdc : bv 32 := 0x03513c23.
Lemma F_65bdc : fetch_word Plain.M.loaded_segments (0x65c1c : word) = Some W_65bdc.
Proof. vm_refl. Qed.
Lemma D_65bdc : decode_any W_65bdc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65be0 : bv 32 := 0x03613823.
Lemma F_65be0 : fetch_word Plain.M.loaded_segments (0x65c20 : word) = Some W_65be0.
Proof. vm_refl. Qed.
Lemma D_65be0 : decode_any W_65be0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65be4 : bv 32 := 0x03713423.
Lemma F_65be4 : fetch_word Plain.M.loaded_segments (0x65c24 : word) = Some W_65be4.
Proof. vm_refl. Qed.
Lemma D_65be4 : decode_any W_65be4 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65be8 : bv 32 := 0x00050413.
Lemma F_65be8 : fetch_word Plain.M.loaded_segments (0x65c28 : word) = Some W_65be8.
Proof. vm_refl. Qed.
Lemma D_65be8 : decode_any W_65be8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bec : bv 32 := 0x00853983.
Lemma F_65bec : fetch_word Plain.M.loaded_segments (0x65c2c : word) = Some W_65bec.
Proof. vm_refl. Qed.
Lemma D_65bec : decode_any W_65bec = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bf0 : bv 32 := 0x01053503.
Lemma F_65bf0 : fetch_word Plain.M.loaded_segments (0x65c30 : word) = Some W_65bf0.
Proof. vm_refl. Qed.
Lemma D_65bf0 : decode_any W_65bf0 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bf4 : bv 32 := 0x41350633.
Lemma F_65bf4 : fetch_word Plain.M.loaded_segments (0x65c34 : word) = Some W_65bf4.
Proof. vm_refl. Qed.
Lemma D_65bf4 : decode_any W_65bf4 = Some (Op ALU_SUB 12 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bf8 : bv 32 := 0x40265613.
Lemma F_65bf8 : fetch_word Plain.M.loaded_segments (0x65c38 : word) = Some W_65bf8.
Proof. vm_refl. Qed.
Lemma D_65bf8 : decode_any W_65bf8 = Some (ShiftImm ALU_SRA 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65bfc : bv 32 := 0x00058493.
Lemma F_65bfc : fetch_word Plain.M.loaded_segments (0x65c3c : word) = Some W_65bfc.
Proof. vm_refl. Qed.
Lemma D_65bfc : decode_any W_65bfc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c00 : bv 32 := 0x06b67263.
Lemma F_65c00 : fetch_word Plain.M.loaded_segments (0x65c40 : word) = Some W_65c00.
Proof. vm_refl. Qed.
Lemma D_65c00 : decode_any W_65c00 = Some (Branch BC_GEU 12 11 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c04 : bv 32 := 0x00043903.
Lemma F_65c04 : fetch_word Plain.M.loaded_segments (0x65c44 : word) = Some W_65c04.
Proof. vm_refl. Qed.
Lemma D_65c04 : decode_any W_65c04 = Some (Load SZ8 true 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c08 : bv 32 := 0x41298a33.
Lemma F_65c08 : fetch_word Plain.M.loaded_segments (0x65c48 : word) = Some W_65c08.
Proof. vm_refl. Qed.
Lemma D_65c08 : decode_any W_65c08 = Some (Op ALU_SUB 20 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c0c : bv 32 := 0x402a5a93.
Lemma F_65c0c : fetch_word Plain.M.loaded_segments (0x65c4c : word) = Some W_65c0c.
Proof. vm_refl. Qed.
Lemma D_65c0c : decode_any W_65c0c = Some (ShiftImm ALU_SRA 21 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c10 : bv 32 := 0x009a8633.
Lemma F_65c10 : fetch_word Plain.M.loaded_segments (0x65c50 : word) = Some W_65c10.
Proof. vm_refl. Qed.
Lemma D_65c10 : decode_any W_65c10 = Some (Op ALU_ADD 12 21 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c14 : bv 32 := 0x03e65593.
Lemma F_65c14 : fetch_word Plain.M.loaded_segments (0x65c54 : word) = Some W_65c14.
Proof. vm_refl. Qed.
Lemma D_65c14 : decode_any W_65c14 = Some (ShiftImm ALU_SRL 11 12 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c18 : bv 32 := 0x10059663.
Lemma F_65c18 : fetch_word Plain.M.loaded_segments (0x65c58 : word) = Some W_65c18.
Proof. vm_refl. Qed.
Lemma D_65c18 : decode_any W_65c18 = Some (Branch BC_NE 11 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c1c : bv 32 := 0x41250533.
Lemma F_65c1c : fetch_word Plain.M.loaded_segments (0x65c5c : word) = Some W_65c1c.
Proof. vm_refl. Qed.
Lemma D_65c1c : decode_any W_65c1c = Some (Op ALU_SUB 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c20 : bv 32 := 0x40155593.
Lemma F_65c20 : fetch_word Plain.M.loaded_segments (0x65c60 : word) = Some W_65c20.
Proof. vm_refl. Qed.
Lemma D_65c20 : decode_any W_65c20 = Some (ShiftImm ALU_SRA 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c24 : bv 32 := 0x00b66463.
Lemma F_65c24 : fetch_word Plain.M.loaded_segments (0x65c64 : word) = Some W_65c24.
Proof. vm_refl. Qed.
Lemma D_65c24 : decode_any W_65c24 = Some (Branch BC_LTU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c28 : bv 32 := 0x00060593.
Lemma F_65c28 : fetch_word Plain.M.loaded_segments (0x65c68 : word) = Some W_65c28.
Proof. vm_refl. Qed.
Lemma D_65c28 : decode_any W_65c28 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c2c : bv 32 := 0xff900613.
Lemma F_65c2c : fetch_word Plain.M.loaded_segments (0x65c6c : word) = Some W_65c2c.
Proof. vm_refl. Qed.
Lemma D_65c2c : decode_any W_65c2c = Some (OpImm ALU_ADD 12 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c30 : bv 32 := 0x00165613.
Lemma F_65c30 : fetch_word Plain.M.loaded_segments (0x65c70 : word) = Some W_65c30.
Proof. vm_refl. Qed.
Lemma D_65c30 : decode_any W_65c30 = Some (ShiftImm ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c34 : bv 32 := 0x00c56663.
Lemma F_65c34 : fetch_word Plain.M.loaded_segments (0x65c74 : word) = Some W_65c34.
Proof. vm_refl. Qed.
Lemma D_65c34 : decode_any W_65c34 = Some (Branch BC_LTU 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c40 : bv 32 := 0x02813023.
Lemma F_65c40 : fetch_word Plain.M.loaded_segments (0x65c80 : word) = Some W_65c40.
Proof. vm_refl. Qed.
Lemma D_65c40 : decode_any W_65c40 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c44 : bv 32 := 0x04058263.
Lemma F_65c44 : fetch_word Plain.M.loaded_segments (0x65c84 : word) = Some W_65c44.
Proof. vm_refl. Qed.
Lemma D_65c44 : decode_any W_65c44 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c48 : bv 32 := 0x00040513.
Lemma F_65c48 : fetch_word Plain.M.loaded_segments (0x65c88 : word) = Some W_65c48.
Proof. vm_refl. Qed.
Lemma D_65c48 : decode_any W_65c48 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c4c : bv 32 := 0x1b4000ef.
Lemma F_65c4c : fetch_word Plain.M.loaded_segments (0x65c8c : word) = Some W_65c4c.
Proof. vm_refl. Qed.
Lemma D_65c4c : decode_any W_65c4c = Some (Jal 1 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c50 : bv 32 := 0x00043903.
Lemma F_65c50 : fetch_word Plain.M.loaded_segments (0x65c90 : word) = Some W_65c50.
Proof. vm_refl. Qed.
Lemma D_65c50 : decode_any W_65c50 = Some (Load SZ8 true 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c54 : bv 32 := 0x00843603.
Lemma F_65c54 : fetch_word Plain.M.loaded_segments (0x65c94 : word) = Some W_65c54.
Proof. vm_refl. Qed.
Lemma D_65c54 : decode_any W_65c54 = Some (Load SZ8 true 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c58 : bv 32 := 0x412609b3.
Lemma F_65c58 : fetch_word Plain.M.loaded_segments (0x65c98 : word) = Some W_65c58.
Proof. vm_refl. Qed.
Lemma D_65c58 : decode_any W_65c58 = Some (Op ALU_SUB 19 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c5c : bv 32 := 0x4029da93.
Lemma F_65c5c : fetch_word Plain.M.loaded_segments (0x65c9c : word) = Some W_65c5c.
Proof. vm_refl. Qed.
Lemma D_65c5c : decode_any W_65c5c = Some (ShiftImm ALU_SRA 21 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c60 : bv 32 := 0x0300006f.
Lemma F_65c60 : fetch_word Plain.M.loaded_segments (0x65ca0 : word) = Some W_65c60.
Proof. vm_refl. Qed.
Lemma D_65c60 : decode_any W_65c60 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c90 : bv 32 := 0x01450a33.
Lemma F_65c90 : fetch_word Plain.M.loaded_segments (0x65cd0 : word) = Some W_65c90.
Proof. vm_refl. Qed.
Lemma D_65c90 : decode_any W_65c90 = Some (Op ALU_ADD 20 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c94 : bv 32 := 0x00259593.
Lemma F_65c94 : fetch_word Plain.M.loaded_segments (0x65cd4 : word) = Some W_65c94.
Proof. vm_refl. Qed.
Lemma D_65c94 : decode_any W_65c94 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c98 : bv 32 := 0x00b50b33.
Lemma F_65c98 : fetch_word Plain.M.loaded_segments (0x65cd8 : word) = Some W_65c98.
Proof. vm_refl. Qed.
Lemma D_65c98 : decode_any W_65c98 = Some (Op ALU_ADD 22 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65c9c : bv 32 := 0x00249493.
Lemma F_65c9c : fetch_word Plain.M.loaded_segments (0x65cdc : word) = Some W_65c9c.
Proof. vm_refl. Qed.
Lemma D_65c9c : decode_any W_65c9c = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ca0 : bv 32 := 0x000a0513.
Lemma F_65ca0 : fetch_word Plain.M.loaded_segments (0x65ce0 : word) = Some W_65ca0.
Proof. vm_refl. Qed.
Lemma D_65ca0 : decode_any W_65ca0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ca4 : bv 32 := 0x00000593.
Lemma F_65ca4 : fetch_word Plain.M.loaded_segments (0x65ce4 : word) = Some W_65ca4.
Proof. vm_refl. Qed.
Lemma D_65ca4 : decode_any W_65ca4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ca8 : bv 32 := 0x00048613.
Lemma F_65ca8 : fetch_word Plain.M.loaded_segments (0x65ce8 : word) = Some W_65ca8.
Proof. vm_refl. Qed.
Lemma D_65ca8 : decode_any W_65ca8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cac : bv 32 := 0x6d87b0ef.
Lemma F_65cac : fetch_word Plain.M.loaded_segments (0x65cec : word) = Some W_65cac.
Proof. vm_refl. Qed.
Lemma D_65cac : decode_any W_65cac = Some (Jal 1 505560, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cb0 : bv 32 := 0x009a0bb3.
Lemma F_65cb0 : fetch_word Plain.M.loaded_segments (0x65cf0 : word) = Some W_65cb0.
Proof. vm_refl. Qed.
Lemma D_65cb0 : decode_any W_65cb0 = Some (Op ALU_ADD 23 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cb4 : bv 32 := 0x002a9a93.
Lemma F_65cb4 : fetch_word Plain.M.loaded_segments (0x65cf4 : word) = Some W_65cb4.
Proof. vm_refl. Qed.
Lemma D_65cb4 : decode_any W_65cb4 = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cb8 : bv 32 := 0x415a04b3.
Lemma F_65cb8 : fetch_word Plain.M.loaded_segments (0x65cf8 : word) = Some W_65cb8.
Proof. vm_refl. Qed.
Lemma D_65cb8 : decode_any W_65cb8 = Some (Op ALU_SUB 9 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cbc : bv 32 := 0x00048513.
Lemma F_65cbc : fetch_word Plain.M.loaded_segments (0x65cfc : word) = Some W_65cbc.
Proof. vm_refl. Qed.
Lemma D_65cbc : decode_any W_65cbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cc0 : bv 32 := 0x00090593.
Lemma F_65cc0 : fetch_word Plain.M.loaded_segments (0x65d00 : word) = Some W_65cc0.
Proof. vm_refl. Qed.
Lemma D_65cc0 : decode_any W_65cc0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cc4 : bv 32 := 0x00098613.
Lemma F_65cc4 : fetch_word Plain.M.loaded_segments (0x65d04 : word) = Some W_65cc4.
Proof. vm_refl. Qed.
Lemma D_65cc4 : decode_any W_65cc4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cc8 : bv 32 := 0x13c7b0ef.
Lemma F_65cc8 : fetch_word Plain.M.loaded_segments (0x65d08 : word) = Some W_65cc8.
Proof. vm_refl. Qed.
Lemma D_65cc8 : decode_any W_65cc8 = Some (Jal 1 504124, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ccc : bv 32 := 0x00043503.
Lemma F_65ccc : fetch_word Plain.M.loaded_segments (0x65d0c : word) = Some W_65ccc.
Proof. vm_refl. Qed.
Lemma D_65ccc : decode_any W_65ccc = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cd0 : bv 32 := 0x01043583.
Lemma F_65cd0 : fetch_word Plain.M.loaded_segments (0x65d10 : word) = Some W_65cd0.
Proof. vm_refl. Qed.
Lemma D_65cd0 : decode_any W_65cd0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cd4 : bv 32 := 0x00943023.
Lemma F_65cd4 : fetch_word Plain.M.loaded_segments (0x65d14 : word) = Some W_65cd4.
Proof. vm_refl. Qed.
Lemma D_65cd4 : decode_any W_65cd4 = Some (Store SZ8 8 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cd8 : bv 32 := 0x01743423.
Lemma F_65cd8 : fetch_word Plain.M.loaded_segments (0x65d18 : word) = Some W_65cd8.
Proof. vm_refl. Qed.
Lemma D_65cd8 : decode_any W_65cd8 = Some (Store SZ8 8 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cdc : bv 32 := 0x01643823.
Lemma F_65cdc : fetch_word Plain.M.loaded_segments (0x65d1c : word) = Some W_65cdc.
Proof. vm_refl. Qed.
Lemma D_65cdc : decode_any W_65cdc = Some (Store SZ8 8 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ce0 : bv 32 := 0x00a13023.
Lemma F_65ce0 : fetch_word Plain.M.loaded_segments (0x65d20 : word) = Some W_65ce0.
Proof. vm_refl. Qed.
Lemma D_65ce0 : decode_any W_65ce0 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ce4 : bv 32 := 0x00a13423.
Lemma F_65ce4 : fetch_word Plain.M.loaded_segments (0x65d24 : word) = Some W_65ce4.
Proof. vm_refl. Qed.
Lemma D_65ce4 : decode_any W_65ce4 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ce8 : bv 32 := 0x00a13823.
Lemma F_65ce8 : fetch_word Plain.M.loaded_segments (0x65d28 : word) = Some W_65ce8.
Proof. vm_refl. Qed.
Lemma D_65ce8 : decode_any W_65ce8 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cec : bv 32 := 0x00b13c23.
Lemma F_65cec : fetch_word Plain.M.loaded_segments (0x65d2c : word) = Some W_65cec.
Proof. vm_refl. Qed.
Lemma D_65cec : decode_any W_65cec = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cf0 : bv 32 := 0x00010513.
Lemma F_65cf0 : fetch_word Plain.M.loaded_segments (0x65d30 : word) = Some W_65cf0.
Proof. vm_refl. Qed.
Lemma D_65cf0 : decode_any W_65cf0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cf4 : bv 32 := 0x034000ef.
Lemma F_65cf4 : fetch_word Plain.M.loaded_segments (0x65d34 : word) = Some W_65cf4.
Proof. vm_refl. Qed.
Lemma D_65cf4 : decode_any W_65cf4 = Some (Jal 1 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cf8 : bv 32 := 0x06813083.
Lemma F_65cf8 : fetch_word Plain.M.loaded_segments (0x65d38 : word) = Some W_65cf8.
Proof. vm_refl. Qed.
Lemma D_65cf8 : decode_any W_65cf8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_65cfc : bv 32 := 0x06013403.
Lemma F_65cfc : fetch_word Plain.M.loaded_segments (0x65d3c : word) = Some W_65cfc.
Proof. vm_refl. Qed.
Lemma D_65cfc : decode_any W_65cfc = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d00 : bv 32 := 0x05813483.
Lemma F_65d00 : fetch_word Plain.M.loaded_segments (0x65d40 : word) = Some W_65d00.
Proof. vm_refl. Qed.
Lemma D_65d00 : decode_any W_65d00 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d04 : bv 32 := 0x05013903.
Lemma F_65d04 : fetch_word Plain.M.loaded_segments (0x65d44 : word) = Some W_65d04.
Proof. vm_refl. Qed.
Lemma D_65d04 : decode_any W_65d04 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d08 : bv 32 := 0x04813983.
Lemma F_65d08 : fetch_word Plain.M.loaded_segments (0x65d48 : word) = Some W_65d08.
Proof. vm_refl. Qed.
Lemma D_65d08 : decode_any W_65d08 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d0c : bv 32 := 0x04013a03.
Lemma F_65d0c : fetch_word Plain.M.loaded_segments (0x65d4c : word) = Some W_65d0c.
Proof. vm_refl. Qed.
Lemma D_65d0c : decode_any W_65d0c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d10 : bv 32 := 0x03813a83.
Lemma F_65d10 : fetch_word Plain.M.loaded_segments (0x65d50 : word) = Some W_65d10.
Proof. vm_refl. Qed.
Lemma D_65d10 : decode_any W_65d10 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d14 : bv 32 := 0x03013b03.
Lemma F_65d14 : fetch_word Plain.M.loaded_segments (0x65d54 : word) = Some W_65d14.
Proof. vm_refl. Qed.
Lemma D_65d14 : decode_any W_65d14 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d18 : bv 32 := 0x02813b83.
Lemma F_65d18 : fetch_word Plain.M.loaded_segments (0x65d58 : word) = Some W_65d18.
Proof. vm_refl. Qed.
Lemma D_65d18 : decode_any W_65d18 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d1c : bv 32 := 0x07010113.
Lemma F_65d1c : fetch_word Plain.M.loaded_segments (0x65d5c : word) = Some W_65d1c.
Proof. vm_refl. Qed.
Lemma D_65d1c : decode_any W_65d1c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d20 : bv 32 := 0x00008067.
Lemma F_65d20 : fetch_word Plain.M.loaded_segments (0x65d60 : word) = Some W_65d20.
Proof. vm_refl. Qed.
Lemma D_65d20 : decode_any W_65d20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d28 : bv 32 := 0x00853603.
Lemma F_65d28 : fetch_word Plain.M.loaded_segments (0x65d68 : word) = Some W_65d28.
Proof. vm_refl. Qed.
Lemma D_65d28 : decode_any W_65d28 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d2c : bv 32 := 0x01053583.
Lemma F_65d2c : fetch_word Plain.M.loaded_segments (0x65d6c : word) = Some W_65d2c.
Proof. vm_refl. Qed.
Lemma D_65d2c : decode_any W_65d2c = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d30 : bv 32 := 0x00b60c63.
Lemma F_65d30 : fetch_word Plain.M.loaded_segments (0x65d70 : word) = Some W_65d30.
Proof. vm_refl. Qed.
Lemma D_65d30 : decode_any W_65d30 = Some (Branch BC_EQ 12 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d48 : bv 32 := 0x00053603.
Lemma F_65d48 : fetch_word Plain.M.loaded_segments (0x65d88 : word) = Some W_65d48.
Proof. vm_refl. Qed.
Lemma D_65d48 : decode_any W_65d48 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d4c : bv 32 := 0x00060a63.
Lemma F_65d4c : fetch_word Plain.M.loaded_segments (0x65d8c : word) = Some W_65d4c.
Proof. vm_refl. Qed.
Lemma D_65d4c : decode_any W_65d4c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_65d60 : bv 32 := 0x00008067.
Lemma F_65d60 : fetch_word Plain.M.loaded_segments (0x65da0 : word) = Some W_65d60.
Proof. vm_refl. Qed.
Lemma D_65d60 : decode_any W_65d60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_65b90_65d64.

Module S1_code_65e00_65e38.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65e00 : bv 32 := 0xff010113.
Lemma F_65e00 : fetch_word Plain.M.loaded_segments (0x65e40 : word) = Some W_65e00.
Proof. vm_refl. Qed.
Lemma D_65e00 : decode_any W_65e00 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e04 : bv 32 := 0x00113423.
Lemma F_65e04 : fetch_word Plain.M.loaded_segments (0x65e44 : word) = Some W_65e04.
Proof. vm_refl. Qed.
Lemma D_65e04 : decode_any W_65e04 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e08 : bv 32 := 0x00813023.
Lemma F_65e08 : fetch_word Plain.M.loaded_segments (0x65e48 : word) = Some W_65e08.
Proof. vm_refl. Qed.
Lemma D_65e08 : decode_any W_65e08 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e0c : bv 32 := 0x03e5d513.
Lemma F_65e0c : fetch_word Plain.M.loaded_segments (0x65e4c : word) = Some W_65e0c.
Proof. vm_refl. Qed.
Lemma D_65e0c : decode_any W_65e0c = Some (ShiftImm ALU_SRL 10 11 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e10 : bv 32 := 0x02051263.
Lemma F_65e10 : fetch_word Plain.M.loaded_segments (0x65e50 : word) = Some W_65e10.
Proof. vm_refl. Qed.
Lemma D_65e10 : decode_any W_65e10 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e14 : bv 32 := 0x00058413.
Lemma F_65e14 : fetch_word Plain.M.loaded_segments (0x65e54 : word) = Some W_65e14.
Proof. vm_refl. Qed.
Lemma D_65e14 : decode_any W_65e14 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e18 : bv 32 := 0x00259513.
Lemma F_65e18 : fetch_word Plain.M.loaded_segments (0x65e58 : word) = Some W_65e18.
Proof. vm_refl. Qed.
Lemma D_65e18 : decode_any W_65e18 = Some (ShiftImm ALU_SLL 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e1c : bv 32 := 0x7817f0ef.
Lemma F_65e1c : fetch_word Plain.M.loaded_segments (0x65e5c : word) = Some W_65e1c.
Proof. vm_refl. Qed.
Lemma D_65e1c : decode_any W_65e1c = Some (Jal 1 524160, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e20 : bv 32 := 0x00040593.
Lemma F_65e20 : fetch_word Plain.M.loaded_segments (0x65e60 : word) = Some W_65e20.
Proof. vm_refl. Qed.
Lemma D_65e20 : decode_any W_65e20 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e24 : bv 32 := 0x00813083.
Lemma F_65e24 : fetch_word Plain.M.loaded_segments (0x65e64 : word) = Some W_65e24.
Proof. vm_refl. Qed.
Lemma D_65e24 : decode_any W_65e24 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e28 : bv 32 := 0x00013403.
Lemma F_65e28 : fetch_word Plain.M.loaded_segments (0x65e68 : word) = Some W_65e28.
Proof. vm_refl. Qed.
Lemma D_65e28 : decode_any W_65e28 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e2c : bv 32 := 0x01010113.
Lemma F_65e2c : fetch_word Plain.M.loaded_segments (0x65e6c : word) = Some W_65e2c.
Proof. vm_refl. Qed.
Lemma D_65e2c : decode_any W_65e2c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e30 : bv 32 := 0x00008067.
Lemma F_65e30 : fetch_word Plain.M.loaded_segments (0x65e70 : word) = Some W_65e30.
Proof. vm_refl. Qed.
Lemma D_65e30 : decode_any W_65e30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_65e00_65e38.

Module Lib_Vec32_Resize.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemset OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.S1_code_65b90_65d64 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.S1_code_65e00_65e38.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac rdA H := peel; rdn_fix H.
Ltac b2z8 := apply bytes_le_to_Z_8.

Ltac rdW a' :=
  lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with a' by lia end;
  peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia.
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.

Section Resize.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition APP_vals (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 23%bv; getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Lemma prologue : forall (fx : FPState) R M sp ret v n,
    getr R 2%bv = Z_to_bv 64 sp -> getr R 1%bv = Z_to_bv 64 ret -> getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 n ->
    0 < n < 2 ^ 62 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    rdn SEGS M (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS M (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    store_ok SEGS M (Z_to_bv 64 (sp - 112)) 112 = true -> 112 <= sp < 2 ^ 63 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x65bd0) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd R 12%bv (Z_to_bv 64 0)) 13%bv (Z_to_bv 64 0))
                             13%bv (Z_to_bv 64 0)) 13%bv (Z_to_bv 64 0)) 11%bv (Z_to_bv 64 n)) 2%bv (Z_to_bv 64 (sp - 112))) 8%bv (Z_to_bv 64 v))
                          (Z_to_bv 64 0x65c2c) (wslots M sp (APP_vals R ret)) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret v n Hsp Hra Ha0 Ha1 Hn Hv0 Hv1 F0 F1 HOK Hsp'.
    norm_pc.
    ld_step F_65b90 D_65b90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0) ltac:(b2z8).
    ld_step F_65b94 D_65b94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F1) ltac:(b2z8).
    stepiv F_65b98 D_65b98 (Z_to_bv 64 0) ltac:(gres; reflexivity).
    stepiv F_65b9c D_65b9c (Z_to_bv 64 0) ltac:(gres; imm_norm; reflexivity).
    stepb_ft F_65ba0 D_65ba0 ltac:(rewrite Ha1; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    stepiv F_65ba4 D_65ba4 (Z_to_bv 64 n) ltac:(gres; rewrite Ha1; rewrite v_sub_Z by lia; f_equal; lia).
    stepj F_65ba8 D_65ba8.
    sv F_65bc0 D_65bc0 (Z_to_bv 64 (sp - 112)).
    stw F_65bc4 D_65bc4 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
    stw F_65bc8 D_65bc8 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
    stw F_65bcc D_65bcc (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
    stw F_65bd0 D_65bd0 (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
    stw F_65bd4 D_65bd4 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
    stw F_65bd8 D_65bd8 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
    stw F_65bdc D_65bdc (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
    stw F_65be0 D_65be0 (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
    stw F_65be4 D_65be4 (Z_to_bv 64 (sp - 72)) (getr R 23%bv) ltac:(ok_sub HOK).
    sv F_65be8 D_65be8 (Z_to_bv 64 v).
    lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
    f_equal. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma epilogue : forall (fx : FPState) R M sp ret (v8 v9 v18 v19 v20 v21 v22 v23 : word),
    getr R 2%bv = Z_to_bv 64 (sp - 112) -> 112 <= sp < 2 ^ 63 ->
    rdn SEGS M (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS M (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS M (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS M (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS M (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS M (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS M (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS M (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    rdn SEGS M (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    ret_ok (Z_to_bv 64 ret) ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x65d38) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                             1%bv (Z_to_bv 64 ret)) 8%bv v8) 9%bv v9) 18%bv v18) 19%bv v19) 20%bv v20) 21%bv v21) 22%bv v22) 23%bv v23)
                             2%bv (Z_to_bv 64 sp))
                          (Z_to_bv 64 ret) M (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret v8 v9 v18 v19 v20 v21 v22 v23 Hsp Hsp' L1 L8 L9 L18 L19 L20 L21 L22 L23 Hret.
    norm_pc.
    ld_step F_65cf8 D_65cf8 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdn_fix L1) ltac:(b2z8).
    ld_step F_65cfc D_65cfc (word_to_le_bytes 8 v8) v8 ltac:(rdn_fix L8) ltac:(b2z8).
    ld_step F_65d00 D_65d00 (word_to_le_bytes 8 v9) v9 ltac:(rdn_fix L9) ltac:(b2z8).
    ld_step F_65d04 D_65d04 (word_to_le_bytes 8 v18) v18 ltac:(rdn_fix L18) ltac:(b2z8).
    ld_step F_65d08 D_65d08 (word_to_le_bytes 8 v19) v19 ltac:(rdn_fix L19) ltac:(b2z8).
    ld_step F_65d0c D_65d0c (word_to_le_bytes 8 v20) v20 ltac:(rdn_fix L20) ltac:(b2z8).
    ld_step F_65d10 D_65d10 (word_to_le_bytes 8 v21) v21 ltac:(rdn_fix L21) ltac:(b2z8).
    ld_step F_65d14 D_65d14 (word_to_le_bytes 8 v22) v22 ltac:(rdn_fix L22) ltac:(b2z8).
    ld_step F_65d18 D_65d18 (word_to_le_bytes 8 v23) v23 ltac:(rdn_fix L23) ltac:(b2z8).
    sv F_65d1c D_65d1c (Z_to_bv 64 sp).
    stepjr F_65d20 D_65d20 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.

  Definition c65b2c : vec_consts := {| vc_entry := 0x65bd0; vc_stack := 128 |}.

  Theorem vec32_resize_65b2c_spec : vec32_resize_stmt SEGS Ly.L MI ST c65b2c.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret v n K.
    cbn [vc_entry vc_stack c65b2c]. lazy zeta.
    intros CB Ha0 Ha1 VEC OBJ Hn0 HNMAX ROOM CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2 & FE). clear Hb FE Hlen.
    change (Zlen (@nil Z)) with 0 in F1. rewrite Z.mul_0_r, Z.add_0_l in F1, F2.
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (128 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
    assert (Hn : 0 <= n < 2 ^ 40) by lia.
    destruct OBJ as [PLv WINv].
    assert (WINv' : v + 24 <= sp - (128 + (16 + MALLOC_STACK MI)) \/ sp <= v).
    { destruct (Z.lt_ge_cases v sp); [left|right; lia].
      destruct (Z.lt_ge_cases (v + 24) (sp - (128 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases v (sp - (128 + (16 + MALLOC_STACK MI)))).
      - apply (WINv (sp - (128 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINv v); unfold zwin; lia. }
    hide WINv'.
    assert (HDR : forall a, v <= a < v + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. exact (placed_sep A M model v 24 a AI PLv Ha). }
    assert (WIN : forall a, sp - (128 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (128 + (16 + MALLOC_STACK MI))) (128 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    unfold fld in F0, F1, F2.
    destruct (Z.eq_dec n 0) as [Hnz|Hnnz].
    -
      subst n.
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
      { norm_pc.
        ld_step F_65b90 D_65b90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0) ltac:(b2z8).
        ld_step F_65b94 D_65b94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F1) ltac:(b2z8).
        stepiv F_65b98 D_65b98 (Z_to_bv 64 0) ltac:(gres; reflexivity).
        stepiv F_65b9c D_65b9c (Z_to_bv 64 0) ltac:(gres; imm_norm; reflexivity).
        stepb_tk F_65ba0 D_65ba0 ltac:(rewrite Ha1; apply Z.ltb_irrefl).
        stepb_tk F_65bac D_65bac ltac:(rewrite Ha1; apply Z.ltb_irrefl).
        stepjr F_65bbc D_65bbc (Z_to_bv 64 ret) ltac:(gres; exact Hra).
        apply mst_refl. }
      cbn [Z.to_nat repeat].
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 ret) by (symmetry; exact Hret) end.
      eapply (CONT A _ M model 0).
      + constructor; [exact AI | exact MS | reflexivity | reflexivity | exact SXI |].
        intros r Hr. unfold callee_saved in Hr.
        repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
      + apply (vec32_nil MI); try assumption; try lia.
      + left. repeat split; reflexivity.
      + apply eff_refl.
    -
      set (M1 := wslots M sp (APP_vals R ret)).
      assert (ST1 : stores_in (zwin (sp - 72) sp) M M1).
      { unfold M1. apply (wslots_stores_in M sp (APP_vals R ret)); unfold Zlen; cbn; lia. }
      assert (AG1 : forall lo hi, (hi <= sp - 128 \/ sp <= lo) -> 0 <= lo -> hi < 2 ^ 64 -> agree_on (zwin lo hi) M M1).
      { intros lo hi Hd Hlo Hhi. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *. lia. }
      assert (F0' : rdn SEGS M1 (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
      { change (fld SEGS M1 v 8 0). eapply fld_agree; [lia| cbn; lia | exact F0 |]. apply AG1; cbn; unhide WINv'; lia. }
      assert (F1' : rdn SEGS M1 (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
      { change (fld SEGS M1 (v + 8) 8 0). eapply fld_agree; [lia| cbn; lia | exact F1 |]. apply AG1; cbn; unhide WINv'; lia. }
      assert (F2' : rdn SEGS M1 (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
      { change (fld SEGS M1 (v + 16) 8 0). eapply fld_agree; [lia| cbn; lia | exact F2 |]. apply AG1; cbn; unhide WINv'; lia. }
      assert (SL : forall k, 1 <= k <= 9 ->
                rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
                = Some (word_to_le_bytes 8 (nth (Z.to_nat (9 - k)) (APP_vals R ret) (Z_to_bv 64 0)))).
      { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
      slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. slotv SL 5 SL5.
      slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. slotv SL 9 SL9. clear SL.
      assert (HD1 : mdef M1 (sp - (128 + (16 + MALLOC_STACK MI))) (128 + (16 + MALLOC_STACK MI))) by (eapply stores_in_mdef; [exact ST1 | exact HDW]).
      set (R1 := regupd (regupd (regupd (regupd (regupd (regupd (regupd R 12%bv (Z_to_bv 64 0)) 13%bv (Z_to_bv 64 0))
                             13%bv (Z_to_bv 64 0)) 13%bv (Z_to_bv 64 0)) 11%bv (Z_to_bv 64 n)) 2%bv (Z_to_bv 64 (sp - 112))) 8%bv (Z_to_bv 64 v)).
      set (M2 := wbytes (wbytes (wbytes M1 (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 (Z_to_bv 64 v)))
                                (Z_to_bv 64 (sp - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0x65c90)))
                         (Z_to_bv 64 (sp - 128)) (word_to_le_bytes 8 (Z_to_bv 64 v))).
      assert (ST12 : stores_in (zwin (sp - 128) sp) M1 M2).
      { unfold M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes| | |] | | |];
          rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin; lia. }
      assert (ST2 : stores_in (zwin (sp - 128) sp) M M2).
      { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST1|] | exact ST12]. intros a Ha; unfold zwin in *; lia. }

      assert (BA : exists Rn,
        msteps SEGS (@mkst fx R1 (Z_to_bv 64 0x65c2c) M1 (seg_rom SEGS))
                    (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) M2 (seg_rom SEGS))
        /\ getr Rn 10%bv = Z_to_bv 64 (4 * n) /\ getr Rn 1%bv = Z_to_bv 64 0x65e60
        /\ getr Rn 2%bv = Z_to_bv 64 (sp - 128) /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
        /\ getr Rn 8%bv = Z_to_bv 64 n /\ getr Rn 9%bv = Z_to_bv 64 n /\ getr Rn 20%bv = Z_to_bv 64 0
        /\ (forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r)).
      { eexists. split.
        - unfold R1. norm_pc.
          ld_step F_65bec D_65bec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F1') ltac:(b2z8).
          ld_step F_65bf0 D_65bf0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F2') ltac:(b2z8).
          stepiv F_65bf4 D_65bf4 (Z_to_bv 64 0) ltac:(gres; reflexivity).
          stepiv F_65bf8 D_65bf8 (Z_to_bv 64 0) ltac:(gres; imm_norm; reflexivity).
          sv F_65bfc D_65bfc (Z_to_bv 64 n).
          stepb_ft F_65c00 D_65c00 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          ld_step F_65c04 D_65c04 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0') ltac:(b2z8).
          stepiv F_65c08 D_65c08 (Z_to_bv 64 0) ltac:(gres; reflexivity).
          stepiv F_65c0c D_65c0c (Z_to_bv 64 0) ltac:(gres; imm_norm; reflexivity).
          stepiv F_65c10 D_65c10 (Z_to_bv 64 n) ltac:(gres; rewrite v_add_Z by lia; f_equal; lia).
          stepiv F_65c14 D_65c14 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
          stepb_ft F_65c18 D_65c18 ltac:(apply c_eq_refl).
          stepiv F_65c1c D_65c1c (Z_to_bv 64 0) ltac:(gres; reflexivity).
          stepiv F_65c20 D_65c20 (Z_to_bv 64 0) ltac:(gres; imm_norm; reflexivity).
          stepb_ft F_65c24 D_65c24 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          sv F_65c28 D_65c28 (Z_to_bv 64 n).
          stepiv F_65c2c D_65c2c (Z_to_bv 64 (2 ^ 64 - 7)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepiv F_65c30 D_65c30 (Z_to_bv 64 0x7ffffffffffffffc) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepb_tk F_65c34 D_65c34 ltac:(rewrite c_ltu_Z by lia; reflexivity).
          stw F_65c40 D_65c40 (Z_to_bv 64 (sp - 80)) (Z_to_bv 64 v) ltac:(ok_mdef HD1).
          stepb_ft F_65c44 D_65c44 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_65c48 D_65c48 (Z_to_bv 64 v).
          stepj F_65c4c D_65c4c.
          sv F_65e00 D_65e00 (Z_to_bv 64 (sp - 128)).
          stw F_65e04 D_65e04 (Z_to_bv 64 (sp - 120)) (Z_to_bv 64 0x65c90) ltac:(ok_mdef HD1).
          stw F_65e08 D_65e08 (Z_to_bv 64 (sp - 128)) (Z_to_bv 64 v) ltac:(ok_mdef HD1).
          stepiv F_65e0c D_65e0c (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
          stepb_ft F_65e10 D_65e10 ltac:(apply c_eq_refl).
          sv F_65e14 D_65e14 (Z_to_bv 64 n).
          stepiv F_65e18 D_65e18 (Z_to_bv 64 (4 * n)) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
          stepj F_65e1c D_65e1c.
          lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
          f_equal. apply bv_eq; vm_compute; reflexivity.
        - gres. repeat split; try reflexivity; try assumption.
          intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
      destruct BA as (Rn & RUNA & Rn10 & Rn1 & Rn2 & Rn3 & Rn4 & Rn8 & Rn9 & Rn20 & RnS).

      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
      { eapply msteps_trans; [apply (prologue fx R M sp ret v n Hsp Hra Ha0 Ha1); try assumption; try lia; ok_sub HOK|].
        fold M1. unfold R1 in RUNA. exact RUNA. }
      eapply (NEW fx A s Rn M2 model (4 * n) (sp - 128) 0x65e60 K).
      + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST2 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
      + exact MS.
      + eapply (roc_stores Ly.L); [exact ROC | exact ST2 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
      + eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST2 |].
        intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
      + exact SXH.
      + constructor.
        * exact Rn1.
        * unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
        * lia.
        * exact Rn2.
        * replace (sp - 128) with (sp - 16 * 8) by lia. apply mod16_sub. exact Hsp16.
        * lia.
        * rewrite Rn3. exact Hgp.
        * rewrite Rn4. exact Htp.
      + exact Rn10.
      + lia.
      + lia.
      + unfold stack_room. replace (sp - 128 - (16 + MALLOC_STACK MI)) with (sp - (128 + (16 + MALLOC_STACK MI))) by lia.
        apply (mdef_store_ok SEGS M2 _ (128 + (16 + MALLOC_STACK MI))); [eapply stores_in_mdef; [exact ST2 | exact HDW] | lia | lia | lia].
      + intros a Ha. apply Hwin. unfold zwin in *. lia.
      + exact Hown_sx.
      + exact Herr_sx.
      + rewrite new_size_id by lia. eapply (roomL_room_for SEGS Ly.L MI); [exact AI | lia | exact (ROOM ltac:(lia))].
      +
        intros A1 R2 M3 model1 p AI1 MS1 Hfs1 Hfds1 SX1 KEPT2 R2a0 Hp LADD CAPS1 BIGC1 NEWT1 FR1 DEF1.
        rewrite new_size_id in LADD, FR1 by lia.
        assert (ROC1 : img_ro_clear Ly.L M2).
        { eapply (roc_stores Ly.L); [exact ROC | exact ST2 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))). }
        assert (ROC2 : img_ro_clear Ly.L M3).
        { eapply (roc_frame Ly.L); [exact ROC1 | exact FR1 |]. intros a [Ho|[Hblk|[Hw|He]]].
          - exact (roc_owned SEGS Ly.L MI A1 M3 model1 a AI1 Ho).
          - right. eapply (live_offimg SEGS Ly.L MI); [exact AI1 | apply (live_add_new _ _ _ _ LADD) | exact Hblk].
          - right. apply (proj2 (stack_sep A1 M3 model1 a AI1 ltac:(unfold zwin in Hw; lia))).
          - left. apply ly_errno_rw. exact He. }
        assert (HinP : In (p, 4 * n) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
        destruct (live_range SEGS Ly.L MI A1 M3 model1 p (4 * n) AI1 HinP) as (_ & Hpal & _ & Hpce).
        assert (HDp : mdef M3 p (4 * n)) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
        assert (Hpown : forall a, p <= a < p + 4 * n -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
        assert (PLv1 : placed MI A1 v 24).
        { eapply (placed_mono SEGS Ly.L MI); [|exact PLv]. intros blk Hblk; eapply live_add_keeps; eassumption. }
        assert (HDRp : v + 24 <= p \/ p + 4 * n <= v).
        { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M3 model model1 v 24 p (4 * n) AI AI1 PLv LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
        hide HDRp.
        assert (WIN1 : forall a, sp - (128 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. apply (stack_sep A1 M3 model1 a AI1). lia. }
        assert (HDR1 : forall a, v <= a < v + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. exact (placed_sep A1 M3 model1 v 24 a AI1 PLv1 Ha). }

        assert (PRES2 : forall a, (sp - 128 <= a < sp) \/ (v <= a < v + 24) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros a Ha.
          assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha; lia).
          apply FR1. rewrite u64_of_Z by lia. intros [Ho|[Hblk|[Hw|He]]].
          - destruct Ha as [H|H]; [exact (proj1 (WIN1 a ltac:(lia)) Ho) | exact (proj1 (HDR1 a H) Ho)].
          - destruct Ha as [H|H]; [lia | unhide HDRp; lia].
          - unfold zwin in Hw. destruct Ha as [H|H]; [lia | unhide WINv'; lia].
          - pose proof (ly_errno_img a He) as Hi. rewrite ly_img_iff in Hi.
            destruct Ha as [H|H].
            + pose proof (proj2 (WIN1 a ltac:(lia))) as X. rewrite ly_img_iff in X. lia.
            + pose proof (proj2 (HDR1 a H)) as X. rewrite ly_img_iff in X. lia. }
        assert (AG23 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                 ((sp - 128 <= lo /\ hi <= sp) \/ (v <= lo /\ hi <= v + 24)) -> agree_on (zwin lo hi) M2 M3).
        { intros lo hi Hlo Hhi Hc a Ha. apply PRES2. unfold zwin in Ha. clear -Hc Ha. destruct Hc as [H|H]; [left|right]; lia. }
        assert (AG12 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= sp - 128 \/ sp - 72 <= lo) -> agree_on (zwin lo hi) M1 M2).
        { intros lo hi Hlo Hhi Hc. eapply stores_in_agree.
          - unfold M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes with (W := zwin (sp - 128) (sp - 72))| | |] | | |];
              rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin; lia.
          - intros a Ha. unfold zwin in *. lia. }

        assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 128)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
        assert (R2_8 : getr R2 8%bv = Z_to_bv 64 n) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
        assert (R2_9 : getr R2 9%bv = Z_to_bv 64 n) by (rewrite (KEPT2 9%bv) by in_cs; exact Rn9).
        assert (R2_20 : getr R2 20%bv = Z_to_bv 64 0) by (rewrite (KEPT2 20%bv) by in_cs; exact Rn20).

        assert (Q120 : rdn SEGS M3 (Z_to_bv 64 (sp - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65c90))).
        { rewrite (rdn_agree_win SEGS M2 M3); [| lia | cbn; lia | apply AG23; cbn; lia].
          unfold M2. peel. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
        assert (Q128 : rdn SEGS M3 (Z_to_bv 64 (sp - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v))).
        { rewrite (rdn_agree_win SEGS M2 M3); [| lia | cbn; lia | apply AG23; cbn; lia].
          unfold M2. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
        assert (F0'' : rdn SEGS M3 (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { rewrite (rdn_agree_win SEGS M2 M3); [| lia | cbn; lia | apply AG23; cbn; lia].
          rewrite (rdn_agree_win SEGS M1 M2); [exact F0' | lia | cbn; lia | apply AG12; cbn; unhide WINv'; lia]. }
        assert (F1'' : rdn SEGS M3 (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { rewrite (rdn_agree_win SEGS M2 M3); [| lia | cbn; lia | apply AG23; cbn; lia].
          rewrite (rdn_agree_win SEGS M1 M2); [exact F1' | lia | cbn; lia | apply AG12; cbn; unhide WINv'; lia]. }
        assert (F2'' : rdn SEGS M3 (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { rewrite (rdn_agree_win SEGS M2 M3); [| lia | cbn; lia | apply AG23; cbn; lia].
          rewrite (rdn_agree_win SEGS M1 M2); [exact F2' | lia | cbn; lia | apply AG12; cbn; unhide WINv'; lia]. }
        assert (HDv3 : mdef M3 v 24).
        { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST2 | exact HDv] | lia | lia |].
          intros a Ha [Ho|He]; [exact (proj1 (HDR a ltac:(lia)) Ho) | exact (proj2 (HDR a ltac:(lia)) (ly_errno_img a He))]. }
        assert (HDW3 : mdef M3 (sp - (128 + (16 + MALLOC_STACK MI))) (128 + (16 + MALLOC_STACK MI))).
        { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST2 | exact HDW] | lia | lia |].
          intros a Ha [Ho|He]; [exact (proj1 (WIN a ltac:(lia)) Ho) | exact (proj2 (WIN a ltac:(lia)) (ly_errno_img a He))]. }

        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc.
          sv F_65e20 D_65e20 (Z_to_bv 64 n).
          ld_step F_65e24 D_65e24 (word_to_le_bytes 8 (Z_to_bv 64 0x65c90)) (Z_to_bv 64 0x65c90) ltac:(rdn_fix Q120) ltac:(b2z8).
          ld_step F_65e28 D_65e28 (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 64 v) ltac:(rdn_fix Q128) ltac:(b2z8).
          sv F_65e2c D_65e2c (Z_to_bv 64 (sp - 112)).
          stepjr F_65e30 D_65e30 (Z_to_bv 64 0x65c90) ltac:(gres; reflexivity).
          change (v_jalr (Z_to_bv 64 0x65c90) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 0x65c90). norm_pc.
          ld_step F_65c50 D_65c50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0'') ltac:(b2z8).
          ld_step F_65c54 D_65c54 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F1'') ltac:(b2z8).
          stepiv F_65c58 D_65c58 (Z_to_bv 64 0) ltac:(gres; reflexivity).
          stepiv F_65c5c D_65c5c (Z_to_bv 64 0) ltac:(gres; imm_norm; reflexivity).
          stepj F_65c60 D_65c60.
          stepiv F_65c90 D_65c90 (Z_to_bv 64 p) ltac:(gres; rewrite R2a0, R2_20; rewrite v_add_Z by lia; f_equal; lia).
          stepiv F_65c94 D_65c94 (Z_to_bv 64 (4 * n)) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
          stepiv F_65c98 D_65c98 (Z_to_bv 64 (p + 4 * n)) ltac:(gres; rewrite R2a0; rewrite v_add_Z by lia; reflexivity).
          stepiv F_65c9c D_65c9c (Z_to_bv 64 (4 * n)) ltac:(gres; rewrite R2_9; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
          sv F_65ca0 D_65ca0 (Z_to_bv 64 p).
          sv F_65ca4 D_65ca4 (Z_to_bv 64 0).
          sv F_65ca8 D_65ca8 (Z_to_bv 64 (4 * n)).
          stepj F_65cac D_65cac.
          apply mst_refl. }

        lazymatch goal with |- srealizes _ (mkCfg (mkst ?r _ _ _) _) _ => set (R3 := r) end.
        destruct (s1_memset M3 (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0x65cf0) (4 * n) (seg_rom SEGS) R3
                    ltac:(lia) ltac:(rewrite u64_of_Z by lia; lia)
                    ltac:(apply (mdef_store_ok SEGS M3 p (4 * n)); try lia; exact HDp)
                    ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; reflexivity)
                    ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; apply bv_eq; vm_compute; reflexivity))
          as (R4 & RUN4 & R4a0 & AGR4).
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with s1_memset_entry by (apply bv_eq; vm_compute; reflexivity) end.
          exact RUN4. }
        rewrite cbyte_zero.
        set (M4 := wbytes M3 (Z_to_bv 64 p) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * n)))) in *.
        assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 112)) by (rewrite (ms_agree_getr _ _ 2%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_8 : getr R4 8%bv = Z_to_bv 64 v) by (rewrite (ms_agree_getr _ _ 8%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_9 : getr R4 9%bv = Z_to_bv 64 (4 * n)) by (rewrite (ms_agree_getr _ _ 9%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_18 : getr R4 18%bv = Z_to_bv 64 0) by (rewrite (ms_agree_getr _ _ 18%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_19 : getr R4 19%bv = Z_to_bv 64 0) by (rewrite (ms_agree_getr _ _ 19%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_20 : getr R4 20%bv = Z_to_bv 64 p) by (rewrite (ms_agree_getr _ _ 20%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_21 : getr R4 21%bv = Z_to_bv 64 0) by (rewrite (ms_agree_getr _ _ 21%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_22 : getr R4 22%bv = Z_to_bv 64 (p + 4 * n)) by (rewrite (ms_agree_getr _ _ 22%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; reflexivity).
        assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (ms_agree_getr _ _ 3%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; rewrite (KEPT2 3%bv) by in_cs; exact Rn3).
        assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (ms_agree_getr _ _ 4%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; rewrite (KEPT2 4%bv) by in_cs; exact Rn4).
        assert (R4S : forall r, In r [23; 24; 25; 26; 27]%bv -> getr R4 r = getr R r).
        { intros r Hr. pose proof Hr as Hr'.
          repeat (destruct Hr as [<-|Hr]; [rewrite (ms_agree_getr _ _ _ AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R3; gres; rewrite (KEPT2 _) by in_cs; apply RnS; (first [solve [clear; cbv; tauto] | cbv; tauto]) |]). destruct Hr. }

        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc.
          stepiv F_65cb0 D_65cb0 (Z_to_bv 64 (p + 4 * n)) ltac:(gres; rewrite R4_20, R4_9; rewrite v_add_Z by lia; reflexivity).
          stepiv F_65cb4 D_65cb4 (Z_to_bv 64 0) ltac:(gres; rewrite R4_21; imm_norm; reflexivity).
          stepiv F_65cb8 D_65cb8 (Z_to_bv 64 p) ltac:(gres; rewrite R4_20; rewrite v_sub_Z by lia; f_equal; lia).
          sv F_65cbc D_65cbc (Z_to_bv 64 p).
          sv F_65cc0 D_65cc0 (Z_to_bv 64 0).
          sv F_65cc4 D_65cc4 (Z_to_bv 64 0).
          stepj F_65cc8 D_65cc8.
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst ?r _ _ _) _) _ => set (R5 := r) end.
        assert (MC : mcH SEGS M4 (Z_to_bv 64 p) (Z_to_bv 64 0) 0 []).
        { constructor; [lia | reflexivity | reflexivity | reflexivity | rewrite !u64_of_Z by lia; right; lia | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; lia]. }
        destruct (s1_memcpy M4 (Z_to_bv 64 p) (Z_to_bv 64 0) 0 [] (seg_rom SEGS) R5 (Z_to_bv 64 0x65d0c)
                    MC ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R5; gres; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R5; gres; reflexivity) ltac:(unfold R5; gres; reflexivity) ltac:(unfold R5; gres; reflexivity))
          as (R6 & RUN6 & KEEP6).
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with s1_memcpy_entry by (apply bv_eq; vm_compute; reflexivity) end.
          exact RUN6. }
        change (wbytes M4 (Z_to_bv 64 p) []) with M4.
        assert (R6_2 : getr R6 2%bv = Z_to_bv 64 (sp - 112)) by (rewrite (KEEP6 2%bv) by in_cs; unfold R5; gres; exact R4_2).
        assert (R6_8 : getr R6 8%bv = Z_to_bv 64 v) by (rewrite (KEEP6 8%bv) by in_cs; unfold R5; gres; exact R4_8).
        assert (R6_9 : getr R6 9%bv = Z_to_bv 64 p) by (rewrite (KEEP6 9%bv) by in_cs; unfold R5; gres; reflexivity).
        assert (R6_22 : getr R6 22%bv = Z_to_bv 64 (p + 4 * n)) by (rewrite (KEEP6 22%bv) by in_cs; unfold R5; gres; exact R4_22).
        assert (R6_23 : getr R6 23%bv = Z_to_bv 64 (p + 4 * n)) by (rewrite (KEEP6 23%bv) by in_cs; unfold R5; gres; reflexivity).
        assert (R6_3 : getr R6 3%bv = getr R 3%bv) by (rewrite (KEEP6 3%bv) by in_cs; unfold R5; gres; exact R4_3).
        assert (R6_4 : getr R6 4%bv = getr R 4%bv) by (rewrite (KEEP6 4%bv) by in_cs; unfold R5; gres; exact R4_4).
        assert (R6S : forall r, In r [24; 25; 26; 27]%bv -> getr R6 r = getr R r).
        { intros r Hr. pose proof Hr as Hr'.
          repeat (destruct Hr as [<-|Hr]; [rewrite (KEEP6 _) by in_cs; unfold R5; gres; apply R4S; (first [solve [clear; cbv; tauto] | cbv; tauto]) |]). destruct Hr. }

        unhide HDRp.
        assert (AG34 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= p \/ p + 4 * n <= lo) -> agree_on (zwin lo hi) M3 M4).
        { intros lo hi H1 H2 H3. eapply stores_in_agree; [unfold M4; apply stores_in_wbytes with (W := zwin p (p + 4 * n)); rewrite ?repeat_length; try lia; intros a Ha; unfold zwin; lia|].
          intros a Ha. unfold zwin in *. lia. }
        assert (G0 : rdn SEGS M4 (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { rewrite (rdn_agree_win SEGS M3 M4); [exact F0'' | lia | cbn; lia | apply AG34; cbn; lia]. }
        assert (G2 : rdn SEGS M4 (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { rewrite (rdn_agree_win SEGS M3 M4); [exact F2'' | lia | cbn; lia | apply AG34; cbn; lia]. }
        assert (HDv4 : mdef M4 v 24) by (unfold M4; apply mdef_wbytes; exact HDv3).
        assert (HDW4 : mdef M4 (sp - (128 + (16 + MALLOC_STACK MI))) (128 + (16 + MALLOC_STACK MI))) by (unfold M4; apply mdef_wbytes; exact HDW3).
        set (M6 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M4
                     (Z_to_bv 64 v) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                     (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n))))
                     (Z_to_bv 64 (v + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n))))
                     (Z_to_bv 64 (sp - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                     (Z_to_bv 64 (sp - 104)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                     (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                     (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
        assert (ST46 : stores_in (fun a => zwin v (v + 24) a \/ zwin (sp - 112) (sp - 80) a) M4 M6).
        { unfold M6.
          eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more;
           [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes| | |] | | |] | | |] | | |] | | |] | | |];
            rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin; lia. }

        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc.
          ld_step F_65ccc D_65ccc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix G0) ltac:(b2z8).
          ld_step F_65cd0 D_65cd0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix G2) ltac:(b2z8).
          stw F_65cd4 D_65cd4 (Z_to_bv 64 v) (Z_to_bv 64 p) ltac:(ok_mdef HDv4).
          stw F_65cd8 D_65cd8 (Z_to_bv 64 (v + 8)) (Z_to_bv 64 (p + 4 * n)) ltac:(ok_mdef HDv4).
          stw F_65cdc D_65cdc (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (p + 4 * n)) ltac:(ok_mdef HDv4).
          stw F_65ce0 D_65ce0 (Z_to_bv 64 (sp - 112)) (Z_to_bv 64 0) ltac:(ok_mdef HDW4).
          stw F_65ce4 D_65ce4 (Z_to_bv 64 (sp - 104)) (Z_to_bv 64 0) ltac:(ok_mdef HDW4).
          stw F_65ce8 D_65ce8 (Z_to_bv 64 (sp - 96)) (Z_to_bv 64 0) ltac:(ok_mdef HDW4).
          stw F_65cec D_65cec (Z_to_bv 64 (sp - 88)) (Z_to_bv 64 0) ltac:(ok_mdef HDW4).
          sv F_65cf0 D_65cf0 (Z_to_bv 64 (sp - 112)).
          stepj F_65cf4 D_65cf4.
          ld_step F_65d28 D_65d28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdW (sp - 104)) ltac:(b2z8).
          ld_step F_65d2c D_65d2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdW (sp - 96)) ltac:(b2z8).
          stepb_tk F_65d30 D_65d30 ltac:(apply c_eq_refl).
          ld_step F_65d48 D_65d48 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdW (sp - 112)) ltac:(b2z8).
          stepb_tk F_65d4c D_65d4c ltac:(apply c_eq_refl).
          stepjr F_65d60 D_65d60 (Z_to_bv 64 0x65d38) ltac:(gres; reflexivity).
          change (v_jalr (Z_to_bv 64 0x65d38) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 0x65d38).
          apply mst_refl. }
        fold M6.

        assert (AG46 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= v \/ v + 24 <= lo) -> (hi <= sp - 112 \/ sp - 80 <= lo) -> agree_on (zwin lo hi) M4 M6).
        { intros lo hi H1 H2 H3 H4. eapply stores_in_agree; [exact ST46|]. intros a Ha. unfold zwin in *. lia. }
        assert (SLT : forall a vv, sp - 72 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some vv).
        { intros a vv H1 H2 H3.
          rewrite (rdn_agree_win SEGS M4 M6); [| lia | cbn; lia | apply AG46; cbn; unhide WINv'; lia].
          rewrite (rdn_agree_win SEGS M3 M4); [| lia | cbn; lia | apply AG34; cbn; lia].
          rewrite (rdn_agree_win SEGS M2 M3); [| lia | cbn; lia | apply AG23; cbn; lia].
          rewrite (rdn_agree_win SEGS M1 M2); [exact H3 | lia | cbn; lia | apply AG12; cbn; lia]. }
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 0x65d38) by (apply bv_eq; vm_compute; reflexivity) end.
          apply (epilogue fx _ M6 sp ret (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv) (getr R 23%bv));
            [ gres; exact R6_2 | lia
            | apply SLT; [lia|lia|rdn_fix SL1] | apply SLT; [lia|lia|rdn_fix SL2] | apply SLT; [lia|lia|rdn_fix SL3]
            | apply SLT; [lia|lia|rdn_fix SL4] | apply SLT; [lia|lia|rdn_fix SL5] | apply SLT; [lia|lia|rdn_fix SL6]
            | apply SLT; [lia|lia|rdn_fix SL7] | apply SLT; [lia|lia|rdn_fix SL8] | apply SLT; [lia|lia|rdn_fix SL9]
            | exact Hret ]. }

        assert (ST34 : stores_in (zwin p (p + 4 * n)) M3 M4).
        { unfold M4. apply stores_in_wbytes; rewrite ?repeat_length; try lia. intros a Ha; unfold zwin; lia. }
        assert (ST36 : stores_in (fun a => zwin p (p + 4 * n) a \/ (zwin v (v + 24) a \/ zwin (sp - 112) (sp - 80) a)) M3 M6).
        { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST34|] | eapply stores_in_weaken; [exact ST46|]];
            intros a Ha; [left; exact Ha | right; exact Ha]. }
        eapply (CONT A1 _ M6 model1 p).
        * constructor.
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST36 |].
             intros a [Ha|[Ha|Ha]]; [apply Hpown | apply HDR1 | apply WIN1]; unfold zwin in Ha; lia.
          -- exact MS1.
          -- exact Hfs1.
          -- exact Hfds1.
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST36 |].
             intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x122000)] a)
                  by (destruct Ha as [Ha|[Ha|Ha]]; [apply Hpown | apply HDR1 | apply WIN1]; unfold zwin in Ha; lia).
                destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
          -- intros r Hr; unfold callee_saved in Hr.
             repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | rewrite ?R6_3, ?R6_4; reflexivity | apply R6S; in_cs ] |]).
             destruct Hr.
        *
          unfold CRep.vec32. rewrite Zlen_repeat by lia.
          split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact ST46|exact HDv4]|].
          split; [lia|].
          split. { right. split; [lia|]. split; [exact Hpal|]. split; [lia|]. split; [lia|]. split; [exact HinP | lia]. }
          split. { unfold fld, M6. do 6 (rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; unhide WINv'; lia)).
                   apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
          split. { unfold fld, M6. do 5 (rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; unhide WINv'; lia)).
                   apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
          split. { unfold fld, M6. do 4 (rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; unhide WINv'; lia)).
                   apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
          intros i Hi. rewrite Znth_repeat by lia. split; [lia|].
          unfold fld. rewrite (rdn_agree_win SEGS M4 M6); [| lia | cbn; lia | apply AG46; cbn; lia].
          unfold M4. rewrite w4_zero. apply rdn_zeros_sub; lia.
        * right. split; [lia|]. cbn. exists (live MI A1). split; [exact LADD | reflexivity].
        *
          set (W := (sp - (128 + (16 + MALLOC_STACK MI)), sp)).
          set (FT := fun a => zwin v (v + 24) a \/ (0 < n /\ zwin p (p + 4 * n) a)).
          change (eff MI A A1 M M6 W FT).
          eapply eff_weaken.
          -- eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of, W in Ha; cbn in Ha; lia].
             ++ eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of, W in Ha; cbn in Ha; lia].
                ** apply (eff_store MI A M M2 W FT); [| exact (proj2 ST2)].
                   intros a HF HW. apply (proj1 ST2). intros Hz. apply HW. unfold W_of, W, zwin in *. cbn. lia.
                ** eapply (eff_of_new MI A A1 M2 M3 model1 W FT p (4 * n)); try eassumption.
                   --- intros a Ha. unfold W_of, W, zwin in *. cbn. lia.
                   --- intros a Ha. unfold FT. right. split; [lia|]. unfold zwin. lia.
             ++ apply (eff_store MI A1 M3 M6 W FT); [| exact (proj2 ST36)].
                intros a HF HW. apply (proj1 ST36). intros [Hz|[Hz|Hz]].
                ** apply HF. unfold FT. right. split; [lia | exact Hz].
                ** apply HF. unfold FT. left. exact Hz.
                ** apply HW. unfold W_of, W, zwin in *. cbn. lia.
          -- intros a [[H|H]|H]; exact H.
  Qed.
End Resize.
End Lib_Vec32_Resize.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Ctx.
From Stdlib Require Permutation.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_65a48_65b90.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65b40 : bv 32 := 0x40a585b3.

Definition W_65b44 : bv 32 := 0x7f1070ef.

Definition W_65b64 : bv 32 := 0x00008067.
Lemma F_65b64 : fetch_word Plain.M.loaded_segments (0x65ba4 : word) = Some W_65b64.
Proof. vm_refl. Qed.
Lemma D_65b64 : decode_any W_65b64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_65a48_65b90.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module TopS1A.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.DrvLibContract.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Ctx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.S1_code_65a48_65b90.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition STOPS : list Z :=
  [0x6c080; 0x6c1a0; 0x65eac; 0x65bd0; 0x660f8; 0x65f04; 0x6db74;
   T_LOOP; T_AFTER; T_EXIT; 0x65ba4].

Section Part.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Variables (cR : rg_consts) (cC : ctx_consts) (cV : vec_consts) (kc : prs_consts).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp ret p n : Z) (payload : list byte) (K : TSet).
  Variable C : topC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K.
  #[local] Ltac ctx := topctx_pose C.
  #[local] Ltac in_sub Hr := revert Hr; clear; intros Hr; cbn in Hr; decompose [or] Hr; try contradiction; subst; inl.
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation sp' := (sp - TOP_FRAME).
  #[local] Abbreviation W := (sp - LIB_STACK, sp).
  #[local] Abbreviation J := (J MI A0).
  #[local] Abbreviation FJW := (FJW MI A0 sp).
  #[local] Abbreviation tinv := (tinv MI ST A0 s R0 M0 model0 sp ret).
  #[local] Abbreviation tregs := (tregs R0 sp).
  #[local] Abbreviation tframe := (tframe R0 sp ret).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation live_facts' := (live_facts Ly.L MI).
  #[local] Abbreviation win_unowned' := (win_unowned C).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff Ly.L MI ly_img_low ly_rw_img ly_errno_rw).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff Ly.L MI ly_rw_img ly_errno_rw).
  #[local] Abbreviation defined_via_eff' := (defined_via_eff Ly.L MI ly_img_low ly_rw_img ly_errno_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_rw_not_relro ly_errno_rw).

  Lemma st_exit : forall (fx' : FPState) A M model R,
    tinv A M model -> tregs R -> frm_zero (@fp_csr fx') ->
    (forall q k, In (q, k) (live MI A) <-> In (q, k) (live MI A0)) ->
    srealizes SEGS (cfg fx' R T_EXIT M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros fx' A M model R TI TR FZ HL.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR]. destruct FR as (F1 & F2 & F3 & F4).
    destruct TR as (Q2 & Q3 & Q4 & Qs). pose proof CR as CR'. destruct CR' as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
    pose proof (u64_range (getr R0 8%bv)) as Hr8. pose proof (u64_range (getr R0 9%bv)) as Hr9. pose proof (u64_range (getr R0 18%bv)) as Hr18.
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KWord (SA (EVar 32) 2568) (N.to_nat 8) (EVar 33); KWord (SA (EVar 32) 2560) (N.to_nat 8) (EVar 34);
                                   KWord (SA (EVar 32) 2552) (N.to_nat 8) (EVar 35); KWord (SA (EVar 32) 2544) (N.to_nat 8) (EVar 36)]).
    { repeat apply Forall_cons; try apply Forall_nil;
        (eapply kword_var; [eassumption | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite ?Z_to_bv_bv_unsigned; reflexivity]). }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
    rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 9%bv G9. rreg HRr 10%bv G10. rreg HRr 18%bv G18.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.

    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ].
    { norm_pc. stepjr F_65b64 D_65b64 (Z_to_bv 64 ret) ltac:(exact G1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl. }
    apply (CONT fx' A s Rr M model AI MS Hfs Hfds SX (sx_le_refl _ _ ST s)).
    -   intros r Hr. unfold callee_saved in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]); try contradiction;
        first [ rewrite G1; symmetry; exact Hra
              | rewrite G2, w_add by lia; unfold TOP_FRAME; replace (sp - 2576 + 2576) with sp by lia; symmetry; exact Hsp2
              | rewrite G8; reflexivity | rewrite G9; reflexivity | rewrite G18; reflexivity
              | rewrite Gs by inl; first [rewrite Q3; symmetry; exact Hgp | rewrite Q4; symmetry; exact Htp | apply Qs; inl] ].
    - exact G10.
    - exact FZ.
    - exact HL.
    - exact (eff_close C A M model AI EF DEFW).
  Qed.

  Lemma st_dtor : forall (fx' : FPState) A M model R (b nw : Z),
    tinv A M model -> tregs R -> frm_zero (@fp_csr fx') ->
    cell8 SEGS M (sp' + 16) b -> cell8 SEGS M (sp' + 32) (b + 4 * nw) -> 0 <= nw < 2 ^ 24 ->
    ((nw = 0 /\ b = 0) \/ (0 < nw /\ 0 < b /\ In (b, 4 * nw) (live MI A) /\ ~ In b (map fst (live MI A0)))) ->
    (forall q k, In (q, k) (live MI A) <-> ((0 < nw /\ (q, k) = (b, 4 * nw)) \/ In (q, k) (live MI A0))) ->
    srealizes SEGS (cfg fx' R T_DTOR_RET M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros fx' A M model R b nw TI TR FZ C16 C32 Hnw Hv HL.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    assert (Hb : 0 <= b /\ b + 4 * nw <= alloc_ceiling).
    { destruct Hv as [[-> ->] | (Hnw0 & Hb0 & Hin & _)]; [lia|]. destruct (live_facts' A M model b (4 * nw) AI Hin) as (_ & _ & Hce & _). lia. }
    unfold cell8 in C16, C32.
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 b; Z_to_bv 64 (b + 4 * nw)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (DW : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M a k).
    { intros a k H1 H2 i Hi. pose proof (DEFW (a + i - (sp - LIB_STACK)) ltac:(lia)) as D. replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia. exact D. }
    assert (HK : know_ok SEGS E M [KWord (SA (EVar 32) 16) (N.to_nat 8) (EVar 33); KWord (SA (EVar 32) 32) (N.to_nat 8) (EVar 34);
                                   KWr (SA (EVar 32) 0) (ELit 2576); KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply kword_var; [exact C16 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
      - eapply kword_var; [exact C32 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
      - eapply kwr_mdef; [evs; reflexivity | apply DW; lia | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
    destruct Hv as [[-> ->] | (Hnw0 & Hb0 & Hin & HbA0)].
    -
      apply (know_more E M [KRange (EVar 33) 0 0]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 2%bv G2.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      apply (st_exit fx' A M model Rr TI); [| exact FZ |].
      + unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr.
      + intros q k. rewrite HL. split; [intros [[? _]|H]; [lia | exact H] | intros H; right; exact H].
    -
      apply (know_more E M [KRange (EVar 33) 1 (2 ^ 47)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 10%bv G10. rreg HRr 11%bv G11.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK.
      assert (TRr : TopS1Ctx.tregs R0 sp Rr).
      { unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr. }

      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (HM1w : forall a : word, ~ (sp' + 24 <= bv_unsigned a < sp' + 32) -> M1 a = M a).
      { intros a Ha. pose proof (u64_range a). unfold M1. rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes]; lia. }
      assert (HM1g : forall a : word, M a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
      assert (TI1 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A M1 model).
      { apply (tinv_store C A M model M1 (fun a => sp' + 24 <= a < sp' + 32) TI).
        - intros a Hna. apply HM1w. exact Hna.
        - intros a Ha. unfold W_of. cbn [fst snd]. lia.
        - exact HM1g. }
      pose proof TI1 as TI1'. destruct TI1' as [AI1 _ _ _ SX1 RC1 OSX1 EF1 DEFW1 FR1].
      rewrite SymExec.alu64_add_lit in G11 || idtac.
      eapply (DEL fx' A Rr M1 model b (4 * nw) sp' T_EXIT K AI1 MS).
      + apply img_ro_clear_of; [exact RC1 |]. intros a Ha. eapply (sx_relro ST); [exact SX1 | exact Ha].
      + constructor; [exact G1 | apply bv_eq; vm_compute; reflexivity | unfold T_EXIT; lia | exact G2 | exact Hsp16' | lia | rewrite Gs by inl; exact Q3 | rewrite Gs by inl; exact Q4].
      + exact G10.
      + right. exact Hin.
      + lia.
      + apply stack_room_of_defined; [lia | lia | lia |]. intros i Hi. pose proof (DEFW1 (sp' - MALLOC_STACK MI + i - (sp - LIB_STACK)) ltac:(lia)) as D.
        replace (sp - LIB_STACK + (sp' - MALLOC_STACK MI + i - (sp - LIB_STACK))) with (sp' - MALLOC_STACK MI + i) in D by lia. exact D.
      + intros a Ha. eapply (win_unowned' A M1 model); [exact AI1 | unfold zwin in Ha; lia].
      + intros A' R' M' model' AI' MS' Hfs' Hfds' KP LD CA CB OWN FRq DEF.
        assert (EFd : eff MI A A' M1 M' (sp' - MALLOC_STACK MI, sp') (fun a => b <= a < b + 4 * nw)).
        { eapply (eff_of_del MI); [exact CA | exact CB | exact OWN | exact FRq | exact DEF | intros a Ha; exact Ha | intros a Ha; exact Ha |].
          intros a Ha. exact (live_offimg Ly.L MI A M1 model b (4 * nw) a AI1 Hin Ha). }
        assert (HFJ : forall a, b <= a < b + 4 * nw -> TopS1Ctx.J MI A0 a).
        { intros a Ha. destruct (live_facts' A M1 model b (4 * nw) AI1 Hin) as (_ & Hb1 & Hce & _).
          split; [lia|]. split; [exact (live_offimg Ly.L MI A M1 model b (4 * nw) a AI1 Hin Ha)|].
          intros q k Hqk Hin'. assert (Hq : In (q, k) (live MI A)) by (apply HL; right; exact Hqk).
          destruct (Z.eq_dec q b) as [-> | Hne]. { exfalso. apply HbA0. apply in_map_iff. exists (b, k). split; [reflexivity | exact Hqk]. }
          destruct (live_facts' A M1 model q k AI1 Hq) as (Hk0 & _).
          destruct (ai_live_disjoint MI A M1 model b (4 * nw) q k AI1 Hin Hq ltac:(congruence)); lia. }
        assert (SX' : sx_inv ST s M').
        { eapply (sx_inv_via_eff' s A A' M1 M' model); [exact SX1 | exact AI1 | exact EFd | exact OSX1 | exact Hesx | | cbn; lia].
          intros a Ha. exact (live_offimg Ly.L MI A M1 model b (4 * nw) a AI1 Hin Ha). }
        assert (TI' : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A' M' model').
        { eapply (tinv_call C A M1 model A' M' model' Rr R' (MALLOC_STACK MI) _ TI1); [| exact EFd | lia | exact HFJ].
          constructor; [exact AI' | exact MS' | exact Hfs' | exact Hfds' | exact SX' | exact KP]. }
        apply (st_exit fx' A' M' model' R' TI' (tregs_kept R0 sp Rr R' TRr KP) FZ).
        intros q k. rewrite (LD q k), HL. split.
        * intros [[[_ E]|H] Hne]; [injection E; intros; subst; exfalso; exact (Hne eq_refl) | exact H].
        * intros H. split; [right; exact H|]. intros ->. apply HbA0. apply in_map_iff. exists (b, k). split; [reflexivity | exact H].
  Qed.

  Lemma st_destroy : forall (fx' : FPState) A M model R (q env b nw : Z),
    tinv A M model -> tregs R -> frm_zero (@fp_csr fx') -> getr R 8%bv = Z_to_bv 64 q ->
    ctx_rep MI A M q env -> ~ In q (map fst (live MI A0)) ->
    cell8 SEGS M (sp' + 16) b -> cell8 SEGS M (sp' + 32) (b + 4 * nw) -> 0 <= nw < 2 ^ 24 ->
    ((nw = 0 /\ b = 0) \/ (0 < nw /\ 0 < b /\ In (b, 4 * nw) (live MI A) /\ ~ In b (map fst (live MI A0)))) -> q <> b ->
    (forall q' k, In (q', k) (live MI A) <-> ((q', k) = (q, CTX_SZ) \/ (0 < nw /\ (q', k) = (b, 4 * nw)) \/ In (q', k) (live MI A0))) ->
    srealizes SEGS (cfg fx' R T_PARSE_RET M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros fx' A M model R q env b nw TI TR FZ Q8 CX HqA0 C16 C32 Hnw Hv Hqb HL.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    pose proof CX as CX'. destruct CX' as (Hq0 & Hq16 & Hq63 & HqIn & _).
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 q]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (8%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
    rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 10%bv G10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
    clear HRr HR HK.
    assert (TRr : TopS1Ctx.tregs R0 sp Rr).
    { unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr. }
    destruct HcC as (_ & Ecd & HcSTK). rewrite <- Ecd.
    eapply (CTXD fx' A s Rr M model sp' T_DTOR_RET q env K).
    - apply (mk_callB C A M model Rr T_DTOR_RET _ TI TRr G1); [apply bv_eq; vm_compute; reflexivity | unfold T_DTOR_RET; lia | lia].
    - exact G10.
    - exact CX.
    - intros A' R' M' model' RB' LD EFc.
      pose proof RB' as RB''. destruct RB'' as [AI' MS' Hfs' Hfds' SX' KP].
      assert (HFJ : forall a, zwin q (q + CTX_SZ) a -> TopS1Ctx.J MI A0 a).
      { intros a Ha. unfold zwin in Ha. destruct (live_facts' A M model q CTX_SZ AI HqIn) as (_ & _ & Hce & _).
        split; [lia|]. split; [exact (live_offimg Ly.L MI A M model q CTX_SZ a AI HqIn Ha)|].
        intros q' k Hqk Hin'. assert (Hq' : In (q', k) (live MI A)) by (apply HL; right; right; exact Hqk).
        destruct (Z.eq_dec q' q) as [-> | Hne]. { apply HqA0. apply in_map_iff. exists (q, k). split; [reflexivity | exact Hqk]. }
        destruct (live_facts' A M model q' k AI Hq') as (Hk0 & _).
        destruct (ai_live_disjoint MI A M model q CTX_SZ q' k AI HqIn Hq' ltac:(congruence)); lia. }
      assert (TI' : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A' M' model').
      { eapply (tinv_call C A M model A' M' model' Rr R' _ _ TI RB' EFc); [lia | exact HFJ]. }
      destruct LD as (lv1 & LD1 & ELV).
      apply (st_dtor fx' A' M' model' R' b nw TI' (tregs_kept R0 sp Rr R' TRr KP) FZ).
      + eapply (cell_call C A M model A' M'); [exact TI | exact EFc | lia | exact HFJ | lia | cbn; lia | exact C16].
      + eapply (cell_call C A M model A' M'); [exact TI | exact EFc | lia | exact HFJ | lia | cbn; lia | exact C32].
      + exact Hnw.
      + destruct Hv as [H0 | (Hnw0 & Hb0 & Hin & HbA0)]; [left; exact H0 | right].
        split; [exact Hnw0|]. split; [exact Hb0|]. split; [| exact HbA0]. rewrite ELV. apply LD1. split; [exact Hin | congruence].
      + intros q' k. rewrite ELV, (LD1 q' k), HL. split.
        * intros [[E | [H | H]] Hne]; [injection E; intros; subst; exfalso; exact (Hne eq_refl) | left; exact H | right; exact H].
        * intros [[Hnw0 E] | H]; [split; [right; left; split; [exact Hnw0 | exact E] | injection E; intros; subst; congruence] |].
          split; [right; right; exact H|]. intros ->. apply HqA0. apply in_map_iff. exists (q, k). split; [reflexivity | exact H].
  Qed.

  Lemma w_mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof using.
    intros a b. apply bv_eq. cbn [mul_div].
    rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Zmult_mod. reflexivity.
  Qed.
  Lemma words_sra : forall nw, 0 <= nw -> 4 * nw < 2 ^ 62 ->
    alu64 ALU_SRA (Z_to_bv 64 (4 * nw)) (Z_to_bv 64 2) = Z_to_bv 64 nw.
  Proof using.
    intros nw Hnw Hh. apply bv_eq.
    rewrite u_sra64_nonneg by (rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small; lia).
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small 2), (Z.mod_small nw), (Z.mod_small (4 * nw)) by lia.
    change (2 ^ (2 mod 64)) with 4. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  Qed.

  Lemma st_parse : forall A M model R (q env b nw : Z),
    tinv A M model -> tregs R -> getr R 8%bv = Z_to_bv 64 q -> getr R 12%bv = Z_to_bv 64 b ->
    ctx_rep MI A M q env -> ~ In q (map fst (live MI A0)) ->
    cell8 SEGS M (sp' + 16) b -> cell8 SEGS M (sp' + 24) (b + 4 * nw) -> cell8 SEGS M (sp' + 32) (b + 4 * nw) -> 0 <= nw < 2 ^ 24 ->
    ((nw = 0 /\ b = 0) \/ (0 < nw /\ 0 < b /\ b mod 16 = 0 /\ In (b, 4 * nw) (live MI A) /\ ~ In b (map fst (live MI A0)) /\ mdef M b (4 * nw))) ->
    q <> b ->
    live MI A = (if nw =? 0 then [] else [(b, 4 * nw)]) ++ (q, CTX_SZ) :: live MI A0 ->
    0 <= env < 32 ->
    srealizes SEGS (cfg fx R T_AFTER M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model R q env b nw TI TR Q8 Q12 CX HqA0 C16 C24 C32 Hnw Hv Hqb HL Henv.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    pose proof CX as CX'. destruct CX' as (Hq0 & Hq16 & Hq63 & HqIn & _).
    destruct (live_facts' A M model q CTX_SZ AI HqIn) as (_ & _ & Hqce & _).
    assert (Hb : 0 <= b /\ b + 4 * nw <= alloc_ceiling).
    { destruct Hv as [[-> ->] | (Hnw0 & Hb0 & _ & Hin & _)]; [lia|]. destruct (live_facts' A M model b (4 * nw) AI Hin) as (_ & _ & Hce & _). lia. }
    unfold cell8 in C24.
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 q; Z_to_bv 64 b; Z_to_bv 64 (b + 4 * nw)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (8%bv, EVar 33); (12%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KWord (SA (EVar 32) 24) (N.to_nat 8) (EVar 35)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      eapply kword_var; [exact C24 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
    rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 10%bv G10. rreg HRr 11%bv G11. rreg HRr 12%bv G12. rreg HRr 13%bv G13.
    rreg HRr 14%bv G14. rreg HRr 15%bv G15. rreg HRr 16%bv G16.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
    clear HRr HR HK.
    rewrite w_mul_lit, SymExec.alu64_add_lit in G13. replace (-1 * b + (b + 4 * nw)) with (4 * nw) in G13 by lia. rewrite words_sra in G13 by lia.
    assert (TRr : TopS1Ctx.tregs R0 sp Rr).
    { unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr. }
    destruct Hkc as (Ekp & HkSTK). unfold binary_parse_stmt, parse_opts_stmt in PARSE. rewrite Ekp in PARSE.
    assert (HcapsA : caps MI A = lib_caps) by (rewrite (ef_caps _ _ _ _ _ _ _ _ _ EF); exact CAPS).
    assert (HbigA : bigcap MI A = LIB_BIGCAP) by (rewrite (ef_bigcap _ _ _ _ _ _ _ _ _ EF); exact BIGC).
    eapply (PARSE fx A s Rr M model sp' T_PARSE_RET q env b nw K).
    - apply (mk_callB C A M model Rr T_PARSE_RET _ TI TRr G1); [apply bv_eq; vm_compute; reflexivity | unfold T_PARSE_RET; lia | lia].
    - exact RC.
    - exact FRM.
    - exact G10. - exact G11. - exact G12. - exact G13. - exact G14. - exact G15. - exact G16.
    - intros HH. discriminate HH.
    - exact CX.
    - intros a Ha. unfold zwin in *. lia.
    - exact Henv.
    - intros Hb0. destruct Hv as [[-> ->] | (Hnw0 & Hb1 & Hal & Hin & HbA0 & Hdef)]; [lia|].
      split; [lia|]. split; [destruct (proj1 (Z.mod_divide b 16 ltac:(lia)) Hal) as [k Hk]; rewrite Hk; replace (k * 16) with (4 * k * 4) by lia; apply Z_mod_mult|]. split; [lia|]. split; [lia|]. split; [exact Hdef|].
      right. exists b, (4 * nw). split; [exact Hin | lia].
    - intros a Ha. unfold zwin in *. lia.
    - apply (BUDGET A ((q, CTX_SZ) :: live MI A0) b nw HcapsA HbigA).
      + cbn. lia.
      + intros q' k [E | Hin']; [injection E; intros <- <-; unfold CTX_SZ; lia | exact (LSZ q' k Hin')].
      + rewrite HL. destruct (Z.eqb_spec nw 0); apply Permutation_refl.
      + exact Hnw.
    - intros fx1 A' R' M' model' r RB' FZ1 Qr PERM EFp.
      pose proof RB' as RB''. destruct RB'' as [AI' MS' Hfs' Hfds' SX' KP].
      assert (HFJ : forall a, PrsNeeds.junk SEGS Ly.L MI A a -> TopS1Ctx.J MI A0 a).
      { intros a (Ha & Hni & Hnl). split; [exact Ha|]. split; [exact Hni|]. intros q' k Hqk. apply Hnl. rewrite HL. apply in_app_iff. right. right. exact Hqk. }
      assert (TI' : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A' M' model').
      { eapply (tinv_call C A M model A' M' model' Rr R' _ _ TI RB' EFp); [lia | exact HFJ]. }
      assert (HLin : forall x, In x (live MI A') <-> In x (live MI A)).
      { intros x. split; intros Hx; [exact (Permutation_in _ PERM Hx) | exact (Permutation_in _ (Permutation_sym PERM) Hx)]. }
      apply (st_destroy fx1 A' M' model' R' q env b nw TI' (tregs_kept R0 sp Rr R' TRr KP) FZ1).
      + rewrite (KP 8%bv) by (clear; inl). rewrite G8. reflexivity.
      + apply (ctx_relive MI A A' M' q env); [| intros Hq; apply HLin; exact Hq].
        assert (AGq : agree_on M M' q CTX_SZ).
        { eapply (agree_block_via_eff' A A' M M' model model' _ _ q CTX_SZ EFp AI AI' HqIn); [apply HLin; exact HqIn | | cbn; lia].
          intros a' Ha' (_ & _ & Hnl). exact (Hnl q CTX_SZ HqIn Ha'). }
        apply (ctx_frame MI A M M' q env CX). intros a Ha. unfold ctx_fp, zwin in Ha.
        pose proof (AGq (a - q) ltac:(lia)) as E. replace (q + (a - q)) with a in E by lia. exact E.
      + exact HqA0.
      + eapply (cell_call C A M model A' M'); [exact TI | exact EFp | lia | exact HFJ | lia | cbn; lia | exact C16].
      + eapply (cell_call C A M model A' M'); [exact TI | exact EFp | lia | exact HFJ | lia | cbn; lia | exact C32].
      + exact Hnw.
      + destruct Hv as [H0 | (Hnw0 & Hb0 & _ & Hin & HbA0 & _)]; [left; exact H0 | right].
        split; [exact Hnw0|]. split; [exact Hb0|]. split; [apply HLin; exact Hin | exact HbA0].
      + exact Hqb.
      + intros q' k. rewrite (HLin (q', k)), HL. rewrite in_app_iff. cbn [In]. destruct (Z.eqb_spec nw 0); cbn [In].
        * split; [intros [[]|[E|H]]; [left; symmetry; exact E | right; right; exact H] | intros [E|[[? _]|H]]; [right; left; symmetry; exact E | lia | right; right; exact H]].
        * split; [intros [[E|[]]|[E|H]]; [right; left; split; [lia | symmetry; exact E] | left; symmetry; exact E | right; right; exact H]
                | intros [E|[[_ E]|H]]; [right; left; symmetry; exact E | left; left; symmetry; exact E | right; right; exact H]].
  Qed.
End Part.
End TopS1A.

Module TopS1B.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.DrvLibContract.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Ctx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.S1_code_65a48_65b90 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.TopS1A.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rdn_byte : forall M (a : Z) (len : nat) (bs : list byte) (k : Z),
  rdn SEGS M (Z_to_bv 64 a) len = Some bs -> 0 <= k < Z.of_nat len -> 0 <= a -> a + Z.of_nat len <= 2 ^ 64 ->
  cellw SEGS M (a + k) 1 (bv_unsigned (nth (Z.to_nat k) bs (Z_to_bv 8 0))).
Proof.
  intros M a len bs k H Hk Ha Halen.
  pose proof (rdn_nth SEGS M len (Z_to_bv 64 a) bs (Z.to_nat k) H ltac:(lia)) as R1.
  replace (Z_to_bv 64 a + nat_to_word (Z.to_nat k))%bv with (Z_to_bv 64 (a + k) : word) in R1.
  2: { apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z2Nat.id by lia.
       rewrite (Z.mod_small a), (Z.mod_small k), (Z.mod_small (a + k)) by lia. reflexivity. }
  pose proof (bv_unsigned_in_range _ (nth (Z.to_nat k) bs (Z_to_bv 8 0))) as Hr. change (bv_modulus 8%N) with 256 in Hr.
  split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite R1. f_equal. cbn [word_to_le_bytes Z_to_le_bytes].
  f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite bv_wrap64_mod, (Z.mod_small _ (2 ^ 64)) by lia.
  unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section Part.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Variables (cR : rg_consts) (cC : ctx_consts) (cV : vec_consts) (kc : prs_consts).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp ret p n : Z) (payload : list byte) (K : TSet).
  Variable C : topC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K.
  #[local] Ltac ctx := topctx_pose C.
  #[local] Ltac in_sub Hr := revert Hr; clear; intros Hr; cbn in Hr; decompose [or] Hr; try contradiction; subst; inl.
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation sp' := (sp - TOP_FRAME).
  #[local] Abbreviation W := (sp - LIB_STACK, sp).
  #[local] Abbreviation J := (J MI A0).
  #[local] Abbreviation FJW := (FJW MI A0 sp).
  #[local] Abbreviation tinv := (tinv MI ST A0 s R0 M0 model0 sp ret).
  #[local] Abbreviation tregs := (tregs R0 sp).
  #[local] Abbreviation tframe := (tframe R0 sp ret).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation live_facts' := (live_facts Ly.L MI).
  #[local] Abbreviation win_unowned' := (win_unowned C).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff Ly.L MI ly_img_low ly_rw_img ly_errno_rw).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff Ly.L MI ly_rw_img ly_errno_rw).
  #[local] Abbreviation defined_via_eff' := (defined_via_eff Ly.L MI ly_img_low ly_rw_img ly_errno_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_rw_not_relro ly_errno_rw).

  #[local] Abbreviation st_parse' := (st_parse MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C).
  #[local] Abbreviation st_exit' := (st_exit MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C).

  Lemma st_loop : forall (k : nat) A M model R (q b nw i : Z),
    Z.of_nat k = nw - i -> 0 <= i < nw -> 4 * nw <= n ->
    tinv A M model -> tregs R -> getr R 8%bv = Z_to_bv 64 q -> getr R 12%bv = Z_to_bv 64 b ->
    getr R 10%bv = Z_to_bv 64 (p + 3 + 4 * i) -> getr R 11%bv = Z_to_bv 64 (p + 3 + 4 * nw) -> getr R 13%bv = Z_to_bv 64 (b + 4 * i) ->
    ctx_rep MI A M q RG_ENV -> ~ In q (map fst (live MI A0)) ->
    cell8 SEGS M (sp' + 16) b -> cell8 SEGS M (sp' + 24) (b + 4 * nw) -> cell8 SEGS M (sp' + 32) (b + 4 * nw) ->
    0 < b -> b mod 16 = 0 -> In (b, 4 * nw) (live MI A) -> ~ In b (map fst (live MI A0)) -> mdef M b (4 * nw) -> q <> b ->
    live MI A = [(b, 4 * nw)] ++ (q, CTX_SZ) :: live MI A0 ->
    rdn SEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some payload -> In (p, n) (live MI A0) ->
    srealizes SEGS (cfg fx R T_LOOP M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    intros k. induction k as [|k IH]; intros A M model R q b nw i Hk Hi Hnwn TI TR Q8 Q12 Q10 Q11 Q13 CX HqA0 C16 C24 C32 Hb0 Hb16 HbIn HbA0 Hdef Hqb HL RDM HpIn; [lia|].
    ctx. destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity. assert (HCS : CTX_SZ = 64) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    pose proof CX as CX'. destruct CX' as (Hq0 & Hq16 & Hq63 & HqIn & _).
    assert (HpA : In (p, n) (live MI A)) by (rewrite HL; apply in_app_iff; right; right; exact HpIn).
    destruct (live_facts' A M model p n AI HpA) as (_ & Hp0 & Hpce & Hpall).
    destruct (live_facts' A M model b (4 * nw) AI HbIn) as (_ & _ & Hbce & Hball).
    assert (Hpb : p + n <= b \/ b + 4 * nw <= p).
    { destruct (Z.eq_dec p b) as [-> | Hne]; [exfalso; apply HbA0; apply in_map_iff; exists (b, n); split; [reflexivity | exact HpIn]|].
      exact (ai_live_disjoint MI A M model p n b (4 * nw) AI HpA HbIn Hne). }

    pose proof (rdn_byte M p (Z.to_nat n) payload (4 * i) RDM ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (rdn_byte M p (Z.to_nat n) payload (4 * i + 1) RDM ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (rdn_byte M p (Z.to_nat n) payload (4 * i + 2) RDM ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
    pose proof (rdn_byte M p (Z.to_nat n) payload (4 * i + 3) RDM ltac:(lia) ltac:(lia) ltac:(lia)) as B3.
    set (y0 := bv_unsigned (nth (Z.to_nat (4 * i)) payload (Z_to_bv 8 0))) in B0.
    set (y1 := bv_unsigned (nth (Z.to_nat (4 * i + 1)) payload (Z_to_bv 8 0))) in B1.
    set (y2 := bv_unsigned (nth (Z.to_nat (4 * i + 2)) payload (Z_to_bv 8 0))) in B2.
    set (y3 := bv_unsigned (nth (Z.to_nat (4 * i + 3)) payload (Z_to_bv 8 0))) in B3.
    pose proof (proj1 B0) as Ry0. pose proof (proj1 B1) as Ry1. pose proof (proj1 B2) as Ry2. pose proof (proj1 B3) as Ry3. cbn in Ry0, Ry1, Ry2, Ry3.
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 (p + 3 + 4 * i); Z_to_bv 64 (p + 3 + 4 * nw); Z_to_bv 64 (b + 4 * i); Z_to_bv 64 b; Z_to_bv 64 q;
                        Z_to_bv 64 y0; Z_to_bv 64 y1; Z_to_bv 64 y2; Z_to_bv 64 y3]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 34); (13%bv, EVar 35); (12%bv, EVar 36); (8%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 33) 4 (2 ^ 47); KRange (EVar 35) 1 (2 ^ 47); KWr (SA (EVar 35) 0) (ELit 4); KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | replace (b + 4 * i + 0) with (b + 4 * i) by lia; intros j Hj; replace (b + 4 * i + j) with (b + (4 * i + j)) by lia; apply (Hdef (4 * i + j)); lia | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
    destruct (Z.eq_dec (i + 1) nw) as [Hlast | Hmore].
    -
      xruns HR HK 100%nat STOPS (SCR [false] [EVar 39; EVar 38; EVar 40; EVar 41] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite w_add, br_ne by lia; apply Bool.negb_false_iff; apply Z.eqb_eq; lia. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 12%bv G12.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (HM1w : forall a : word, ~ (b + 4 * i <= bv_unsigned a < b + 4 * i + 4) -> M1 a = M a).
      { intros a Ha. pose proof (u64_range a). unfold M1. rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes Z_to_le_bytes]; lia. }
      assert (HM1g : forall a : word, M a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
      assert (TI1 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A M1 model).
      { apply (tinv_storeJ C A M model M1 (fun a => b + 4 * i <= a < b + 4 * i + 4) TI).
        - intros a Hna. apply HM1w. exact Hna.
        - intros a Ha. split; [lia|]. split; [exact (live_offimg Ly.L MI A M model b (4 * nw) a AI HbIn ltac:(lia))|].
          intros q' k' Hqk Hin'. assert (Hq' : In (q', k') (live MI A)) by (rewrite HL; apply in_app_iff; right; right; exact Hqk).
          destruct (Z.eq_dec q' b) as [-> | Hne]. { apply HbA0. apply in_map_iff. exists (b, k'). split; [reflexivity | exact Hqk]. }
          destruct (live_facts' A M model q' k' AI Hq') as (Hk0 & _).
          destruct (ai_live_disjoint MI A M model b (4 * nw) q' k' AI HbIn Hq' ltac:(congruence)); lia.
        - intros a Ha. exact (proj1 (Hball a ltac:(lia))).
        - exact HM1g. }
      apply (st_parse' A M1 model Rr q RG_ENV b nw TI1).
      + unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr.
      + exact G8. + exact G12.
      + apply (ctx_frame MI A M M1 q RG_ENV CX). intros a Ha. unfold ctx_fp, zwin in Ha. apply HM1w. rewrite u64_of_Z by lia.
        destruct (ai_live_disjoint MI A M model b (4 * nw) q CTX_SZ AI HbIn HqIn ltac:(congruence)); unfold CTX_SZ in *; lia.
      + exact HqA0.
      + eapply cellw_agree; [exact C16 | intros j Hj; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia].
      + eapply cellw_agree; [exact C24 | intros j Hj; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia].
      + eapply cellw_agree; [exact C32 | intros j Hj; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia].
      + lia.
      + right. split; [lia|]. split; [exact Hb0|]. split; [exact Hb16|]. split; [exact HbIn|]. split; [exact HbA0|]. intros j Hj. apply HM1g. apply Hdef. exact Hj.
      + exact Hqb.
      + rewrite HL. destruct (Z.eqb_spec nw 0); [lia | reflexivity].
      + unfold RG_ENV. lia.
    -
      xruns HR HK 100%nat STOPS (SCR [true] [EVar 39; EVar 38; EVar 40; EVar 41] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite w_add, br_ne by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; lia. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 10%bv G10. rreg HRr 11%bv G11. rreg HRr 12%bv G12. rreg HRr 13%bv G13.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK. rewrite w_add in G10, G13 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (HM1w : forall a : word, ~ (b + 4 * i <= bv_unsigned a < b + 4 * i + 4) -> M1 a = M a).
      { intros a Ha. pose proof (u64_range a). unfold M1. rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes Z_to_le_bytes]; lia. }
      assert (HM1g : forall a : word, M a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
      assert (TI1 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A M1 model).
      { apply (tinv_storeJ C A M model M1 (fun a => b + 4 * i <= a < b + 4 * i + 4) TI).
        - intros a Hna. apply HM1w. exact Hna.
        - intros a Ha. split; [lia|]. split; [exact (live_offimg Ly.L MI A M model b (4 * nw) a AI HbIn ltac:(lia))|].
          intros q' k' Hqk Hin'. assert (Hq' : In (q', k') (live MI A)) by (rewrite HL; apply in_app_iff; right; right; exact Hqk).
          destruct (Z.eq_dec q' b) as [-> | Hne]. { apply HbA0. apply in_map_iff. exists (b, k'). split; [reflexivity | exact Hqk]. }
          destruct (live_facts' A M model q' k' AI Hq') as (Hk0 & _).
          destruct (ai_live_disjoint MI A M model b (4 * nw) q' k' AI HbIn Hq' ltac:(congruence)); lia.
        - intros a Ha. exact (proj1 (Hball a ltac:(lia))).
        - exact HM1g. }
      apply (IH A M1 model Rr q b nw (i + 1) ltac:(lia) ltac:(lia) Hnwn TI1).
      + unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr.
      + exact G8. + exact G12.
      + rewrite G10. f_equal. lia. + exact G11. + rewrite G13. f_equal. lia.
      + apply (ctx_frame MI A M M1 q RG_ENV CX). intros a Ha. unfold ctx_fp, zwin in Ha. apply HM1w. rewrite u64_of_Z by lia.
        destruct (ai_live_disjoint MI A M model b (4 * nw) q CTX_SZ AI HbIn HqIn ltac:(congruence)); unfold CTX_SZ in *; lia.
      + exact HqA0.
      + eapply cellw_agree; [exact C16 | intros j Hj; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia].
      + eapply cellw_agree; [exact C24 | intros j Hj; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia].
      + eapply cellw_agree; [exact C32 | intros j Hj; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia].
      + exact Hb0. + exact Hb16. + exact HbIn. + exact HbA0.
      + intros j Hj. apply HM1g. apply Hdef. exact Hj.
      + exact Hqb. + exact HL.
      + rewrite <- RDM. apply (rdn_agree_win SEGS M M1 p (Z.to_nat n)); [lia | lia |]. intros a Ha. unfold zwin in Ha. apply HM1w. rewrite u64_of_Z by lia. lia.
      + exact HpIn.
  Qed.

  Lemma st_vec : forall A M model R (q b nw : Z),
    tinv A M model -> tregs R -> getr R 8%bv = Z_to_bv 64 q -> getr R 9%bv = Z_to_bv 64 p -> getr R 18%bv = Z_to_bv 64 n ->
    4 * nw <= n < 4 * nw + 4 -> 0 < n ->
    ctx_rep MI A M q RG_ENV -> ~ In q (map fst (live MI A0)) ->
    cell8 SEGS M (sp' + 16) b -> cell8 SEGS M (sp' + 24) (b + 4 * nw) -> cell8 SEGS M (sp' + 32) (b + 4 * nw) ->
    ((nw = 0 /\ b = 0) \/ (0 < nw /\ 0 < b /\ b mod 16 = 0 /\ In (b, 4 * nw) (live MI A) /\ ~ In b (map fst (live MI A0)) /\ mdef M b (4 * nw))) ->
    q <> b ->
    live MI A = (if nw =? 0 then [] else [(b, 4 * nw)]) ++ (q, CTX_SZ) :: live MI A0 ->
    rdn SEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some payload -> In (p, n) (live MI A0) ->
    srealizes SEGS (cfg fx R T_RES_RET M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model R q b nw TI TR Q8 Q9 Q18 Hnw Hn0 CX HqA0 C16 C24 C32 Hv Hqb HL RDM HpIn.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity. assert (HCS : CTX_SZ = 64) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    assert (HpA : In (p, n) (live MI A)) by (rewrite HL; apply in_app_iff; right; right; exact HpIn).
    destruct (live_facts' A M model p n AI HpA) as (_ & Hp0 & Hpce & _).
    assert (Hb : 0 <= b /\ b + 4 * nw <= alloc_ceiling).
    { destruct Hv as [[-> ->] | (Hnw0 & Hb0 & _ & Hin & _)]; [lia|]. destruct (live_facts' A M model b (4 * nw) AI Hin) as (_ & _ & Hce & _). lia. }
    unfold cell8 in C16.
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 q; Z_to_bv 64 n; Z_to_bv 64 p; Z_to_bv 64 b]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 34); (9%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK0 : know_ok SEGS E M [KWord (SA (EVar 32) 16) (N.to_nat 8) (EVar 36); KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply kword_var; [exact C16 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
    destruct (Z.lt_ge_cases n 4) as [Hsmall | Hbig].
    -
      assert (Hnw0 : nw = 0) by lia. subst nw.
      pose proof (know_more E M [KRange (EVar 34) 1 3] _ HK0 ltac:(repeat apply Forall_cons; try apply Forall_nil; eapply krange_var; [evs; reflexivity | lia | lia])) as HK.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 12%bv G12.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK HK0.
      apply (st_parse' A M model Rr q RG_ENV b 0 TI).
      + unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr.
      + exact G8. + exact G12. + exact CX. + exact HqA0.
      + exact C16. + exact C24. + exact C32. + lia.
      + exact Hv. + exact Hqb. + exact HL. + unfold RG_ENV. lia.
    -
      assert (Hnw1 : 1 <= nw) by lia.
      assert (Hdiv : (n + -4) / 2 ^ 2 = nw - 1).
      { change (2 ^ 2) with 4. apply Z.le_antisymm; [| apply Z.div_le_lower_bound; lia].
        apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
      pose proof (know_more E M [KRange (EVar 34) 4 (2 ^ 26)] _ HK0 ltac:(repeat apply Forall_cons; try apply Forall_nil; eapply krange_var; [evs; reflexivity | lia | lia])) as HK.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 10%bv G10. rreg HRr 11%bv G11. rreg HRr 12%bv G12. rreg HRr 13%bv G13.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK HK0.
      rewrite ?SymExec.alu64_add_lit in G10, G11. rewrite w_srl in G11 by lia. rewrite Hdiv, w_mul_lit, !SymExec.alu64_add_lit in G11.
      destruct Hv as [[? ?] | (_ & Hb0 & Hb16 & HbIn & HbA0 & Hdef)]; [lia|].
      apply (st_loop (Z.to_nat nw) A M model Rr q b nw 0 ltac:(lia) ltac:(lia) ltac:(lia) TI).
      + unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr.
      + exact G8. + exact G12.
      + rewrite G10. f_equal. lia. + rewrite G11. f_equal. lia. + rewrite G13. f_equal. lia.
      + exact CX. + exact HqA0.
      + exact C16. + exact C24. + exact C32.
      + exact Hb0. + exact Hb16. + exact HbIn. + exact HbA0. + exact Hdef. + exact Hqb.
      + rewrite HL. destruct (Z.eqb_spec nw 0); [lia | reflexivity].
      + exact RDM. + exact HpIn.
  Qed.

  Lemma st_res : forall A M model R (q : Z),
    tinv A M model -> tregs R -> getr R 10%bv = Z_to_bv 64 q -> getr R 9%bv = Z_to_bv 64 p -> getr R 18%bv = Z_to_bv 64 n -> 0 < n ->
    ctx_rep MI A M q RG_ENV -> ~ In q (map fst (live MI A0)) -> live MI A = (q, CTX_SZ) :: live MI A0 ->
    rdn SEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some payload -> In (p, n) (live MI A0) ->
    srealizes SEGS (cfg fx R T_CTX_RET M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model R q TI TR Q10 Q9 Q18 Hn0 CX HqA0 HL RDM HpIn.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity. assert (HCS : CTX_SZ = 64) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    pose proof CX as CX'. destruct CX' as (Hq0 & Hq16 & Hq63 & HqIn & _).
    assert (HpA : In (p, n) (live MI A)) by (rewrite HL; right; exact HpIn).
    destruct (live_facts' A M model p n AI HpA) as (_ & Hp0 & Hpce & _).
    destruct (live_facts' A M model q CTX_SZ AI HqIn) as (_ & _ & Hqce & _).
    assert (DW : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M a k).
    { intros a k H1 H2 i Hi. pose proof (DEFW (a + i - (sp - LIB_STACK)) ltac:(lia)) as D. replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia. exact D. }
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 q; Z_to_bv 64 n; Z_to_bv 64 p]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (18%bv, EVar 34); (9%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 26 - 1); KRange (EVar 32) (2 ^ 24) (2 ^ 47); KAlign (EVar 32) 16; KWr (SA (EVar 32) 0) (ELit 2576)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hsp16'].
      - eapply kwr_mdef; [evs; reflexivity | replace (sp' + 0) with sp' by lia; apply DW; lia | lia | lia | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
    rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 9%bv G9. rreg HRr 10%bv G10. rreg HRr 11%bv G11. rreg HRr 18%bv G18.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
    clear HRr HR HK. rewrite w_add in G10 by lia. rewrite w_srl in G11 by lia. change (2 ^ 2) with 4 in G11.
    set (nw := n / 4) in G11.
    assert (Hnw : 4 * nw <= n < 4 * nw + 4) by (pose proof (Z.div_mod n 4 ltac:(lia)); pose proof (Z.mod_pos_bound n 4 ltac:(lia)); lia).
    assert (TRr : TopS1Ctx.tregs R0 sp Rr).
    { unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr. }

    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (HM1w : forall a : word, ~ (sp' + 16 <= bv_unsigned a < sp' + 40) -> M1 a = M a).
    { intros a Ha. pose proof (u64_range a). unfold M1. rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes Z_to_le_bytes]; lia. }
    assert (HM1g : forall a : word, M a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
    assert (TI1 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A M1 model).
    { apply (tinv_store C A M model M1 (fun a => sp' + 16 <= a < sp' + 40) TI).
      - intros a Hna. apply HM1w. exact Hna.
      - intros a Ha. unfold W_of. cbn [fst snd]. lia.
      - exact HM1g. }
    pose proof TI1 as TI1'. destruct TI1' as [AI1 _ _ _ SX1 RC1 OSX1 EF1 DEFW1 FR1].
    assert (V1 : vec32 MI A M1 (sp' + 16) 0 [] 0).
    { unfold vec32. split; [lia|]. split; [lia|]. split; [intros i Hi; pose proof (DEFW1 (sp' + 16 + i - (sp - LIB_STACK)) ltac:(lia)) as D; replace (sp - LIB_STACK + (sp' + 16 + i - (sp - LIB_STACK))) with (sp' + 16 + i) in D by lia; exact D|].
      split; [change (Zlen (@nil Z)) with 0; lia|]. split; [left; split; reflexivity|].
      split; [unfold M1; rdback|]. split; [change (0 + 4 * Zlen (@nil Z)) with 0; replace (sp' + 16 + 8) with (sp' + 24) by lia; unfold M1; rdback|].
      split; [change (0 + 4 * 0) with 0; replace (sp' + 16 + 16) with (sp' + 32) by lia; unfold M1; rdback|].
      intros i Hi. change (Zlen (@nil Z)) with 0 in Hi. lia. }
    destruct HcV as (Ecv & HvSTK). rewrite <- Ecv.
    assert (HcapsA : caps MI A = lib_caps) by (rewrite (ef_caps _ _ _ _ _ _ _ _ _ EF); exact CAPS).
    assert (HbigA : bigcap MI A = LIB_BIGCAP) by (rewrite (ef_bigcap _ _ _ _ _ _ _ _ _ EF); exact BIGC).
    eapply (VRES fx A s Rr M1 model sp' T_RES_RET (sp' + 16) nw K).
    - apply (mk_callB C A M1 model Rr T_RES_RET _ TI1 TRr G1); [apply bv_eq; vm_compute; reflexivity | unfold T_RES_RET; lia | unfold NEW_STACK; lia].
    - exact G10. - exact G11. - exact V1.
    - split; [left; lia|]. intros a Ha. unfold zwin in *. lia.
    - lia.
    - unfold LIB_NMAX in HNMAX. lia.
    - intros Hnw0. rewrite HL. split.
      + intros Hlt. rewrite HcapsA. pose proof (lib_caps_ge_small (size_class MI (4 * nw))). pose proof (lib_caps_ge_small (size_class MI (4 * nw) + 1)).
        pose proof (count_class_le_length (size_class MI) (BIG MI) ((q, CTX_SZ) :: live MI A0) (size_class MI (4 * nw))).
        pose proof (count_class_le_length (size_class MI) (BIG MI) ((q, CTX_SZ) :: live MI A0) (size_class MI (4 * nw) + 1)).
        cbn [length] in *. unfold CAP_SMALL in *. lia.
      + intros Hge. rewrite HbigA.
        pose proof (big_bytes_le (round_big MI) (BIG MI) ((q, CTX_SZ) :: live MI A0) (2 ^ 26 + 4116)) as HB.
        pose proof (RB (4 * nw) ltac:(lia)). unfold LIB_BIGCAP. cbn [length] in HB.
        assert (HB' : 0 <= big_bytes_f (round_big MI) (BIG MI) ((q, CTX_SZ) :: live MI A0) <= 3 * (2 ^ 26 + 4116)).
        { destruct (HB ltac:(intros q' k [E|Hin]; [injection E; intros <- <-; unfold CTX_SZ; rewrite HBIG; cbn; lia|];
                            pose proof (LSZ q' k Hin); destruct (Z.leb_spec (BIG MI) k); [pose proof (RB k ltac:(lia)); lia | lia]) ltac:(lia)) as [H1 H2].
          split; [exact H1|]. etransitivity; [exact H2|]. nia. }
        lia.
    - intros A' R' M' model' b RB' V' HLV EFr.
      pose proof RB' as RB''. destruct RB'' as [AI' MS' Hfs' Hfds' SX' KP].
      pose proof V' as V''. destruct V'' as (_ & _ & Hmd & Hzl & Hbk & Fb & Fe & Fc & _). rewrite Zlen_repeat in Fe by lia.

      assert (HLV' : live MI A' = (if nw =? 0 then [] else [(b, 4 * nw)]) ++ (q, CTX_SZ) :: live MI A0 /\ (nw = 0 /\ b = 0 \/ (0 < nw /\ ~ In b (map fst (live MI A))))).
      { destruct HLV as [(-> & -> & ->) | (Hnw0 & lv1 & [-> Hnot] & ->)].
        - split; [rewrite HL; reflexivity | left; split; reflexivity].
        - destruct (Z.eqb_spec nw 0); [lia|]. split; [rewrite HL; reflexivity | right; split; [exact Hnw0 | exact Hnot]]. }
      destruct HLV' as [HL' Hbn].
      assert (HFJ : forall a, (zwin (sp' + 16) (sp' + 16 + 24) a \/ (0 < nw /\ zwin b (b + 4 * nw) a)) -> TopS1Ctx.J MI A0 a \/ (sp' <= a < sp' + 2544)).
      { intros a [Ha | [Hnw0 Ha]]; unfold zwin in Ha; [right; lia | left].
        destruct Hbk as [[-> ->] | (Hb0 & Hbal & _ & _ & HbIn & _)]; [lia|].
        destruct (live_facts' A' M' model' b (4 * nw) AI' HbIn) as (_ & _ & Hbce & _).
        split; [lia|]. split; [exact (live_offimg Ly.L MI A' M' model' b (4 * nw) a AI' HbIn Ha)|].
        intros q' k' Hqk Hin'. assert (Hq' : In (q', k') (live MI A')) by (rewrite HL'; apply in_app_iff; right; right; exact Hqk).
        destruct (Z.eq_dec q' b) as [-> | Hne].
        { destruct Hbn as [[? ?] | [_ Hnot]]; [lia|]. apply Hnot. rewrite HL. cbn. right. apply in_map_iff. exists (b, k'). split; [reflexivity | exact Hqk]. }
        destruct (live_facts' A' M' model' q' k' AI' Hq') as (Hk0 & _).
        destruct (ai_live_disjoint MI A' M' model' b (4 * nw) q' k' AI' HbIn Hq' ltac:(congruence)); lia. }
      assert (TI' : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A' M' model').
      { eapply (tinv_callW C A M1 model A' M' model' Rr R' _ _ TI1 RB' EFr); [unfold NEW_STACK; lia | exact HFJ |].
        intros a _ Ha. destruct (Z.lt_ge_cases a (sp' + 16)) as [Hlo|Hge].
        all: cycle 1. 1: destruct (Z.lt_ge_cases a (sp' + 40)) as [Hin40|Hge40].
        - pose proof (Hmd (a - (sp' + 16)) ltac:(lia)) as D. replace (sp' + 16 + (a - (sp' + 16))) with a in D by lia. exact D.
        -
          destruct (ef_def _ _ _ _ _ _ _ _ _ EFr a ltac:(lia) ltac:(pose proof (DEFW1 (a - (sp - LIB_STACK)) ltac:(lia)) as D; replace (sp - LIB_STACK + (a - (sp - LIB_STACK))) with a in D by lia; exact D)) as [H|[H|[[H|[_ H]]|H]]].
          + exact H. + exfalso. exact (win_unowned' A M1 model a AI1 ltac:(lia) H).
          + unfold zwin in H. lia.
          + unfold zwin in H. destruct Hbk as [[-> ->] | (_ & _ & _ & _ & HbIn & _)]; [lia|]. destruct (live_facts' A' M' model' b (4 * nw) AI' HbIn) as (_ & _ & Hbce & _). lia.
          + exfalso. pose proof (ly_img_low _ (ly_rw_img _ (ly_errno_rw _ H))). lia.
        - destruct (ef_def _ _ _ _ _ _ _ _ _ EFr a ltac:(lia) ltac:(pose proof (DEFW1 (a - (sp - LIB_STACK)) ltac:(lia)) as D; replace (sp - LIB_STACK + (a - (sp - LIB_STACK))) with a in D by lia; exact D)) as [H|[H|[[H|[_ H]]|H]]].
          + exact H. + exfalso. exact (win_unowned' A M1 model a AI1 ltac:(lia) H).
          + unfold zwin in H. lia.
          + unfold zwin in H. destruct Hbk as [[-> ->] | (_ & _ & _ & _ & HbIn & _)]; [lia|]. destruct (live_facts' A' M' model' b (4 * nw) AI' HbIn) as (_ & _ & Hbce & _). lia.
          + exfalso. pose proof (ly_img_low _ (ly_rw_img _ (ly_errno_rw _ H))). lia. }
      assert (Hbr : 0 <= b /\ b + 4 * nw <= alloc_ceiling).
      { destruct Hbk as [[-> ->] | (Hb0 & _ & _ & _ & HbIn & _)]; [lia|]. destruct (live_facts' A' M' model' b (4 * nw) AI' HbIn) as (_ & _ & Hce & _). lia. }
      apply (st_vec A' M' model' R' q b nw TI' (tregs_kept R0 sp Rr R' TRr KP)).
      + rewrite (KP 8%bv) by (clear; inl). exact G8.
      + rewrite (KP 9%bv) by (clear; inl). exact G9.
      + rewrite (KP 18%bv) by (clear; inl). exact G18.
      + exact Hnw. + exact Hn0.
      + apply (ctx_relive MI A A' M' q RG_ENV); [| intros _; rewrite HL'; apply in_app_iff; right; left; reflexivity].
        assert (AGq : agree_on M1 M' q CTX_SZ).
        { eapply (agree_block_via_eff' A A' M1 M' model model' _ _ q CTX_SZ EFr AI1 AI'); [rewrite HL; left; reflexivity | rewrite HL'; apply in_app_iff; right; left; reflexivity | | cbn [fst]; unfold NEW_STACK; lia].
          intros a Ha [Hw | [Hnw0 Hw]]; unfold zwin in Hw; [lia|].
          destruct Hbk as [[-> ->] | (_ & _ & _ & _ & HbIn & _)]; [lia|].
          assert (HqA' : In (q, CTX_SZ) (live MI A')) by (rewrite HL'; apply in_app_iff; right; left; reflexivity).
          destruct (ai_live_disjoint MI A' M' model' b (4 * nw) q CTX_SZ AI' HbIn HqA' ltac:(intros ->; destruct Hbn as [[? ?]|[_ Hnot]]; [lia | apply Hnot; rewrite HL; left; reflexivity])); unfold CTX_SZ in *; lia. }
        apply (ctx_frame MI A M M' q RG_ENV CX). intros a Ha. unfold ctx_fp, zwin in Ha.
        rewrite <- (HM1w (Z_to_bv 64 a)) by (rewrite u64_of_Z by lia; lia).
        pose proof (AGq (a - q) ltac:(lia)) as E'. replace (q + (a - q)) with a in E' by lia. exact E'.
      + exact HqA0.
      + split; [cbn; lia | exact Fb].
      + split; [cbn; lia | replace (sp' + 24) with (sp' + 16 + 8) by lia; exact Fe].
      + split; [cbn; lia | replace (sp' + 32) with (sp' + 16 + 16) by lia; exact Fc].
      + destruct Hbk as [[-> Hc0] | (Hb0 & Hbal & Hc0 & _ & HbIn & _)]; [left; lia | right].
        split; [lia|]. split; [exact Hb0|]. split; [exact Hbal|]. split; [exact HbIn|]. split.
        * destruct Hbn as [[? ?]|[_ Hnot]]; [lia|]. intros Hin. apply Hnot. rewrite HL. cbn. right. exact Hin.
        * intros i Hi. destruct (live_facts' A' M' model' b (4 * nw) AI' HbIn) as (_ & _ & _ & Hall). exact (proj2 (Hall (b + i) ltac:(lia))).
      + intros ->. destruct Hbn as [[? ->]|[_ Hnot]]; [lia|]. apply Hnot. rewrite HL. left. reflexivity.
      + exact HL'.
      + rewrite <- RDM. rewrite <- (rdn_agree_win SEGS M M1 p (Z.to_nat n)); [| lia | lia | intros a Ha; unfold zwin in Ha; apply HM1w; rewrite u64_of_Z by lia; lia].
        apply (rdn_agree_win SEGS M1 M' p (Z.to_nat n)); [lia | lia |]. intros a Ha. unfold zwin in Ha.
        assert (AGp : agree_on M1 M' p n).
        { eapply (agree_block_via_eff' A A' M1 M' model model' _ _ p n EFr AI1 AI'); [exact HpA | rewrite HL'; apply in_app_iff; right; right; exact HpIn | | cbn [fst]; unfold NEW_STACK; lia].
          intros a' Ha' [Hw | [Hnw0 Hw]]; unfold zwin in Hw; [lia|].
          destruct Hbk as [[-> ->] | (_ & _ & _ & _ & HbIn & _)]; [lia|].
          assert (HpA' : In (p, n) (live MI A')) by (rewrite HL'; apply in_app_iff; right; right; exact HpIn).
          destruct (ai_live_disjoint MI A' M' model' b (4 * nw) p n AI' HbIn HpA' ltac:(intros ->; destruct Hbn as [[? ?]|[_ Hnot]]; [lia | apply Hnot; rewrite HL; right; apply in_map_iff; exists (p, n); split; [reflexivity | exact HpIn]])); lia. }
        pose proof (AGp (a - p) ltac:(lia)) as E'. replace (p + (a - p)) with a in E' by lia. exact E'.
      + exact HpIn.
  Qed.

  Lemma st_ctx : forall M model R,
    tinv A0 M model -> tregs R -> getr R 10%bv = Z_to_bv 64 RG_ENV -> getr R 9%bv = Z_to_bv 64 p -> getr R 18%bv = Z_to_bv 64 n -> 0 < n ->
    rdn SEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some payload -> In (p, n) (live MI A0) ->
    srealizes SEGS (cfg fx R T_GTE_RET M model) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros M model R TI TR Q10 Q9 Q18 Hn0 RDM HpIn.
    destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity. assert (HCS : CTX_SZ = 64) by reflexivity.
    pose proof TI as TI'. destruct TI' as [AI MS Hfs Hfds SX RC OSX EF DEFW FR].
    pose proof TR as TR'. destruct TR' as (Q2 & Q3 & Q4 & Qs).
    destruct (live_facts' A0 M model p n AI HpIn) as (_ & Hp0 & Hpce & _).
    pose (E := Eseed R [Z_to_bv 64 sp'; Z_to_bv 64 RG_ENV; Z_to_bv 64 p; Z_to_bv 64 n]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (9%bv, EVar 34); (18%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
    rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 9%bv G9. rreg HRr 10%bv G10. rreg HRr 18%bv G18.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
    clear HRr HR HK.
    assert (TRr : TopS1Ctx.tregs R0 sp Rr).
    { unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. split; [reflexivity|]. split; [exact Q3|]. split; [exact Q4|]. intros r Hr. rewrite Gs by (in_sub Hr). apply Qs, Hr. }
    destruct HcC as (Ecc & _ & HcSTK). rewrite <- Ecc.
    assert (HcapsA : caps MI A0 = lib_caps) by exact CAPS.
    eapply (CTXC fx A0 s Rr M model sp' T_CTX_RET RG_ENV K).
    - apply (mk_callB C A0 M model Rr T_CTX_RET _ TI TRr G1); [apply bv_eq; vm_compute; reflexivity | unfold T_CTX_RET; lia | unfold NEW_STACK; lia].
    - exact G10.
    - exact RG_ENV_valid.
    - split.
      + intros Hlt. rewrite CAPS. pose proof (lib_caps_ge_small (size_class MI CTX_SZ)). pose proof (lib_caps_ge_small (size_class MI CTX_SZ + 1)).
        pose proof (count_class_le_length (size_class MI) (BIG MI) (live MI A0) (size_class MI CTX_SZ)).
        pose proof (count_class_le_length (size_class MI) (BIG MI) (live MI A0) (size_class MI CTX_SZ + 1)).
        unfold CAP_SMALL in *. lia.
      + intros Hge. rewrite HBIG in Hge. unfold CTX_SZ in Hge. lia.
    - unfold LIB_NMAX in HNMAX. unfold CTX_SZ. lia.
    - intros A' R' M' model' q RB' Qq CX LD EFc.
      pose proof RB' as RB''. destruct RB'' as [AI' MS' Hfs' Hfds' SX' KP].
      pose proof CX as CX'. destruct CX' as (Hq0 & Hq16 & Hq63 & HqIn & _).
      destruct LD as (lv1 & [Elv Hnot] & HL'). rewrite Elv in HL'. clear Elv lv1.
      assert (HFJ : forall a, zwin q (q + CTX_SZ) a -> TopS1Ctx.J MI A0 a).
      { intros a Ha. unfold zwin in Ha. destruct (live_facts' A' M' model' q CTX_SZ AI' HqIn) as (_ & _ & Hqce & _).
        split; [lia|]. split; [exact (live_offimg Ly.L MI A' M' model' q CTX_SZ a AI' HqIn Ha)|].
        intros q' k' Hqk Hin'. assert (Hq' : In (q', k') (live MI A')) by (rewrite HL'; right; exact Hqk).
        destruct (Z.eq_dec q' q) as [-> | Hne]. { apply Hnot. apply in_map_iff. exists (q, k'). split; [reflexivity | exact Hqk]. }
        destruct (live_facts' A' M' model' q' k' AI' Hq') as (Hk0 & _).
        destruct (ai_live_disjoint MI A' M' model' q CTX_SZ q' k' AI' HqIn Hq' ltac:(congruence)); lia. }
      assert (TI' : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A' M' model').
      { eapply (tinv_call C A0 M model A' M' model' Rr R' _ _ TI RB' EFc); [unfold NEW_STACK; lia | exact HFJ]. }
      apply (st_res A' M' model' R' q TI' (tregs_kept R0 sp Rr R' TRr KP) Qq).
      + rewrite (KP 9%bv) by (clear; inl). exact G9.
      + rewrite (KP 18%bv) by (clear; inl). exact G18.
      + exact Hn0. + exact CX. + exact Hnot. + exact HL'.
      + rewrite <- RDM. apply (rdn_agree_win SEGS M M' p (Z.to_nat n)); [lia | lia |]. intros a Ha. unfold zwin in Ha.
        assert (AGp : agree_on M M' p n).
        { eapply (agree_block_via_eff' A0 A' M M' model model' _ _ p n EFc AI AI' HpIn); [rewrite HL'; right; exact HpIn | | cbn [fst]; unfold NEW_STACK; lia].
          intros a' Ha' Hw. unfold zwin in Hw.
          assert (HpA' : In (p, n) (live MI A')) by (rewrite HL'; right; exact HpIn).
          destruct (ai_live_disjoint MI A' M' model' q CTX_SZ p n AI' HqIn HpA' ltac:(intros ->; apply Hnot; apply in_map_iff; exists (p, n); split; [reflexivity | exact HpIn])); lia. }
        pose proof (AGp (a - p) ltac:(lia)) as E'. replace (p + (a - p)) with a in E' by lia. exact E'.
      + exact HpIn.
  Qed.

  Theorem top_correct : srealizes SEGS (cfg fx R0 LLVM_ENTRY M0 model0) K.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. destruct SPF as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv.
    assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    pose proof CR as CR'. destruct CR' as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
    pose proof (win_defined C) as DEF0.
    assert (DW : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M0 a k).
    { intros a k H1 H2 i Hi. pose proof (DEF0 (a + i - (sp - LIB_STACK)) ltac:(lia)) as D. replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia. exact D. }
    pose proof (u64_range (getr R0 8%bv)) as Hr8. pose proof (u64_range (getr R0 9%bv)) as Hr9. pose proof (u64_range (getr R0 18%bv)) as Hr18.

    pose (E := Eseed R0 [Z_to_bv 64 sp; Z_to_bv 64 p; Z_to_bv 64 n; Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 34); (1%bv, EVar 35); (8%bv, EVar 36); (9%bv, EVar 37); (18%bv, EVar 38)]) R0).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; try assumption; rewrite ?Z_to_bv_bv_unsigned; reflexivity. }
    assert (HK0 : know_ok SEGS E M0 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KAlign (EVar 32) 16; KWr (SA (EVar 32) (- 65536)) (ELit 65536)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hsp16].
      - eapply kwr_mdef; [evs; reflexivity | replace (sp + - 65536) with (sp - LIB_STACK) by lia; rewrite <- HLS; exact DEF0 | lia | lia | lia | lia]. }
    destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
    -
      pose proof (know_more E M0 [KRange (EVar 34) 0 0] _ HK0 ltac:(repeat apply Forall_cons; try apply Forall_nil; eapply krange_var; [evs; reflexivity | lia | lia])) as HK.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 2%bv G2.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK HK0. rewrite SymExec.alu64_add_lit in G2 || idtac.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (HM1w : forall a : word, ~ (sp' + 2544 <= bv_unsigned a < sp) -> M1 a = M0 a).
      { intros a Ha. pose proof (u64_range a). unfold M1. rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes Z_to_le_bytes]; lia. }
      assert (HM1g : forall a : word, M0 a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
      assert (TI1 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A0 M1 model0).
      { constructor.
        - eapply (ai_frame MI); [exact AI0 | | exact HM1g | reflexivity | reflexivity]. intros x Ho. apply HM1w. intros Hx. refine (win_unowned' A0 M0 model0 _ AI0 _ Ho). lia.
        - exact MS0. - reflexivity. - reflexivity.
        - apply (sx_frame ST s M0 M1 SX0). intros a Ha. apply HM1w. intros Hx.
          assert (Hi : in_ranges (ly_img Ly.L) (bv_unsigned a)) by (destruct Ha as [Hs | Hr]; [exact (ly_rw_img _ (sx_region_rw ST _ Hs)) | exact (ly_relro_img _ Hr)]).
          pose proof (ly_img_low _ Hi). lia.
        - eapply (ro_clear_frame Ly.L (fun a => sp' + 2544 <= a < sp) M0 M1 ROC); [intros a Hna; apply HM1w; exact Hna |]. intros a (Hi & _) Hx. pose proof (ly_img_low _ Hi). lia.
        - exact Hosx.
        - apply eff_store with (F := TopS1Ctx.FJW MI A0 sp); [| exact HM1g]. intros a _ Hw. apply HM1w. intros Hx. apply Hw. unfold W_of. cbn [fst snd]. lia.
        - intros i Hi. apply HM1g. apply DEF0. exact Hi.
        - unfold TopS1Ctx.tframe, cell8, cellw. rewrite HTF.
          replace (sp - 2576 + 2568) with (sp + -8) by lia. replace (sp - 2576 + 2560) with (sp + -16) by lia.
          replace (sp - 2576 + 2552) with (sp + -24) by lia. replace (sp - 2576 + 2544) with (sp + -32) by lia.
          rewrite !Z_to_bv_bv_unsigned. repeat split; try (cbn; lia); unfold M1; rdback. }
      apply (st_exit' fx A0 M1 model0 Rr TI1); [| exact FRM | intros q k; split; intros H; exact H].
      unfold TopS1Ctx.tregs. rewrite G2, !Gs by inl. rewrite HTF. split; [f_equal; lia|]. split; [exact Hgp|]. split; [exact Htp|]. intros r Hr. rewrite Gs by (in_sub Hr). reflexivity.
    -
      destruct Hp as [[? _] | [_ HpIn]]; [lia|].
      destruct (live_facts' A0 M0 model0 p n AI0 HpIn) as (_ & Hp0 & Hpce & Hpall).
      pose proof (know_more E M0 [KRange (EVar 34) 1 (2 ^ 26 - 1)] _ HK0 ltac:(repeat apply Forall_cons; try apply Forall_nil; eapply krange_var; [evs; reflexivity | lia | lia])) as HK.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 9%bv G9. rreg HRr 10%bv G10. rreg HRr 11%bv G11. rreg HRr 12%bv G12. rreg HRr 18%bv G18.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.
      clear HRr HR HK HK0. rewrite ?SymExec.alu64_add_lit in G2, G10. rewrite HTF in *.
      replace (sp + -2576) with (sp - 2576) in G2 by lia. replace (sp + -2536) with (sp - 2576 + 40) in G10 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (HM1w : forall a : word, ~ (sp' + 2544 <= bv_unsigned a < sp) -> M1 a = M0 a).
      { intros a Ha. pose proof (u64_range a). unfold M1. rewrite HTF in Ha. rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes Z_to_le_bytes]; lia. }
      assert (HM1g : forall a : word, M0 a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
      assert (TI1 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A0 M1 model0).
      { constructor.
        - eapply (ai_frame MI); [exact AI0 | | exact HM1g | reflexivity | reflexivity]. intros x Ho. apply HM1w. intros Hx. refine (win_unowned' A0 M0 model0 _ AI0 _ Ho). rewrite HTF in Hx. lia.
        - exact MS0. - reflexivity. - reflexivity.
        - apply (sx_frame ST s M0 M1 SX0). intros a Ha. apply HM1w. intros Hx.
          assert (Hi : in_ranges (ly_img Ly.L) (bv_unsigned a)) by (destruct Ha as [Hs | Hr]; [exact (ly_rw_img _ (sx_region_rw ST _ Hs)) | exact (ly_relro_img _ Hr)]).
          pose proof (ly_img_low _ Hi). rewrite HTF in Hx. lia.
        - eapply (ro_clear_frame Ly.L (fun a => sp' + 2544 <= a < sp) M0 M1 ROC); [intros a Hna; apply HM1w; exact Hna |]. intros a (Hi & _) Hx. pose proof (ly_img_low _ Hi). rewrite HTF in Hx. lia.
        - exact Hosx.
        - apply eff_store with (F := TopS1Ctx.FJW MI A0 sp); [| exact HM1g]. intros a _ Hw. apply HM1w. intros Hx. apply Hw. unfold W_of. cbn [fst snd]. rewrite HTF in Hx. lia.
        - intros i Hi. apply HM1g. apply DEF0. exact Hi.
        - unfold TopS1Ctx.tframe, cell8, cellw. rewrite HTF.
          replace (sp - 2576 + 2568) with (sp + -8) by lia. replace (sp - 2576 + 2560) with (sp + -16) by lia.
          replace (sp - 2576 + 2552) with (sp + -24) by lia. replace (sp - 2576 + 2544) with (sp + -32) by lia.
          rewrite !Z_to_bv_bv_unsigned. repeat split; try (cbn; lia); unfold M1; rdback. }
      pose proof TI1 as TI1'. destruct TI1' as [AI1 _ _ _ SX1 RC1 OSX1 EF1 DEFW1 FR1].
      assert (RDM1 : rdn SEGS M1 (Z_to_bv 64 p) (Z.to_nat n) = Some payload).
      { rewrite <- RDP. apply (rdn_agree_win SEGS M0 M1 p (Z.to_nat n)); [lia | lia |]. intros a Ha. unfold zwin in Ha. apply HM1w. rewrite u64_of_Z by lia. rewrite HTF. lia. }
      assert (DW1 : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M1 a k).
      { intros a k H1 H2 i Hi. pose proof (DEFW1 (a + i - (sp - LIB_STACK)) ltac:(lia)) as D. replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia. exact D. }
      destruct HcR as (Erc & Erg & HrcS & HrgS). unfold TOP_FRAME in *.

      destruct (RGC fx M1 Rr (sp - 2576) T_RGC_RET (sp - 2576 + 40) p n (firstn (Z.to_nat (Z.min n 37)) payload) RC1
                 ltac:(lia) ltac:(unfold RG_SZ; lia) ltac:(unfold RG_SZ; apply DW1; lia) Hp0 ltac:(lia) ltac:(lia)
                 ltac:(eapply rdn_firstn; [exact RDM1 | lia])
                 ltac:(intros a Ha; unfold zwin, RG_SZ in *; lia) ltac:(intros a Ha; unfold zwin, RG_SZ in *; lia)
                 ltac:(apply stack_room_of_defined; [lia | lia | lia | apply DW1; lia]) ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(apply bv_eq; vm_compute; reflexivity) G1 G2 G10 G11 G12)
        as (R2 & M2 & MSr & KP2 & SEED2 & FE2 & HG2 & RC2).
      rewrite Erc in MSr.
      eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact MSr |].
      assert (TI2 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A0 M2 model0).
      { apply (tinv_store C A0 M1 model0 M2 _ TI1 FE2); [| exact HG2]. intros a [Ha | Ha]; unfold zwin, RG_SZ, W_of, TOP_FRAME, LIB_STACK in *; cbn [fst snd]; lia. }
      pose proof TI2 as TI2'. destruct TI2' as [AI2 _ _ _ SX2 RC2' OSX2 EF2 DEFW2 FR2].
      assert (DW2 : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M2 a k).
      { intros a k H1 H2 i Hi. pose proof (DEFW2 (a + i - (sp - LIB_STACK)) ltac:(lia)) as D. replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia. exact D. }
      assert (Q2' : getr R2 2%bv = Z_to_bv 64 (sp - 2576)) by (rewrite (KP2 2%bv) by (clear; inl); exact G2).

      pose (E := Eseed R2 [Z_to_bv 64 (sp - 2576)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M2 []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into R3 end.
      rreg HRr 1%bv T1. rreg HRr 2%bv T2. rreg HRr 10%bv T10.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Ts.
      clear HRr HR HK. rewrite w_add in T10 by lia.
      assert (Hal8 : (sp - 2576 + 40) mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (sp - 2576) 16 ltac:(lia)) Hsp16') as [k Hk]. rewrite Hk. replace (k * 16 + 40) with ((2 * k + 5) * 8) by lia. apply Z_mod_mult. }
      destruct (RGE fx M2 R3 (sp - 2576) T_GTE_RET (sp - 2576 + 40) RC2 ltac:(lia) ltac:(unfold RG_SZ; lia) SEED2
                 ltac:(intros a Ha; unfold zwin, RG_SZ in *; lia)
                 ltac:(apply stack_room_of_defined; [lia | lia | lia | apply DW2; lia]) ltac:(lia) ltac:(lia) Hsp16' ltac:(lia) Hal8
                 ltac:(apply bv_eq; vm_compute; reflexivity) T1 T2 T10)
        as (R4 & M4 & MSg & KP4 & Qenv & Hmd4 & FE4 & HG4 & RC4).
      rewrite Erg in MSg.
      eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact MSg |].
      assert (TI4 : TopS1Ctx.tinv MI ST A0 s R0 M0 model0 sp ret A0 M4 model0).
      { apply (tinv_store C A0 M2 model0 M4 _ TI2 FE4); [| exact HG4]. intros a [Ha | Ha]; unfold zwin, RG_SZ, W_of, TOP_FRAME, LIB_STACK in *; cbn [fst snd]; lia. }
      apply (st_ctx M4 model0 R4 TI4).
      + unfold TopS1Ctx.tregs. rewrite !(KP4 _) by (clear; inl). rewrite T2, !Ts by inl. rewrite !(KP2 _) by (clear; inl). rewrite !Gs by inl. unfold TOP_FRAME.
        split; [reflexivity|]. split; [exact Hgp|]. split; [exact Htp|]. intros r Hr.
        rewrite (KP4 r) by (revert Hr; clear; intros Hr; cbn in Hr; unfold callee_saved; cbn; intuition (subst; tauto)).
        rewrite Ts by (in_sub Hr). rewrite (KP2 r) by (revert Hr; clear; intros Hr; cbn in Hr; unfold callee_saved; cbn; intuition (subst; tauto)). rewrite Gs by (in_sub Hr). reflexivity.
      + exact Qenv.
      + rewrite (KP4 9%bv) by (clear; inl). rewrite Ts by inl. rewrite (KP2 9%bv) by (clear; inl). exact G9.
      + rewrite (KP4 18%bv) by (clear; inl). rewrite Ts by inl. rewrite (KP2 18%bv) by (clear; inl). exact G18.
      + lia.
      + rewrite <- RDM1. rewrite <- (rdn_agree_win SEGS M1 M2 p (Z.to_nat n)); [| lia | lia | intros a Ha; unfold zwin in Ha; apply FE2; rewrite u64_of_Z by lia; unfold zwin, RG_SZ; lia].
        apply (rdn_agree_win SEGS M2 M4 p (Z.to_nat n)); [lia | lia |]. intros a Ha. unfold zwin in Ha. apply FE4. rewrite u64_of_Z by lia. unfold zwin, RG_SZ. lia.
      + exact HpIn.
  Qed.
End Part.
End TopS1B.

Module TopS1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.DrvLibContract.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Ctx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.TopS1B.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope Z_scope.

Module Ly := S1Layout.

Section TopS1.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.

  Variables (cR : rg_consts) (cC : ctx_consts) (cV : vec_consts) (kc : prs_consts).
  Hypothesis HcR : rc_ctor cR = 0x6c080 /\ rc_gettargetenv cR = 0x6c1a0 /\ 0 <= rc_ctor_stack cR <= 1024 /\ 0 <= rc_gte_stack cR <= 1024.
  Hypothesis HcC : cc_create cC = 0x65eac /\ cc_destroy cC = 0x65f04 /\ 0 <= cc_stack cC <= 1024.
  Hypothesis HcV : vc_entry cV = 0x65bd0 /\ 0 <= vc_stack cV <= 1024.
  Hypothesis Hkc : kc_parse kc = 0x660f8 /\ 0 <= kc_po_stack kc <= 32768.

  Hypothesis MSTK : 0 <= MALLOC_STACK MI <= 16384.
  Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
  Hypothesis HBIG : BIG MI = 131052.
  Hypothesis RB : round_big_law MI.
  Hypothesis HEAPOWN : forall A M model a, ainv MI A M model -> 0 < a < alloc_ceiling -> ~ in_ranges (ly_img Ly.L) a ->
      (forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k)) -> owned MI A a.

  Hypothesis RGC  : rg_ctor_stmt SEGS Ly.L cR.
  Hypothesis RGE  : rg_gettargetenv_stmt SEGS Ly.L cR.
  Hypothesis CTXC : ctx_create_stmt SEGS Ly.L MI ST cC.
  Hypothesis CTXD : ctx_destroy_stmt SEGS Ly.L MI ST cC.
  Hypothesis VRES : vec32_resize_stmt SEGS Ly.L MI ST cV.
  Hypothesis DEL  : op_delete_stmt SEGS Ly.L MI DEL1 (MALLOC_STACK MI).
  Hypothesis PARSE : binary_parse_stmt SEGS Ly.L MI ST kc.

  Lemma budget_ok : forall (A : AS MI) (lv : list (Z * Z)) (b nw : Z),
      caps MI A = lib_caps -> bigcap MI A = LIB_BIGCAP ->
      (length lv <= 3)%nat -> (forall q k, In (q, k) lv -> 0 < k <= 2 ^ 26) ->
      Permutation (live MI A) ((if nw =? 0 then [] else [(b, 4 * nw)]) ++ lv) ->
      0 <= nw < 2 ^ 24 ->
      pm_budget SEGS Ly.L MI A nw.
  Proof using AC MI HNMAX HBIG RB.
    intros A lv b nw HC HB Hlen Hsz PERM Hnw.
    assert (Hlen4 : (length (live MI A) <= 4)%nat).
    { rewrite (Permutation_length PERM), length_app. destruct (nw =? 0); cbn [length]; lia. }
    assert (Hcnt : forall c, 0 <= count_class_f (size_class MI) (BIG MI) (live MI A) c <= 4).
    { intros c. pose proof (count_class_le_length (size_class MI) (BIG MI) (live MI A) c). lia. }
    assert (Hin : forall q k, In (q, k) (live MI A) -> 0 <= k <= 2 ^ 26).
    { intros q k Hk. apply (Permutation_in _ PERM) in Hk. apply in_app_iff in Hk. destruct Hk as [Hk | Hk].
      - destruct (Z.eqb_spec nw 0); [destruct Hk|]. destruct Hk as [E|[]]. injection E; intros <- <-. lia.
      - pose proof (Hsz q k Hk). lia. }
    assert (Hbb : 0 <= big_bytes_f (round_big MI) (BIG MI) (live MI A) <= 4 * (2 ^ 26 + 4116)).
    { destruct (big_bytes_le (round_big MI) (BIG MI) (live MI A) (2 ^ 26 + 4116)) as [H1 H2].
      - intros q k Hk. pose proof (Hin q k Hk). destruct (Z.leb_spec (BIG MI) k); [pose proof (RB k ltac:(lia)); lia | lia].
      - lia.
      - split; [exact H1|]. etransitivity; [exact H2|]. nia. }
    pose proof (Z.mul_div_le nw 2 ltac:(lia)). pose proof (Z.mul_div_le nw 3 ltac:(lia)).
    pose proof (Z.div_pos nw 2 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos nw 3 ltac:(lia) ltac:(lia)).
    unfold pm_budget, PM_SMALL_SLACK, PM_NODES, PM_BIG, CAP_SMALL, CAP_NODE, LIB_BIGCAP in *.
    split; [exact HC|]. split; [exact HB|]. split; [exact HNMAX|]. split; [exact Hnw|].
    split; [intros c Hc; pose proof (Hcnt c); lia|].
    split; [intros c Hc; pose proof (Hcnt c); lia|].
    lia.
  Qed.

  Theorem lib_top_S1 :
    lib_call_stmt SEGS Ly.L MI ST LLVM_ENTRY EMPTY_OBJ LIB_STACK lib_caps LIB_BIGCAP TD_LOCALE GLOBAL_LOCALE.
  Proof using AC MI ST cR cC cV kc HcR HcC HcV Hkc MSTK HNMAX HBIG RB HEAPOWN RGC RGE CTXC CTXD VRES DEL PARSE.
    intros fx A s R M model sp ret p n payload K AI MS SX SXH ROC HLOC Hosx Hesx CAPS BIGC LLEN LSZ CR Qa0 Qa1 FRM Hn Hpay Hp16 Hp RDP Hceil Hroom Hwin CONT.
    apply (top_correct MI ST cR cC cV kc fx A s R M model sp ret p n payload K).
    constructor; try assumption. exact budget_ok.
  Qed.
End TopS1.
End TopS1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec SRealizes LibIface LibBudget LibEff S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import DrvLibContract.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1TargetConsts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts Lib_RG Lib_RG2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.Lib_Ctx. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.Lib_Vec32_Resize. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import Lib_Cxx_OperatorDelete.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PrsStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop Require Import TopS1Ctx.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.TopS1.
Import ListNotations.
Open Scope Z_scope.

Section Inst.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface S1Layout.SEGS S1Layout.L.
  Variable ST : StaticsIface S1Layout.SEGS S1Layout.L.
  Hypothesis HC : mi_consts_ok S1Layout.SEGS S1Layout.L MI.
  Hypothesis NEW : new_rule_stmt S1Layout.SEGS S1Layout.L MI ST (NEW_STACK S1Layout.SEGS S1Layout.L MI).
  Hypothesis HEAPOWN : forall A M model a, ainv MI A M model -> 0 < a < alloc_ceiling -> ~ in_ranges (ly_img S1Layout.L) a ->
      (forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k)) -> owned MI A a.
  Variable kc : prs_consts.
  Hypothesis Hkc : kc_parse kc = 0x660f8 /\ 0 <= kc_po_stack kc <= 32768.
  Hypothesis PARSE : binary_parse_stmt S1Layout.SEGS S1Layout.L MI ST kc.

  Lemma round_up_pg_bounds : forall x, x <= mng_round_up_pg x < x + 4096.
  Proof using AC.
    intros x. unfold mng_round_up_pg, MNG_PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
    change 4096 with (2 ^ 12). pose proof (Z.mod_pos_bound (- x) (2 ^ 12) ltac:(lia)). lia.
  Qed.
  Lemma rb_of_consts : round_big_law MI.
  Proof using AC MI HC.
    intros n Hn. rewrite (mc_round_big _ _ _ HC n). unfold mng_round_big, MNG_IB, MNG_UNIT.
    pose proof (round_up_pg_bounds (n + 4 + 16)). lia.
  Qed.

  Theorem lib_top_S1_inst :
    lib_call_stmt S1Layout.SEGS S1Layout.L MI ST S1TargetConsts.LLVM_ENTRY S1TargetConsts.EMPTY_OBJ LIB_STACK lib_caps LIB_BIGCAP
                  S1TargetConsts.TD_LOCALE S1TargetConsts.GLOBAL_LOCALE.
  Proof using AC MI ST HC NEW HEAPOWN kc Hkc PARSE.
    assert (MSTK : 0 <= MALLOC_STACK MI <= 16384) by (rewrite (mc_stack _ _ _ HC); unfold MNG_MALLOC_STACK; lia).
    assert (M0 : 0 <= MALLOC_STACK MI) by lia.
    assert (HNMAX : LIB_NMAX <= NMAX MI) by (rewrite (mc_nmax _ _ _ HC); unfold MNG_NMAX; lia).
    assert (HcR : rc_ctor cRG = 0x6c080 /\ rc_gettargetenv cRG = 0x6c1a0 /\ 0 <= rc_ctor_stack cRG <= 1024 /\ 0 <= rc_gte_stack cRG <= 1024) by (cbn; lia).
    assert (HcC : cc_create cS1 = 0x65eac /\ cc_destroy cS1 = 0x65f04 /\ 0 <= cc_stack cS1 <= 1024) by (cbn; lia).
    assert (HcV : vc_entry c65b2c = 0x65bd0 /\ 0 <= vc_stack c65b2c <= 1024) by (cbn; lia).
    exact (lib_top_S1 MI ST cRG cS1 c65b2c kc HcR HcC HcV Hkc
             MSTK HNMAX (mc_big _ _ _ HC) rb_of_consts HEAPOWN
             rg_ctor_6bfdc_spec rg_gettargetenv_6c0fc_spec
             (ctx_create_65e08_spec MI ST M0 NEW) (ctx_destroy_65e60_spec MI ST M0)
             (vec32_resize_65b2c_spec MI ST M0 NEW) (op_delete1_spec MI) PARSE).
  Qed.
End Inst.
