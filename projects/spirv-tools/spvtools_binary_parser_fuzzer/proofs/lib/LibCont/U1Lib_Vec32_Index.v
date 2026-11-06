(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_65ee8_65f2c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65ee8 : bv 32 := 0x00053603.
Lemma F_65ee8 : fetch_word Ubsan.M.loaded_segments (0x65f28 : word) = Some W_65ee8.
Proof. vm_refl. Qed.
Lemma D_65ee8 : decode_any W_65ee8 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eec : bv 32 := 0x00259513.
Lemma F_65eec : fetch_word Ubsan.M.loaded_segments (0x65f2c : word) = Some W_65eec.
Proof. vm_refl. Qed.
Lemma D_65eec : decode_any W_65eec = Some (ShiftImm ALU_SLL 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ef0 : bv 32 := 0x00a60533.
Lemma F_65ef0 : fetch_word Ubsan.M.loaded_segments (0x65f30 : word) = Some W_65ef0.
Proof. vm_refl. Qed.
Lemma D_65ef0 : decode_any W_65ef0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ef4 : bv 32 := 0x00c036b3.
Lemma F_65ef4 : fetch_word Ubsan.M.loaded_segments (0x65f34 : word) = Some W_65ef4.
Proof. vm_refl. Qed.
Lemma D_65ef4 : decode_any W_65ef4 = Some (Op ALU_SLTU 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ef8 : bv 32 := 0x00153713.
Lemma F_65ef8 : fetch_word Ubsan.M.loaded_segments (0x65f38 : word) = Some W_65ef8.
Proof. vm_refl. Qed.
Lemma D_65ef8 : decode_any W_65ef8 = Some (OpImm ALU_SLTU 14 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65efc : bv 32 := 0x02e68663.
Lemma F_65efc : fetch_word Ubsan.M.loaded_segments (0x65f3c : word) = Some W_65efc.
Proof. vm_refl. Qed.
Lemma D_65efc : decode_any W_65efc = Some (Branch BC_EQ 13 14 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f00 : bv 32 := 0x00100693.
Lemma F_65f00 : fetch_word Ubsan.M.loaded_segments (0x65f40 : word) = Some W_65f00.
Proof. vm_refl. Qed.
Lemma D_65f00 : decode_any W_65f00 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f04 : bv 32 := 0x03d69693.
Lemma F_65f04 : fetch_word Ubsan.M.loaded_segments (0x65f44 : word) = Some W_65f04.
Proof. vm_refl. Qed.
Lemma D_65f04 : decode_any W_65f04 = Some (ShiftImm ALU_SLL 13 13 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f08 : bv 32 := 0x00d585b3.
Lemma F_65f08 : fetch_word Ubsan.M.loaded_segments (0x65f48 : word) = Some W_65f08.
Proof. vm_refl. Qed.
Lemma D_65f08 : decode_any W_65f08 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f0c : bv 32 := 0x03e5d593.
Lemma F_65f0c : fetch_word Ubsan.M.loaded_segments (0x65f4c : word) = Some W_65f0c.
Proof. vm_refl. Qed.
Lemma D_65f0c : decode_any W_65f0c = Some (ShiftImm ALU_SRL 11 11 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f10 : bv 32 := 0x00059c63.
Lemma F_65f10 : fetch_word Ubsan.M.loaded_segments (0x65f50 : word) = Some W_65f10.
Proof. vm_refl. Qed.
Lemma D_65f10 : decode_any W_65f10 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f14 : bv 32 := 0x00c56a63.
Lemma F_65f14 : fetch_word Ubsan.M.loaded_segments (0x65f54 : word) = Some W_65f14.
Proof. vm_refl. Qed.
Lemma D_65f14 : decode_any W_65f14 = Some (Branch BC_LTU 10 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f18 : bv 32 := 0x00060863.
Lemma F_65f18 : fetch_word Ubsan.M.loaded_segments (0x65f58 : word) = Some W_65f18.
Proof. vm_refl. Qed.
Lemma D_65f18 : decode_any W_65f18 = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f1c : bv 32 := 0x00357593.
Lemma F_65f1c : fetch_word Ubsan.M.loaded_segments (0x65f5c : word) = Some W_65f1c.
Proof. vm_refl. Qed.
Lemma D_65f1c : decode_any W_65f1c = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f20 : bv 32 := 0x00059463.
Lemma F_65f20 : fetch_word Ubsan.M.loaded_segments (0x65f60 : word) = Some W_65f20.
Proof. vm_refl. Qed.
Lemma D_65f20 : decode_any W_65f20 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f24 : bv 32 := 0x00008067.
Lemma F_65f24 : fetch_word Ubsan.M.loaded_segments (0x65f64 : word) = Some W_65f24.
Proof. vm_refl. Qed.
Lemma D_65f24 : decode_any W_65f24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f28 : bv 32 := 0xc0001073.

End U1_code_65ee8_65f2c.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts U1Facts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_Index.U1_code_65ee8_65f2c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.
Ltac zval := gres; pin; imm_norm; apply bv_eq; unfold v_add, v_addi, v_sub, v_slli;
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; imm_norm;
  rewrite ?Z.add_0_r, ?Z.sub_0_r, ?Z.add_0_l, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Z.mod_mod by lia;
  first [ reflexivity | f_equal; lia | rewrite !Z.mod_small by lia; lia ].

Lemma step_sltu_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Ltac stepsltu F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_sltu_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].
Lemma snez_Z : forall b, 0 < b < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof. intros b Hb. unfold v_sltu. rewrite c_ltu_Z by lia. destruct (Z.ltb_spec 0 b); [reflexivity|lia]. Qed.

Section Index.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.

  Definition u1c65e84 : vec_consts := {| vc_entry := 0x65f28; vc_stack := 0 |}.

  Lemma sltiu_1_Z : forall a, 0 <= a < 2 ^ 64 -> v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 (if a =? 0 then 1 else 0).
  Proof using.
    intros a Ha. unfold v_sltiu. rewrite u64_of_Z by lia. change (bv_wrap 64 1) with 1.
    destruct (Z.eqb_spec a 0); [subst; reflexivity|]. destruct (Z.ltb_spec a 1); [lia|reflexivity].
  Qed.

  Theorem vec32_index_65e84_spec : vec32_index_stmt SEGS Ly.L MI u1c65e84.
  Proof using AC MI.
    intros fx A M rom R ret v b cap i xs VEC Hi Hret Hra Ha0 Ha1. cbn [vc_entry u1c65e84].
    destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2 & FE).
    pose proof (ai_nmax_bound MI) as HNM.
    destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
    unfold fld in F0.
    eexists. split; [|split].
    - norm_pc.
      ld_step F_65ee8 D_65ee8 (word_to_le_bytes 8 (Z_to_bv 64 b)) (Z_to_bv 64 b) ltac:(rdn_fix F0) ltac:(b2z8).
      stepiv F_65eec D_65eec (Z_to_bv 64 (4 * i)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
      stepiv F_65ef0 D_65ef0 (Z_to_bv 64 (b + 4 * i)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
      stepsltu F_65ef4 D_65ef4 (Z_to_bv 64 1) ltac:(gres; pin; apply snez_Z; lia).
      stepiv F_65ef8 D_65ef8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (b + 4 * i) 0); [lia|reflexivity]).
      stepb_ft F_65efc D_65efc ltac:(vm_compute; reflexivity).
      snl F_65f00 D_65f00. snl F_65f04 D_65f04.
      stepiv F_65f08 D_65f08 (Z_to_bv 64 (i + 2 ^ 61)) ltac:(zval).
      stepiv F_65f0c D_65f0c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_65f10 D_65f10 ltac:(apply c_eq_refl).
      stepb_ft F_65f14 D_65f14 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepb_ft F_65f18 D_65f18 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
      stepiv F_65f1c D_65f1c (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia;
              change (2 ^ 2) with 4; replace (b + 4 * i) with ((b / 16 * 4 + i) * 4) by (pose proof (Z.div_mod b 16 ltac:(lia)); lia); apply Z_mod_mult).
      stepb_ft F_65f20 D_65f20 ltac:(apply c_eq_refl).
      stepjr F_65f24 D_65f24 ret ltac:(gres; exact Hra).
      lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' _ _ _) => unify r' r;
        replace pc with ret by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
    - intros r Hr; unfold callee_saved in Hr.
      repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption] |]). destruct Hr.
    - gres. reflexivity.
  Qed.
End Index.
