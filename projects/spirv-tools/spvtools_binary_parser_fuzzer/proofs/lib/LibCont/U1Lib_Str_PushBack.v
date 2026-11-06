(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_e2f6c_e2fc4.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e2f6c : bv 32 := 0x08b50663.
Lemma F_e2f6c : fetch_word Ubsan.M.loaded_segments (0xe2fa0 : word) = Some W_e2f6c.
Proof. vm_refl. Qed.
Lemma D_e2f6c : decode_any W_e2f6c = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f70 : bv 32 := 0x00a606b3.
Lemma F_e2f70 : fetch_word Ubsan.M.loaded_segments (0xe2fa4 : word) = Some W_e2f70.
Proof. vm_refl. Qed.
Lemma D_e2f70 : decode_any W_e2f70 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f74 : bv 32 := 0x00161713.
Lemma F_e2f74 : fetch_word Ubsan.M.loaded_segments (0xe2fa8 : word) = Some W_e2f74.
Proof. vm_refl. Qed.
Lemma D_e2f74 : decode_any W_e2f74 = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f78 : bv 32 := 0x40d586b3.
Lemma F_e2f78 : fetch_word Ubsan.M.loaded_segments (0xe2fac : word) = Some W_e2f78.
Proof. vm_refl. Qed.
Lemma D_e2f78 : decode_any W_e2f78 = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f7c : bv 32 := 0x40e00733.
Lemma F_e2f7c : fetch_word Ubsan.M.loaded_segments (0xe2fb0 : word) = Some W_e2f7c.
Proof. vm_refl. Qed.
Lemma D_e2f7c : decode_any W_e2f7c = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f80 : bv 32 := 0x04d77063.
Lemma F_e2f80 : fetch_word Ubsan.M.loaded_segments (0xe2fb4 : word) = Some W_e2f80.
Proof. vm_refl. Qed.
Lemma D_e2f80 : decode_any W_e2f80 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2fc0 : bv 32 := 0xba9ff06f.
Lemma F_e2fc0 : fetch_word Ubsan.M.loaded_segments (0xe2ff4 : word) = Some W_e2fc0.
Proof. vm_refl. Qed.
Lemma D_e2fc0 : decode_any W_e2fc0 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.
End U1_code_e2f6c_e2fc4.

Module U1Lib_Musl_Memmove.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack.U1_code_e2f6c_e2fc4.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition MEMMOVE : Z := 0xe2fa0.

Section Memmove.
  Context {fx : FPState}.

  Lemma mod_neg_small : forall a m, (0 < m -> - m <= a < 0 -> a mod m = a + m)%Z.
  Proof using.
    intros a m Hm Ha. rewrite <- (Z.mod_add a 1 m) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma memmove_test : forall d s n, (0 <= d -> 0 <= s -> 0 < n -> s + n < 2^64 -> d + n < 2^64 ->
    (d + n <= s \/ s + n <= d) ->
    ((0 - (Z.shiftl n 1) mod 2^64) mod 2^64 <? ((s - ((n + d) mod 2^64)) mod 2^64)) = false)%Z.
  Proof using.
    intros d s n Hd Hs Hn Hsn Hdn Hdisj.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z.
    rewrite (Z.mod_small (n*2)) by lia. rewrite (Z.mod_small (n + d)) by lia.
    rewrite mod_neg_small by lia.
    apply Z.ltb_ge.
    destruct Hdisj as [A|B].
    - rewrite Z.mod_small by lia. lia.
    - rewrite mod_neg_small by lia. lia.
  Qed.

  Theorem u1_memmove_spec : memmove_stmt SEGS MEMMOVE.
  Proof using.
    intros fx' mem0 dst src n bs rom regs ret MC Hn Hret H1 H10 H11 H12.
    destruct MC as [Hn0 Hlen Hsrc Hdst Hdisj Hnws Hnwd].
    pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.

    eapply (runs_trans SEGS _ (fun r => mkst r u1_memcpy_entry mem0 rom)
             (fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
                       /\ keeps regs r)).
    - eexists. split.
      + unfold MEMMOVE. norm_pc.
        stepb_ft F_e2f6c D_e2f6c ltac:(rewrite H10, H11; apply c_eq_neq; lia).
        stepn F_e2f70 D_e2f70.
        stepn F_e2f74 D_e2f74.
        stepn F_e2f78 D_e2f78.
        stepn F_e2f7c D_e2f7c.
        stepb_tk F_e2f80 D_e2f80 ltac:(idtac).
        { rewrite H10, H11, H12. unfold c_ltu, bv_ltu, v_sub, v_add, v_slli.
          rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small n), Z.mod_0_l by lia.
          apply memmove_test; lia. }
        stepj F_e2fc0 D_e2fc0. apply mst_refl.
      + cbv beta. gres. repeat split; try assumption.
        repeat (apply keeps_upd; [| cbv; intuition discriminate]). apply keeps_refl.
    - cbv beta. intros r1 (R1 & R10 & R11 & R12 & KR).
      destruct (u1_memcpy mem0 dst src n bs rom r1 ret (MCH _ _ _ _ _ _ Hn0 Hlen Hsrc Hdst Hdisj Hnws Hnwd)
                  Hret R1 R10 R11 R12) as (r2 & RUN & K2).
      exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.
End Memmove.
End U1Lib_Musl_Memmove.

Module U1_code_8d198_8d2e4.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8d198 : bv 32 := 0xfc010113.
Lemma F_8d198 : fetch_word Ubsan.M.loaded_segments (0x8d1d8 : word) = Some W_8d198.
Proof. vm_refl. Qed.
Lemma D_8d198 : decode_any W_8d198 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d19c : bv 32 := 0x02113c23.
Lemma F_8d19c : fetch_word Ubsan.M.loaded_segments (0x8d1dc : word) = Some W_8d19c.
Proof. vm_refl. Qed.
Lemma D_8d19c : decode_any W_8d19c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1a0 : bv 32 := 0x02813823.
Lemma F_8d1a0 : fetch_word Ubsan.M.loaded_segments (0x8d1e0 : word) = Some W_8d1a0.
Proof. vm_refl. Qed.
Lemma D_8d1a0 : decode_any W_8d1a0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1a4 : bv 32 := 0x02913423.
Lemma F_8d1a4 : fetch_word Ubsan.M.loaded_segments (0x8d1e4 : word) = Some W_8d1a4.
Proof. vm_refl. Qed.
Lemma D_8d1a4 : decode_any W_8d1a4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1a8 : bv 32 := 0x03213023.
Lemma F_8d1a8 : fetch_word Ubsan.M.loaded_segments (0x8d1e8 : word) = Some W_8d1a8.
Proof. vm_refl. Qed.
Lemma D_8d1a8 : decode_any W_8d1a8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1ac : bv 32 := 0x01313c23.
Lemma F_8d1ac : fetch_word Ubsan.M.loaded_segments (0x8d1ec : word) = Some W_8d1ac.
Proof. vm_refl. Qed.
Lemma D_8d1ac : decode_any W_8d1ac = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1b0 : bv 32 := 0x01413823.
Lemma F_8d1b0 : fetch_word Ubsan.M.loaded_segments (0x8d1f0 : word) = Some W_8d1b0.
Proof. vm_refl. Qed.
Lemma D_8d1b0 : decode_any W_8d1b0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1b4 : bv 32 := 0x01513423.
Lemma F_8d1b4 : fetch_word Ubsan.M.loaded_segments (0x8d1f4 : word) = Some W_8d1b4.
Proof. vm_refl. Qed.
Lemma D_8d1b4 : decode_any W_8d1b4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1b8 : bv 32 := 0x01613023.
Lemma F_8d1b8 : fetch_word Ubsan.M.loaded_segments (0x8d1f8 : word) = Some W_8d1b8.
Proof. vm_refl. Qed.
Lemma D_8d1b8 : decode_any W_8d1b8 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1bc : bv 32 := 0x00050493.
Lemma F_8d1bc : fetch_word Ubsan.M.loaded_segments (0x8d1fc : word) = Some W_8d1bc.
Proof. vm_refl. Qed.
Lemma D_8d1bc : decode_any W_8d1bc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1c0 : bv 32 := 0x00054603.
Lemma F_8d1c0 : fetch_word Ubsan.M.loaded_segments (0x8d200 : word) = Some W_8d1c0.
Proof. vm_refl. Qed.
Lemma D_8d1c0 : decode_any W_8d1c0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1c4 : bv 32 := 0x00167513.
Lemma F_8d1c4 : fetch_word Ubsan.M.loaded_segments (0x8d204 : word) = Some W_8d1c4.
Proof. vm_refl. Qed.
Lemma D_8d1c4 : decode_any W_8d1c4 = Some (OpImm ALU_AND 10 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1c8 : bv 32 := 0x00058413.
Lemma F_8d1c8 : fetch_word Ubsan.M.loaded_segments (0x8d208 : word) = Some W_8d1c8.
Proof. vm_refl. Qed.
Lemma D_8d1c8 : decode_any W_8d1c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1cc : bv 32 := 0x02051063.
Lemma F_8d1cc : fetch_word Ubsan.M.loaded_segments (0x8d20c : word) = Some W_8d1cc.
Proof. vm_refl. Qed.
Lemma D_8d1cc : decode_any W_8d1cc = Some (Branch BC_NE 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1d0 : bv 32 := 0x02c00513.
Lemma F_8d1d0 : fetch_word Ubsan.M.loaded_segments (0x8d210 : word) = Some W_8d1d0.
Proof. vm_refl. Qed.
Lemma D_8d1d0 : decode_any W_8d1d0 = Some (OpImm ALU_ADD 10 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1d4 : bv 32 := 0x06a61263.
Lemma F_8d1d4 : fetch_word Ubsan.M.loaded_segments (0x8d214 : word) = Some W_8d1d4.
Proof. vm_refl. Qed.
Lemma D_8d1d4 : decode_any W_8d1d4 = Some (Branch BC_NE 12 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1d8 : bv 32 := 0x00148913.
Lemma F_8d1d8 : fetch_word Ubsan.M.loaded_segments (0x8d218 : word) = Some W_8d1d8.
Proof. vm_refl. Qed.
Lemma D_8d1d8 : decode_any W_8d1d8 = Some (OpImm ALU_ADD 18 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1dc : bv 32 := 0x03000993.
Lemma F_8d1dc : fetch_word Ubsan.M.loaded_segments (0x8d21c : word) = Some W_8d1dc.
Proof. vm_refl. Qed.
Lemma D_8d1dc : decode_any W_8d1dc = Some (OpImm ALU_ADD 19 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1e0 : bv 32 := 0x01600513.
Lemma F_8d1e0 : fetch_word Ubsan.M.loaded_segments (0x8d220 : word) = Some W_8d1e0.
Proof. vm_refl. Qed.
Lemma D_8d1e0 : decode_any W_8d1e0 = Some (OpImm ALU_ADD 10 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1e4 : bv 32 := 0x00150a93.
Lemma F_8d1e4 : fetch_word Ubsan.M.loaded_segments (0x8d224 : word) = Some W_8d1e4.
Proof. vm_refl. Qed.
Lemma D_8d1e4 : decode_any W_8d1e4 = Some (OpImm ALU_ADD 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1e8 : bv 32 := 0x0680006f.
Lemma F_8d1e8 : fetch_word Ubsan.M.loaded_segments (0x8d228 : word) = Some W_8d1e8.
Proof. vm_refl. Qed.
Lemma D_8d1e8 : decode_any W_8d1e8 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1ec : bv 32 := 0x0004b503.
Lemma F_8d1ec : fetch_word Ubsan.M.loaded_segments (0x8d22c : word) = Some W_8d1ec.
Proof. vm_refl. Qed.
Lemma D_8d1ec : decode_any W_8d1ec = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1f0 : bv 32 := 0x0084ba03.
Lemma F_8d1f0 : fetch_word Ubsan.M.loaded_segments (0x8d230 : word) = Some W_8d1f0.
Proof. vm_refl. Qed.
Lemma D_8d1f0 : decode_any W_8d1f0 = Some (Load SZ8 true 20 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1f4 : bv 32 := 0xffe57a93.
Lemma F_8d1f4 : fetch_word Ubsan.M.loaded_segments (0x8d234 : word) = Some W_8d1f4.
Proof. vm_refl. Qed.
Lemma D_8d1f4 : decode_any W_8d1f4 = Some (OpImm ALU_AND 21 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1f8 : bv 32 := 0xfffa8513.
Lemma F_8d1f8 : fetch_word Ubsan.M.loaded_segments (0x8d238 : word) = Some W_8d1f8.
Proof. vm_refl. Qed.
Lemma D_8d1f8 : decode_any W_8d1f8 = Some (OpImm ALU_ADD 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d1fc : bv 32 := 0x08aa1863.
Lemma F_8d1fc : fetch_word Ubsan.M.loaded_segments (0x8d23c : word) = Some W_8d1fc.
Proof. vm_refl. Qed.
Lemma D_8d1fc : decode_any W_8d1fc = Some (Branch BC_NE 20 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d200 : bv 32 := 0xff800593.
Lemma F_8d200 : fetch_word Ubsan.M.loaded_segments (0x8d240 : word) = Some W_8d200.
Proof. vm_refl. Qed.
Lemma D_8d200 : decode_any W_8d200 = Some (OpImm ALU_ADD 11 0 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d204 : bv 32 := 0x0cba8e63.
Lemma F_8d204 : fetch_word Ubsan.M.loaded_segments (0x8d244 : word) = Some W_8d204.
Proof. vm_refl. Qed.
Lemma D_8d204 : decode_any W_8d204 = Some (Branch BC_EQ 21 11 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d208 : bv 32 := 0x0104b903.
Lemma F_8d208 : fetch_word Ubsan.M.loaded_segments (0x8d248 : word) = Some W_8d208.
Proof. vm_refl. Qed.
Lemma D_8d208 : decode_any W_8d208 = Some (Load SZ8 true 18 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d20c : bv 32 := 0xfe500593.
Lemma F_8d20c : fetch_word Ubsan.M.loaded_segments (0x8d24c : word) = Some W_8d20c.
Proof. vm_refl. Qed.
Lemma D_8d20c : decode_any W_8d20c = Some (OpImm ALU_ADD 11 0 4069, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d210 : bv 32 := 0x0015d593.
Lemma F_8d210 : fetch_word Ubsan.M.loaded_segments (0x8d250 : word) = Some W_8d210.
Proof. vm_refl. Qed.
Lemma D_8d210 : decode_any W_8d210 = Some (ShiftImm ALU_SRL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d214 : bv 32 := 0x02a5ec63.
Lemma F_8d214 : fetch_word Ubsan.M.loaded_segments (0x8d254 : word) = Some W_8d214.
Proof. vm_refl. Qed.
Lemma D_8d214 : decode_any W_8d214 = Some (Branch BC_LTU 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d218 : bv 32 := 0x00151593.
Lemma F_8d218 : fetch_word Ubsan.M.loaded_segments (0x8d258 : word) = Some W_8d218.
Proof. vm_refl. Qed.
Lemma D_8d218 : decode_any W_8d218 = Some (ShiftImm ALU_SLL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d21c : bv 32 := 0x0075e993.
Lemma F_8d21c : fetch_word Ubsan.M.loaded_segments (0x8d25c : word) = Some W_8d21c.
Proof. vm_refl. Qed.
Lemma D_8d21c : decode_any W_8d21c = Some (OpImm ALU_OR 19 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d220 : bv 32 := 0x01700593.
Lemma F_8d220 : fetch_word Ubsan.M.loaded_segments (0x8d260 : word) = Some W_8d220.
Proof. vm_refl. Qed.
Lemma D_8d220 : decode_any W_8d220 = Some (OpImm ALU_ADD 11 0 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d224 : bv 32 := 0x0ab99463.
Lemma F_8d224 : fetch_word Ubsan.M.loaded_segments (0x8d264 : word) = Some W_8d224.
Proof. vm_refl. Qed.
Lemma D_8d224 : decode_any W_8d224 = Some (Branch BC_NE 19 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d238 : bv 32 := 0x00165a13.
Lemma F_8d238 : fetch_word Ubsan.M.loaded_segments (0x8d278 : word) = Some W_8d238.
Proof. vm_refl. Qed.
Lemma D_8d238 : decode_any W_8d238 = Some (ShiftImm ALU_SRL 20 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d23c : bv 32 := 0x00148513.
Lemma F_8d23c : fetch_word Ubsan.M.loaded_segments (0x8d27c : word) = Some W_8d23c.
Proof. vm_refl. Qed.
Lemma D_8d23c : decode_any W_8d23c = Some (OpImm ALU_ADD 10 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d240 : bv 32 := 0x00260613.
Lemma F_8d240 : fetch_word Ubsan.M.loaded_segments (0x8d280 : word) = Some W_8d240.
Proof. vm_refl. Qed.
Lemma D_8d240 : decode_any W_8d240 = Some (OpImm ALU_ADD 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d244 : bv 32 := 0x00c48023.
Lemma F_8d244 : fetch_word Ubsan.M.loaded_segments (0x8d284 : word) = Some W_8d244.
Proof. vm_refl. Qed.
Lemma D_8d244 : decode_any W_8d244 = Some (Store SZ1 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d248 : bv 32 := 0x0500006f.
Lemma F_8d248 : fetch_word Ubsan.M.loaded_segments (0x8d288 : word) = Some W_8d248.
Proof. vm_refl. Qed.
Lemma D_8d248 : decode_any W_8d248 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d250 : bv 32 := 0x00050a13.
Lemma F_8d250 : fetch_word Ubsan.M.loaded_segments (0x8d290 : word) = Some W_8d250.
Proof. vm_refl. Qed.
Lemma D_8d250 : decode_any W_8d250 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d254 : bv 32 := 0x00098513.
Lemma F_8d254 : fetch_word Ubsan.M.loaded_segments (0x8d294 : word) = Some W_8d254.
Proof. vm_refl. Qed.
Lemma D_8d254 : decode_any W_8d254 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d258 : bv 32 := 0x09d5a0ef.
Lemma F_8d258 : fetch_word Ubsan.M.loaded_segments (0x8d298 : word) = Some W_8d258.
Proof. vm_refl. Qed.
Lemma D_8d258 : decode_any W_8d258 = Some (Jal 1 370844, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d25c : bv 32 := 0x00050b13.
Lemma F_8d25c : fetch_word Ubsan.M.loaded_segments (0x8d29c : word) = Some W_8d25c.
Proof. vm_refl. Qed.
Lemma D_8d25c : decode_any W_8d25c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d260 : bv 32 := 0x00090593.
Lemma F_8d260 : fetch_word Ubsan.M.loaded_segments (0x8d2a0 : word) = Some W_8d260.
Proof. vm_refl. Qed.
Lemma D_8d260 : decode_any W_8d260 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d264 : bv 32 := 0x000a0613.
Lemma F_8d264 : fetch_word Ubsan.M.loaded_segments (0x8d2a4 : word) = Some W_8d264.
Proof. vm_refl. Qed.
Lemma D_8d264 : decode_any W_8d264 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d268 : bv 32 := 0x4f9550ef.
Lemma F_8d268 : fetch_word Ubsan.M.loaded_segments (0x8d2a8 : word) = Some W_8d268.
Proof. vm_refl. Qed.
Lemma D_8d268 : decode_any W_8d268 = Some (Jal 1 351480, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d26c : bv 32 := 0x01700513.
Lemma F_8d26c : fetch_word Ubsan.M.loaded_segments (0x8d2ac : word) = Some W_8d26c.
Proof. vm_refl. Qed.
Lemma D_8d26c : decode_any W_8d26c = Some (OpImm ALU_ADD 10 0 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d270 : bv 32 := 0x00aa8863.
Lemma F_8d270 : fetch_word Ubsan.M.loaded_segments (0x8d2b0 : word) = Some W_8d270.
Proof. vm_refl. Qed.
Lemma D_8d270 : decode_any W_8d270 = Some (Branch BC_EQ 21 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d274 : bv 32 := 0x00090513.
Lemma F_8d274 : fetch_word Ubsan.M.loaded_segments (0x8d2b4 : word) = Some W_8d274.
Proof. vm_refl. Qed.
Lemma D_8d274 : decode_any W_8d274 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d278 : bv 32 := 0x000a8593.
Lemma F_8d278 : fetch_word Ubsan.M.loaded_segments (0x8d2b8 : word) = Some W_8d278.
Proof. vm_refl. Qed.
Lemma D_8d278 : decode_any W_8d278 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d27c : bv 32 := 0xe10e20ef.
Lemma F_8d27c : fetch_word Ubsan.M.loaded_segments (0x8d2bc : word) = Some W_8d27c.
Proof. vm_refl. Qed.
Lemma D_8d27c : decode_any W_8d27c = Some (Jal 1 1975824, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d280 : bv 32 := 0x0019e513.
Lemma F_8d280 : fetch_word Ubsan.M.loaded_segments (0x8d2c0 : word) = Some W_8d280.
Proof. vm_refl. Qed.
Lemma D_8d280 : decode_any W_8d280 = Some (OpImm ALU_OR 10 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d284 : bv 32 := 0x00a4b023.
Lemma F_8d284 : fetch_word Ubsan.M.loaded_segments (0x8d2c4 : word) = Some W_8d284.
Proof. vm_refl. Qed.
Lemma D_8d284 : decode_any W_8d284 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d288 : bv 32 := 0x0164b823.
Lemma F_8d288 : fetch_word Ubsan.M.loaded_segments (0x8d2c8 : word) = Some W_8d288.
Proof. vm_refl. Qed.
Lemma D_8d288 : decode_any W_8d288 = Some (Store SZ8 9 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d28c : bv 32 := 0x0104b503.
Lemma F_8d28c : fetch_word Ubsan.M.loaded_segments (0x8d2cc : word) = Some W_8d28c.
Proof. vm_refl. Qed.
Lemma D_8d28c : decode_any W_8d28c = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d290 : bv 32 := 0x001a0593.
Lemma F_8d290 : fetch_word Ubsan.M.loaded_segments (0x8d2d0 : word) = Some W_8d290.
Proof. vm_refl. Qed.
Lemma D_8d290 : decode_any W_8d290 = Some (OpImm ALU_ADD 11 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d294 : bv 32 := 0x00b4b423.
Lemma F_8d294 : fetch_word Ubsan.M.loaded_segments (0x8d2d4 : word) = Some W_8d294.
Proof. vm_refl. Qed.
Lemma D_8d294 : decode_any W_8d294 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d298 : bv 32 := 0x01450533.
Lemma F_8d298 : fetch_word Ubsan.M.loaded_segments (0x8d2d8 : word) = Some W_8d298.
Proof. vm_refl. Qed.
Lemma D_8d298 : decode_any W_8d298 = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d29c : bv 32 := 0x00850023.
Lemma F_8d29c : fetch_word Ubsan.M.loaded_segments (0x8d2dc : word) = Some W_8d29c.
Proof. vm_refl. Qed.
Lemma D_8d29c : decode_any W_8d29c = Some (Store SZ1 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2a0 : bv 32 := 0x000500a3.
Lemma F_8d2a0 : fetch_word Ubsan.M.loaded_segments (0x8d2e0 : word) = Some W_8d2a0.
Proof. vm_refl. Qed.
Lemma D_8d2a0 : decode_any W_8d2a0 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2a4 : bv 32 := 0x03813083.
Lemma F_8d2a4 : fetch_word Ubsan.M.loaded_segments (0x8d2e4 : word) = Some W_8d2a4.
Proof. vm_refl. Qed.
Lemma D_8d2a4 : decode_any W_8d2a4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2a8 : bv 32 := 0x03013403.
Lemma F_8d2a8 : fetch_word Ubsan.M.loaded_segments (0x8d2e8 : word) = Some W_8d2a8.
Proof. vm_refl. Qed.
Lemma D_8d2a8 : decode_any W_8d2a8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2ac : bv 32 := 0x02813483.
Lemma F_8d2ac : fetch_word Ubsan.M.loaded_segments (0x8d2ec : word) = Some W_8d2ac.
Proof. vm_refl. Qed.
Lemma D_8d2ac : decode_any W_8d2ac = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2b0 : bv 32 := 0x02013903.
Lemma F_8d2b0 : fetch_word Ubsan.M.loaded_segments (0x8d2f0 : word) = Some W_8d2b0.
Proof. vm_refl. Qed.
Lemma D_8d2b0 : decode_any W_8d2b0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2b4 : bv 32 := 0x01813983.
Lemma F_8d2b4 : fetch_word Ubsan.M.loaded_segments (0x8d2f4 : word) = Some W_8d2b4.
Proof. vm_refl. Qed.
Lemma D_8d2b4 : decode_any W_8d2b4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2b8 : bv 32 := 0x01013a03.
Lemma F_8d2b8 : fetch_word Ubsan.M.loaded_segments (0x8d2f8 : word) = Some W_8d2b8.
Proof. vm_refl. Qed.
Lemma D_8d2b8 : decode_any W_8d2b8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2bc : bv 32 := 0x00813a83.
Lemma F_8d2bc : fetch_word Ubsan.M.loaded_segments (0x8d2fc : word) = Some W_8d2bc.
Proof. vm_refl. Qed.
Lemma D_8d2bc : decode_any W_8d2bc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2c0 : bv 32 := 0x00013b03.
Lemma F_8d2c0 : fetch_word Ubsan.M.loaded_segments (0x8d300 : word) = Some W_8d2c0.
Proof. vm_refl. Qed.
Lemma D_8d2c0 : decode_any W_8d2c0 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2c4 : bv 32 := 0x04010113.
Lemma F_8d2c4 : fetch_word Ubsan.M.loaded_segments (0x8d304 : word) = Some W_8d2c4.
Proof. vm_refl. Qed.
Lemma D_8d2c4 : decode_any W_8d2c4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2c8 : bv 32 := 0x00008067.
Lemma F_8d2c8 : fetch_word Ubsan.M.loaded_segments (0x8d308 : word) = Some W_8d2c8.
Proof. vm_refl. Qed.
Lemma D_8d2c8 : decode_any W_8d2c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2cc : bv 32 := 0x00198993.
Lemma F_8d2cc : fetch_word Ubsan.M.loaded_segments (0x8d30c : word) = Some W_8d2cc.
Proof. vm_refl. Qed.
Lemma D_8d2cc : decode_any W_8d2cc = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2d0 : bv 32 := 0x00c00593.
Lemma F_8d2d0 : fetch_word Ubsan.M.loaded_segments (0x8d310 : word) = Some W_8d2d0.
Proof. vm_refl. Qed.
Lemma D_8d2d0 : decode_any W_8d2d0 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d2d4 : bv 32 := 0xf0b578e3.
Lemma F_8d2d4 : fetch_word Ubsan.M.loaded_segments (0x8d314 : word) = Some W_8d2d4.
Proof. vm_refl. Qed.
Lemma D_8d2d4 : decode_any W_8d2d4 = Some (Branch BC_GEU 10 11 7952, 4%Z).
Proof. vm_refl. Qed.
End U1_code_8d198_8d2e4.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemcpyBase SumMemcpy LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts U1Facts U1Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack.U1Lib_Musl_Memmove. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack.U1_code_8d198_8d2e4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac rdA H := peel; rdn_fix H.
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.
Ltac msteps_close :=
  lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
    unify r' r; replace pc' with pc by (apply bv_eq; vm_compute; reflexivity);
    replace m' with m by reflexivity; apply mst_refl end.

Ltac peel1 := repeat first [ rewrite rdn_wbytes_out_Z by (cbn [length]; len_simpl; lia) | rewrite rdn_wbytes_out by region_side ].

Section PushBack.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition PRO_vals (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Lemma prologue : forall (fx : FPState) R M sp ret p,
    getr R 2%bv = Z_to_bv 64 sp -> getr R 1%bv = Z_to_bv 64 ret -> getr R 10%bv = Z_to_bv 64 p ->
    store_ok SEGS M (Z_to_bv 64 (sp - 64)) 64 = true -> 64 <= sp < 2 ^ 63 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x8d1d8) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd R 2%bv (Z_to_bv 64 (sp - 64))) 9%bv (Z_to_bv 64 p))
                          (Z_to_bv 64 0x8d200) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret p Hsp Hra Ha0 HOK Hsp'.
    norm_pc.
    sv F_8d198 D_8d198 (Z_to_bv 64 (sp - 64)).
    stw F_8d19c D_8d19c (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
    stw F_8d1a0 D_8d1a0 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
    stw F_8d1a4 D_8d1a4 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
    stw F_8d1a8 D_8d1a8 (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
    stw F_8d1ac D_8d1ac (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
    stw F_8d1b0 D_8d1b0 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
    stw F_8d1b4 D_8d1b4 (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
    stw F_8d1b8 D_8d1b8 (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
    sv F_8d1bc D_8d1bc (Z_to_bv 64 p).
    lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
    f_equal. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma epilogue : forall (fx : FPState) R M sp ret (x len : Z) (chv v8 v9 v18 v19 v20 v21 v22 : word),
    getr R 2%bv = Z_to_bv 64 (sp - 64) -> getr R 10%bv = Z_to_bv 64 x -> getr R 20%bv = Z_to_bv 64 len ->
    getr R 8%bv = chv ->
    64 <= sp < 2 ^ 63 -> 0 <= x -> 0 <= len -> x + len + 2 <= 2 ^ 63 -> (x + len + 2 <= sp - 64 \/ sp <= x + len) ->
    store_ok SEGS M (Z_to_bv 64 (x + len)) 2 = true ->
    rdn SEGS M (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS M (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS M (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS M (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS M (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS M (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS M (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS M (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    ret_ok (Z_to_bv 64 ret) ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x8d2d8) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                             10%bv (Z_to_bv 64 (x + len)))
                             1%bv (Z_to_bv 64 ret)) 8%bv v8) 9%bv v9) 18%bv v18) 19%bv v19) 20%bv v20) 21%bv v21) 22%bv v22)
                             2%bv (Z_to_bv 64 sp))
                          (Z_to_bv 64 ret)
                          (wbytes (wbytes M (Z_to_bv 64 (x + len)) [Z_to_bv 8 (bv_unsigned chv)])
                                  (Z_to_bv 64 (x + len + 1)) [Z_to_bv 8 0]) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret x len chv v8 v9 v18 v19 v20 v21 v22 Hsp Ha0 Hs4 Hs0 Hsp' Hx0 Hlen0 Hx1 Hdisj HOKx
           L1 L8 L9 L18 L19 L20 L21 L22 Hret.
    norm_pc.
    stepiv F_8d298 D_8d298 (Z_to_bv 64 (x + len)) ltac:(gres; rewrite Ha0, Hs4; rewrite v_add_Z by lia; reflexivity).
    stw F_8d29c D_8d29c (Z_to_bv 64 (x + len)) chv ltac:(ok_sub HOKx).
    stw F_8d2a0 D_8d2a0 (Z_to_bv 64 (x + len + 1)) (Z_to_bv 64 0) ltac:(ok_sub HOKx).
    ld_step F_8d2a4 D_8d2a4 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(peel1; rdn_fix L1) ltac:(b2z8).
    ld_step F_8d2a8 D_8d2a8 (word_to_le_bytes 8 v8) v8 ltac:(peel1; rdn_fix L8) ltac:(b2z8).
    ld_step F_8d2ac D_8d2ac (word_to_le_bytes 8 v9) v9 ltac:(peel1; rdn_fix L9) ltac:(b2z8).
    ld_step F_8d2b0 D_8d2b0 (word_to_le_bytes 8 v18) v18 ltac:(peel1; rdn_fix L18) ltac:(b2z8).
    ld_step F_8d2b4 D_8d2b4 (word_to_le_bytes 8 v19) v19 ltac:(peel1; rdn_fix L19) ltac:(b2z8).
    ld_step F_8d2b8 D_8d2b8 (word_to_le_bytes 8 v20) v20 ltac:(peel1; rdn_fix L20) ltac:(b2z8).
    ld_step F_8d2bc D_8d2bc (word_to_le_bytes 8 v21) v21 ltac:(peel1; rdn_fix L21) ltac:(b2z8).
    ld_step F_8d2c0 D_8d2c0 (word_to_le_bytes 8 v22) v22 ltac:(peel1; rdn_fix L22) ltac:(b2z8).
    sv F_8d2c4 D_8d2c4 (Z_to_bv 64 sp).
    stepjr F_8d2c8 D_8d2c8 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.
  Definition c8d144 : str_consts :=
    {| sc_push_back := 0x8d1d8; sc_resize := 0x8d60c; sc_makestring := 0x6682c;
       sc_push_stack := 64; sc_resize_stack := 80; sc_ms_stack := 128 |}.

  Theorem str_push_back_8d144_spec : str_push_back_stmt SEGS Ly.L MI ST c8d144.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret p ch m cs K.
    cbn [sc_push_back sc_push_stack c8d144]. lazy zeta.
    intros CB Ha0 Ha1 STR OBJ ROOM CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    destruct STR as (Hp0 & Hp1 & HDp & Hlen & HM & FC & FN).
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (64 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
    destruct OBJ as [PLp WINp].
    assert (WINp' : p + 24 <= sp - (64 + (16 + MALLOC_STACK MI)) \/ sp <= p).
    { destruct (Z.lt_ge_cases p sp); [left|right; lia].
      destruct (Z.lt_ge_cases (p + 24) (sp - (64 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases p (sp - (64 + (16 + MALLOC_STACK MI)))).
      - apply (WINp (sp - (64 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINp p); unfold zwin; lia. }
    clear WINp. hide WINp'.
    remember (Zlen cs) as n eqn:En. remember (str_data p m) as src eqn:Esrc. remember (str_cap m) as oc eqn:Eoc.
    assert (Hlencs : Z.of_nat (length cs) = n) by (rewrite En; reflexivity).

    assert (SRC : 0 <= src /\ src + oc + 1 <= 2 ^ 63 /\ mdef M src (oc + 1) /\ placed MI A src (oc + 1)
                  /\ (src + oc + 1 <= sp - (64 + (16 + MALLOC_STACK MI)) \/ sp <= src)
                  /\ (forall a, src <= a < src + oc + 1 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a)).
    { destruct m as [|d asz]; subst src oc; cbn [str_data str_cap] in *; unfold SSO_CAP in *.
      - split; [lia|]. split; [lia|]. split; [eapply mdef_sub; [exact HDp| lia | lia]|].
        split. { destruct PLp as [H|(q & k & H1 & H2 & H3)]; [left; lia | right]. exists q, k. split; [exact H1|lia]. }
        split; [unhide WINp'; lia|].
        intros a Ha. apply (placed_sep A M model p 24 a AI PLp). lia.
      - destruct HM as (Hd0 & Hd16 & Hdsz & Hsz8 & Hsz46 & HIn & Hdj & G0 & G1 & G2).
        split; [lia|]. split; [lia|]. replace (d + (asz - 1) + 1) with (d + asz) by lia. replace (asz - 1 + 1) with asz by lia.
        split; [eapply (live_mdef SEGS Ly.L MI); eassumption|].
        split; [right; exists d, asz; split; [exact HIn|lia]|].
        split. { left. destruct (live_range SEGS Ly.L MI A M model d asz AI HIn) as (_ & _ & _ & Hce). lia. }
        intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
    destruct SRC as (Hs0 & Hs1 & HDs & PLs & WINs & SRCsep). hide WINs.
    assert (HDR : forall a, p <= a < p + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. exact (placed_sep A M model p 24 a AI PLp Ha). }
    assert (WIN : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (64 + (16 + MALLOC_STACK MI))) (64 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }

    set (M1 := wslots M sp (PRO_vals R ret)).
    assert (ST1 : stores_in (zwin (sp - 64) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp (PRO_vals R ret)); unfold Zlen; cbn; lia. }
    assert (AG1 : forall lo hi, (hi <= sp - 64 \/ sp <= lo) -> 0 <= lo -> hi < 2 ^ 64 -> agree_on (zwin lo hi) M M1).
    { intros lo hi Hd Hlo Hhi. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *. lia. }
    assert (HDp1 : mdef M1 p 24) by (eapply stores_in_mdef; [exact ST1 | exact HDp]).
    assert (HDs1 : mdef M1 src (oc + 1)) by (eapply stores_in_mdef; [exact ST1 | exact HDs]).
    assert (FC1 : forall i, 0 <= i < n -> 0 <= Znth i cs < 256 /\ fld SEGS M1 (src + i) 1 (Znth i cs)).
    { intros i Hi. destruct (FC i Hi) as [Hr HF]. split; [exact Hr|].
      eapply fld_agree; [lia| cbn; lia | exact HF |]. apply AG1; cbn; unhide WINs; lia. }
    assert (CS1 : rdn SEGS M1 (Z_to_bv 64 src) (length cs) = Some (str_bytes cs)).
    { apply fld_str_rdn; [lia | unfold Zlen; lia | intros i Hi; apply FC1; unfold Zlen in Hi; lia]. }
    assert (SL : forall k, 1 <= k <= 8 ->
              rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
              = Some (word_to_le_bytes 8 (nth (Z.to_nat (8 - k)) (PRO_vals R ret) (Z_to_bv 64 0)))).
    { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
    slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4.
    slotv SL 5 SL5. slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. clear SL.
    set (W := (sp - (64 + (16 + MALLOC_STACK MI)), sp)).
    set (bch := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ch))).
    assert (Hbch : [bch] = word_to_le_bytes 1 (Z_to_bv 64 (ch mod 256))) by (unfold bch; apply sb_byte_w1).
    assert (Hchr : 0 <= ch mod 256 < 256) by (apply Z.mod_pos_bound; lia).

    assert (GROW : forall Rg,
      n = oc ->
      getr Rg 2%bv = Z_to_bv 64 (sp - 64) -> getr Rg 3%bv = getr R 3%bv -> getr Rg 4%bv = getr R 4%bv ->
      getr Rg 8%bv = Z_to_bv 64 ch -> getr Rg 9%bv = Z_to_bv 64 p -> getr Rg 10%bv = Z_to_bv 64 oc ->
      getr Rg 18%bv = Z_to_bv 64 src -> getr Rg 19%bv = Z_to_bv 64 (str_grow m) -> getr Rg 21%bv = Z_to_bv 64 (oc + 1) ->
      (forall r, In r [23; 24; 25; 26; 27]%bv -> getr Rg r = getr R r) ->
      srealizes SEGS (mkCfg (@mkst fx Rg (Z_to_bv 64 0x8d290) M1 (seg_rom SEGS)) model) K).
    { intros Rg LEN Rg2 Rg3 Rg4 Rg8 Rg9 Rg10 Rg18 Rg19 Rg21 RgS.
      destruct (ROOM LEN) as [HNMAX RL].
      remember (str_grow m) as ng eqn:Eng.
      assert (Hng : 48 <= ng /\ ng mod 8 = 0 /\ 2 * oc + 2 <= ng /\ 22 <= oc).
      { destruct m as [|d asz]; subst ng oc; cbn [str_grow str_cap] in *; unfold SSO_CAP in *.
        - split; [lia|]. split; [reflexivity|]. lia.
        - destruct HM as (Hd0 & Hd16 & Hdsz & Hsz8 & Hsz46 & _). split; [lia|]. split; [|lia].
          pose proof (Z.div_mod asz 8 ltac:(lia)). replace (2 * asz) with ((2 * (asz / 8)) * 8) by lia. apply Z_mod_mult. }
      destruct Hng as (Hng48 & Hng8 & Hngoc & Hoc22).
      assert (Hng1 : Z.lor ng 1 = ng + 1).
      { apply lor_even_1; [lia|]. change 8 with (2 * 4) in Hng8. rewrite Z.rem_mul_r in Hng8 by lia.
        pose proof (Z.mod_pos_bound ng 2 ltac:(lia)). pose proof (Z.mod_pos_bound (ng / 2) 4 ltac:(lia)). lia. }

      assert (B2 : exists Rn,
        msteps SEGS (@mkst fx Rg (Z_to_bv 64 0x8d290) M1 (seg_rom SEGS))
                    (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) M1 (seg_rom SEGS))
        /\ getr Rn 10%bv = Z_to_bv 64 ng /\ getr Rn 1%bv = Z_to_bv 64 0x8d29c
        /\ getr Rn 2%bv = Z_to_bv 64 (sp - 64) /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
        /\ getr Rn 8%bv = Z_to_bv 64 ch /\ getr Rn 9%bv = Z_to_bv 64 p /\ getr Rn 18%bv = Z_to_bv 64 src
        /\ getr Rn 19%bv = Z_to_bv 64 ng /\ getr Rn 20%bv = Z_to_bv 64 oc /\ getr Rn 21%bv = Z_to_bv 64 (oc + 1)
        /\ (forall r, In r [23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r)).
      { eexists. split.
        - norm_pc.
          sv F_8d250 D_8d250 (Z_to_bv 64 oc).
          sv F_8d254 D_8d254 (Z_to_bv 64 ng).
          stepj F_8d258 D_8d258.
          lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
          f_equal. apply bv_eq; vm_compute; reflexivity.
        - gres. repeat split; try reflexivity; try assumption.
          intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply RgS; exact Hr'|]). destruct Hr. }
      destruct B2 as (Rn & RUN2 & Rn10 & Rn1 & Rn2 & Rn3 & Rn4 & Rn8 & Rn9 & Rn18 & Rn19 & Rn20 & Rn21 & RnS).
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN2 | ].
      eapply (NEW fx A s Rn M1 model ng (sp - 64) 0x8d29c K).
      + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
      + exact MS.
      + eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
      + eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
        intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
      + exact SXH.
      + constructor.
        * exact Rn1.
        * unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
        * lia.
        * exact Rn2.
        * replace (sp - 64) with (sp - 16 * 4) by lia. apply mod16_sub. exact Hsp16.
        * lia.
        * rewrite Rn3. exact Hgp.
        * rewrite Rn4. exact Htp.
      + exact Rn10.
      + lia.
      + lia.
      + unfold stack_room. eapply stores_in_store_ok; [exact ST1|]. ok_sub HOK.
      + intros a Ha. apply Hwin. unfold zwin in *. lia.
      + exact Hown_sx.
      + exact Herr_sx.
      + rewrite new_size_id by lia. eapply (roomL_room_for SEGS Ly.L MI); [exact AI | lia | exact RL].
      +
        intros A1 R2 M2 model1 q AI1 MS1 Hfs1 Hfds1 SX1 KEPT2 R2a0 Hq LADD CAPS1 BIGC1 NEWT1 FR1 DEF1.
        rewrite new_size_id in LADD, FR1 by lia.
        assert (ROC1 : img_ro_clear Ly.L M1).
        { eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))). }
        assert (ROC2 : img_ro_clear Ly.L M2).
        { eapply (roc_frame Ly.L); [exact ROC1 | exact FR1 |]. intros a [Ho|[Hblk|[Hw|He]]].
          - exact (roc_owned SEGS Ly.L MI A1 M2 model1 a AI1 Ho).
          - right. eapply (live_offimg SEGS Ly.L MI); [exact AI1 | apply (live_add_new _ _ _ _ LADD) | exact Hblk].
          - right. apply (proj2 (stack_sep A1 M2 model1 a AI1 ltac:(unfold zwin in Hw; lia))).
          - left. apply ly_errno_rw. exact He. }
        assert (HinQ : In (q, ng) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
        destruct (live_range SEGS Ly.L MI A1 M2 model1 q ng AI1 HinQ) as (_ & Hqal & _ & Hqce).
        assert (HDq : mdef M2 q ng) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
        assert (Hqown : forall a, q <= a < q + ng -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
        assert (LIVE1 : forall blk, In blk (live MI A) -> In blk (live MI A1)) by (intros blk Hblk; eapply live_add_keeps; eassumption).
        assert (PLp1 : placed MI A1 p 24) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
        assert (PLs1 : placed MI A1 src (oc + 1)) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
        assert (HDRq : p + 24 <= q \/ q + ng <= p).
        { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 p 24 q ng AI AI1 PLp LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
        assert (SRCq : src + oc + 1 <= q \/ q + ng <= src).
        { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 src (oc + 1) q ng AI AI1 PLs LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
        hide HDRq. hide SRCq.
        assert (WIN1 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. apply (stack_sep A1 M2 model1 a AI1). lia. }
        assert (HDR1 : forall a, p <= a < p + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. exact (placed_sep A1 M2 model1 p 24 a AI1 PLp1 Ha). }
        assert (SRC1 : forall a, src <= a < src + oc + 1 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. apply (placed_sep A1 M2 model1 src (oc + 1) a AI1 PLs1). lia. }

        assert (PRES2 : forall a, (sp - 64 <= a < sp) \/ (p <= a < p + 24) \/ (src <= a < src + oc + 1) ->
                                  M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha.
          assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [H|[H|H]]; lia).
          apply FR1. rewrite u64_of_Z by lia. intros [Ho|[Hblk|[Hw|He]]].
          - destruct Ha as [H|[H|H]].
            + exact (proj1 (WIN1 a ltac:(lia)) Ho).
            + exact (proj1 (HDR1 a H) Ho).
            + exact (proj1 (SRC1 a H) Ho).
          - destruct Ha as [H|[H|H]]. + lia. + unhide HDRq; lia. + unhide SRCq; lia.
          - unfold zwin in Hw. destruct Ha as [H|[H|H]]. + lia. + unhide WINp'; lia. + unhide WINs; lia.
          - pose proof (ly_errno_img a He) as Hi. rewrite ly_img_iff in Hi.
            destruct Ha as [H|[H|H]].
            + pose proof (proj2 (WIN1 a ltac:(lia))) as X. rewrite ly_img_iff in X. lia.
            + pose proof (proj2 (HDR1 a H)) as X. rewrite ly_img_iff in X. lia.
            + pose proof (proj2 (SRC1 a H)) as X. rewrite ly_img_iff in X. lia. }
        assert (AG2 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                 ((sp - 64 <= lo /\ hi <= sp) \/ (p <= lo /\ hi <= p + 24) \/ (src <= lo /\ hi <= src + oc + 1)) ->
                 agree_on (zwin lo hi) M1 M2).
        { intros lo hi Hlo Hhi Hc a Ha. apply PRES2. unfold zwin in Ha. clear -Hc Ha.
          destruct Hc as [H|[H|H]]; [left|right;left|right;right]; lia. }

        assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
        assert (R2_8 : getr R2 8%bv = Z_to_bv 64 ch) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
        assert (R2_9 : getr R2 9%bv = Z_to_bv 64 p) by (rewrite (KEPT2 9%bv) by in_cs; exact Rn9).
        assert (R2_18 : getr R2 18%bv = Z_to_bv 64 src) by (rewrite (KEPT2 18%bv) by in_cs; exact Rn18).
        assert (R2_19 : getr R2 19%bv = Z_to_bv 64 ng) by (rewrite (KEPT2 19%bv) by in_cs; exact Rn19).
        assert (R2_20 : getr R2 20%bv = Z_to_bv 64 oc) by (rewrite (KEPT2 20%bv) by in_cs; exact Rn20).
        assert (R2_21 : getr R2 21%bv = Z_to_bv 64 (oc + 1)) by (rewrite (KEPT2 21%bv) by in_cs; exact Rn21).
        assert (CS2 : rdn SEGS M2 (Z_to_bv 64 src) (length cs) = Some (str_bytes cs)).
        { rewrite <- CS1. apply rdn_agree_win; [lia | lia |]. apply AG2; [lia|lia|]. right; right; lia. }

        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc.
          sv F_8d25c D_8d25c (Z_to_bv 64 q).
          sv F_8d260 D_8d260 (Z_to_bv 64 src).
          sv F_8d264 D_8d264 (Z_to_bv 64 oc).
          stepj F_8d268 D_8d268.
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst ?r _ _ _) _) _ => set (R3 := r) end.
        assert (MC : mcH SEGS M2 (Z_to_bv 64 q) (Z_to_bv 64 src) oc (str_bytes cs)).
        { constructor.
          - lia.
          - rewrite str_bytes_length. lia.
          - rewrite str_bytes_length. exact CS2.
          - rewrite str_bytes_length. apply (mdef_store_ok SEGS M2 q ng); try lia. exact HDq.
          - rewrite !u64_of_Z by lia. unhide SRCq. destruct SRCq; [right|left]; lia.
          - rewrite u64_of_Z by lia. lia.
          - rewrite u64_of_Z by lia. lia. }
        destruct (u1_memmove_spec fx M2 (Z_to_bv 64 q) (Z_to_bv 64 src) oc (str_bytes cs) (seg_rom SEGS) R3 (Z_to_bv 64 0x8d2ac)
                    MC ltac:(lia) ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R3; gres; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R3; gres; exact R2a0) ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; reflexivity))
          as (R4 & RUN4 & KEEP4).
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 MEMMOVE) by (apply bv_eq; vm_compute; reflexivity) end.
          exact RUN4. }
        set (M3 := wbytes M2 (Z_to_bv 64 q) (str_bytes cs)) in *.

        assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEEP4 2%bv) by in_cs; unfold R3; gres; exact R2_2).
        assert (R4_8 : getr R4 8%bv = Z_to_bv 64 ch) by (rewrite (KEEP4 8%bv) by in_cs; unfold R3; gres; exact R2_8).
        assert (R4_9 : getr R4 9%bv = Z_to_bv 64 p) by (rewrite (KEEP4 9%bv) by in_cs; unfold R3; gres; exact R2_9).
        assert (R4_18 : getr R4 18%bv = Z_to_bv 64 src) by (rewrite (KEEP4 18%bv) by in_cs; unfold R3; gres; exact R2_18).
        assert (R4_19 : getr R4 19%bv = Z_to_bv 64 ng) by (rewrite (KEEP4 19%bv) by in_cs; unfold R3; gres; exact R2_19).
        assert (R4_20 : getr R4 20%bv = Z_to_bv 64 oc) by (rewrite (KEEP4 20%bv) by in_cs; unfold R3; gres; exact R2_20).
        assert (R4_21 : getr R4 21%bv = Z_to_bv 64 (oc + 1)) by (rewrite (KEEP4 21%bv) by in_cs; unfold R3; gres; exact R2_21).
        assert (R4_22 : getr R4 22%bv = Z_to_bv 64 q) by (rewrite (KEEP4 22%bv) by in_cs; unfold R3; gres; reflexivity).
        assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (KEEP4 3%bv) by in_cs; unfold R3; gres; rewrite (KEPT2 3%bv) by in_cs; exact Rn3).
        assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (KEEP4 4%bv) by in_cs; unfold R3; gres; rewrite (KEPT2 4%bv) by in_cs; exact Rn4).
        assert (R4S : forall r, In r [23; 24; 25; 26; 27]%bv -> getr R4 r = getr R r).
        { intros r Hr. pose proof Hr as Hr'.
          repeat (destruct Hr as [<-|Hr]; [rewrite (KEEP4 _) by in_cs; unfold R3; gres; rewrite (KEPT2 _) by in_cs; apply RnS; exact Hr' |]). destruct Hr. }
        assert (HDp2 : mdef M2 p 24).
        { intros i Hi. destruct (DEF1 (Z_to_bv 64 (p + i)) (HDp1 i Hi)) as [H|[H|H]]; [exact H| |].
          - exfalso. rewrite u64_of_Z in H by lia. exact (proj1 (HDR (p + i) ltac:(lia)) H).
          - exfalso. rewrite u64_of_Z in H by lia. exact (proj2 (HDR (p + i) ltac:(lia)) (ly_errno_img _ H)). }
        assert (HDp3 : mdef M3 p 24) by (unfold M3; apply mdef_wbytes; exact HDp2).
        assert (HDq3 : mdef M3 q ng) by (unfold M3; apply mdef_wbytes; exact HDq).
        assert (ST23 : stores_in (zwin q (q + oc)) M2 M3).
        { unfold M3. apply stores_in_wbytes; rewrite ?str_bytes_length; try lia. intros a Ha. unfold zwin. lia. }
        assert (CS3 : rdn SEGS M3 (Z_to_bv 64 q) (length cs) = Some (str_bytes cs)).
        { unfold M3. rewrite <- str_bytes_length. apply RefReadLib.rdn_wbytes_self.
          rewrite str_bytes_length, u64_of_Z by lia. lia. }
        unhide HDRq.
        assert (AG13 : agree_on (zwin (sp - 64) sp) M1 M3).
        { intros a Ha. unfold zwin in Ha. rewrite <- (PRES2 a) by (left; lia). apply (proj1 ST23). rewrite u64_of_Z by lia. unfold zwin. lia. }
        set (FT := fun a => zwin p (p + 24) a \/ sbuf_fp m a \/ zwin q (q + ng) a).
        assert (EFF3 : eff MI A A1 M M3 W FT).
        { eapply eff_weaken.
          - eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of, W in Ha; cbn in Ha; lia].
            + eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of, W in Ha; cbn in Ha; lia].
              * apply (eff_store MI A M M1 W FT); [| exact (proj2 ST1)].
                intros a HF HW. apply (proj1 ST1). intros Hz. apply HW. unfold W_of, W, zwin in *. cbn. lia.
              * eapply (eff_of_new MI A A1 M1 M2 model1 W FT q ng); try eassumption.
                -- intros a Ha. unfold W_of, W, zwin in *. cbn. lia.
                -- intros a Ha. unfold FT. right; right. unfold zwin. lia.
            + apply (eff_store MI A1 M2 M3 W FT); [| exact (proj2 ST23)].
              intros a HF HW. apply (proj1 ST23). intros Hz; apply HF; unfold FT. right; right; unfold zwin in *; lia.
          - intros a [[H|H]|H]; exact H. }
        hide HDRq.

        assert (TAIL : forall A2 R6 M6 model2,
          ainv MI A2 M6 model2 -> mstd model2 -> m_fs model2 = m_fs model -> m_fds model2 = m_fds model ->
          sx_inv ST s M6 ->
          getr R6 2%bv = Z_to_bv 64 (sp - 64) -> getr R6 8%bv = Z_to_bv 64 ch -> getr R6 9%bv = Z_to_bv 64 p ->
          getr R6 19%bv = Z_to_bv 64 ng -> getr R6 20%bv = Z_to_bv 64 oc -> getr R6 22%bv = Z_to_bv 64 q ->
          getr R6 3%bv = getr R 3%bv -> getr R6 4%bv = getr R 4%bv ->
          (forall r, In r [23; 24; 25; 26; 27]%bv -> getr R6 r = getr R r) ->
          agree_on (zwin (sp - 64) sp) M1 M6 ->
          mdef M6 p 24 -> mdef M6 q ng -> rdn SEGS M6 (Z_to_bv 64 q) (length cs) = Some (str_bytes cs) ->
          In (q, ng) (live MI A2) ->
          (forall a, p <= a < p + 24 -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x124000)] a) ->
          eff MI A A2 M M6 W FT -> lapply (live MI A) (LAdd q ng :: sbuf_del m) (live MI A2) ->
          srealizes SEGS (mkCfg (@mkst fx R6 (Z_to_bv 64 0x8d2c0) M6 (seg_rom SEGS)) model2) K).
        { intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 SX2 R6_2 R6_8 R6_9 R6_19 R6_20 R6_22 R6_3 R6_4 R6S AG6 HDp6 HDq6 CS6 HinQ2 HDR2 EFF6 LAP.
          assert (SLT : forall a vv, sp - 64 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some vv).
          { intros a vv H1 H2 H3. rewrite (rdn_agree_win SEGS M1 M6); [exact H3 | lia | cbn; lia |].
            eapply agree_on_weaken; [exact AG6|]. intros a' Ha. unfold zwin in *. cbn in Ha. lia. }
          assert (WIN2 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
          { intros a Ha. apply (stack_sep A2 M6 model2 a AI2). lia. }
          assert (Hqown2 : forall a, q <= a < q + ng -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
          { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
          destruct (live_range SEGS Ly.L MI A2 M6 model2 q ng AI2 HinQ2) as (_ & _ & _ & Hqce2).
          set (M7 := wbytes (wbytes (wbytes M6 (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (ng + 1))))
                                    (Z_to_bv 64 (p + 16)) (word_to_le_bytes 8 (Z_to_bv 64 q)))
                             (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (oc + 1)))).
          set (M8 := wbytes (wbytes M7 (Z_to_bv 64 (q + oc)) [bch]) (Z_to_bv 64 (q + oc + 1)) [Z_to_bv 8 0]).
          assert (ST78 : stores_in (fun a => zwin p (p + 24) a \/ zwin (q + oc) (q + oc + 2) a) M6 M8).
          { unfold M8, M7.
            eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more;
              [eapply stores_in_wbytes_more; [apply stores_in_wbytes| | |] | | |] | | |] | | |];
              rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia;
              intros a Ha; unfold zwin; lia. }
          eapply srz_msteps; [exact (ms_halt _ MS2) | exact (ms_lazy _ MS2) | | ].
          { eapply msteps_trans.
            - norm_pc.
              stepiv F_8d280 D_8d280 (Z_to_bv 64 (ng + 1))
                ltac:(gres; rewrite R6_19; unfold v_ori; rewrite u64_of_Z by lia; imm_norm; change (bv_wrap 64 1) with 1; rewrite Hng1; reflexivity).
              stw F_8d284 D_8d284 (Z_to_bv 64 p) (Z_to_bv 64 (ng + 1)) ltac:(ok_mdef HDp6).
              stw F_8d288 D_8d288 (Z_to_bv 64 (p + 16)) (Z_to_bv 64 q) ltac:(ok_mdef HDp6).
              ld_step F_8d28c D_8d28c (word_to_le_bytes 8 (Z_to_bv 64 q)) (Z_to_bv 64 q)
                ltac:(peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia) ltac:(b2z8).
              stepiv F_8d290 D_8d290 (Z_to_bv 64 (oc + 1)) ltac:(gres; rewrite R6_20; imm_norm; rewrite v_addi_Z by lia; reflexivity).
              stw F_8d294 D_8d294 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (oc + 1)) ltac:(ok_mdef HDp6).
              apply mst_refl.
            - fold M7.
              lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
                replace pc with (Z_to_bv 64 0x8d2d8) by (apply bv_eq; vm_compute; reflexivity) end.
              apply (epilogue fx _ M7 sp ret q oc (Z_to_bv 64 ch)
                       (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv));
                [ gres; exact R6_2 | gres; reflexivity | gres; exact R6_20 | gres; exact R6_8 | lia | lia | lia | lia | left; lia | | | | | | | | | | exact Hret ].
              + unfold M7. apply (mdef_store_ok SEGS _ (q + oc) 2 2); [|lia|lia|cbn; lia].
                eapply mdef_sub; [apply mdef_wbytes, mdef_wbytes, mdef_wbytes; exact HDq6 | lia | lia].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL1].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL2].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL3].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL4].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL5].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL6].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL7].
              + unfold M7. unhide WINp'. peel. apply SLT; [lia|lia|rdn_fix SL8]. }
          fold M7. fold bch. fold M8.
          eapply (CONT A2 _ M8 model2 (SLong q ng)).
          -   constructor.
            + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI2 | exact ST78 |].
              intros a [Ha|Ha]; [apply HDR2 | apply Hqown2]; unfold zwin in Ha; lia.
            + exact MS2.
            + exact Hfs2.
            + exact Hfds2.
            + eapply (stores_in_sx SEGS Ly.L ST); [exact SX2 | exact ST78 |].
              intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x124000)] a)
                by (destruct Ha as [Ha|Ha]; [apply HDR2 | apply Hqown2]; unfold zwin in Ha; lia).
              destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
            + intros r Hr; unfold callee_saved in Hr.
              repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | rewrite ?R6_3, ?R6_4; reflexivity | apply R6S; in_cs ] |]).
              destruct Hr.
          -
            assert (AG8 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= p \/ p + 24 <= lo) -> (hi <= q + oc \/ q + oc + 2 <= lo) ->
                          agree_on (zwin lo hi) M6 M8).
            { intros lo hi H1 H2 H3 H4. eapply stores_in_agree; [exact ST78|]. intros a Ha. unfold zwin in *. lia. }
            unhide HDRq.
            assert (FC6 : forall i, 0 <= i < n -> fld SEGS M6 (q + i) 1 (Znth i cs)).
            { intros i Hi. apply (rdn_str_fld SEGS M6 q cs); [lia | unfold Zlen; lia | | exact CS6 | unfold Zlen; lia].
              intros j Hj. apply (proj1 (FC j ltac:(unfold Zlen in Hj; lia))). }
            unfold CRep.str_rep. rewrite Zlen_app1, <- En. cbn [str_cap str_data].
            split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact ST78|exact HDp6]|].
            split; [lia|].
            split. { split; [lia|]. split; [exact Hqal|]. split; [lia|]. split; [exact Hng8|]. split; [unfold SSO_CAP; lia|].
                     split; [exact HinQ2|]. split; [lia|].
                     split. { unfold fld, M8, M7. peel1. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
                     split. { unfold fld, M8, M7. peel1. replace (n + 1) with (oc + 1) by lia. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
                     unfold fld, M8, M7. peel1. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
            split.
            + intros i Hi. destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
              * rewrite Znth_app_l by lia. split; [apply (proj1 (FC i ltac:(lia)))|].
                eapply fld_agree; [lia|cbn; lia|apply FC6; lia|]. apply AG8; cbn; lia.
              * replace i with n by lia. rewrite En, Znth_app_r1, <- En. split; [exact Hchr|].
                unfold fld, M8. peel1. rewrite <- Hbch. replace (q + n) with (q + oc) by lia.
                change 1%nat with (length [bch]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
            + unfold fld, M8. replace (q + (n + 1)) with (q + oc + 1) by lia.
              change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
              change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
          - right. split; [exact LEN|]. exists q. split; [reflexivity|]. exact LAP.
          -
            eapply eff_weaken.
            + eapply (eff_trans MI); [exact EFF6 | | intros a Ha; apply WIN2; unfold W_of, W in Ha; cbn in Ha; lia].
              apply (eff_store MI A2 M6 M8 W FT); [| exact (proj2 ST78)].
              intros a HF HW. apply (proj1 ST78). intros [Hz|Hz]; apply HF; unfold FT; [left; exact Hz | right; right; unfold zwin in *; lia].
            + intros a' [H|H]; [exact H|]. unfold FT in H. cbn [sbuf_fp]. exact H.
        }

        destruct m as [|d asz].
        *
          cbn [str_cap] in Eoc. unfold SSO_CAP in Eoc.
          eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
          { norm_pc. sv F_8d26c D_8d26c (Z_to_bv 64 23).
            stepb_tk F_8d270 D_8d270 ltac:(rewrite R4_21, Eoc; apply c_eq_refl). apply mst_refl. }
          lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x8d2c0) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
          apply (TAIL A1 R5 M3 model1); try assumption; try (unfold R5; gres; assumption).
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST23 |]. intros a Ha; apply Hqown; unfold zwin in Ha; lia.
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST23 |].
             intros a Ha. destruct (offimg_sep a (proj2 (Hqown a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
          -- intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [unfold R5; gres; apply R4S; exact Hr' |]). destruct Hr.
          -- cbn. exists (live MI A1). split; [exact LADD | reflexivity].
        *
          cbn [str_cap str_data] in Eoc, Esrc. subst src.
          destruct HM as (Hd0 & Hd16 & Hdsz & Hsz8 & Hsz46 & HIn & Hdj & G0 & G1 & G2). unfold SSO_CAP in Hsz46.
          eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
          { norm_pc. sv F_8d26c D_8d26c (Z_to_bv 64 23).
            stepb_ft F_8d270 D_8d270 ltac:(rewrite R4_21; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            sv F_8d274 D_8d274 (Z_to_bv 64 d).
            sv F_8d278 D_8d278 (Z_to_bv 64 asz).
            stepj F_8d27c D_8d27c. apply mst_refl. }
          lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 DEL1) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
          eapply (u1_op_delete1_spec MI fx A1 R5 M3 model1 d asz (sp - 64) 0x8d2c0 K).
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST23 |]. intros a Ha; apply Hqown; unfold zwin in Ha; lia.
          -- exact MS1.
          -- eapply (roc_stores Ly.L); [exact ROC2 | exact ST23 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (Hqown a ltac:(unfold zwin in Ha; lia))).
          -- constructor; unfold R5; gres.
             ++ apply bv_eq; vm_compute; reflexivity.
             ++ unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
             ++ lia.
             ++ exact R4_2.
             ++ replace (sp - 64) with (sp - 16 * 4) by lia. apply mod16_sub. exact Hsp16.
             ++ lia.
             ++ rewrite R4_3. exact Hgp.
             ++ rewrite R4_4. exact Htp.
          -- unfold R5; gres; reflexivity.
          -- right. apply LIVE1. exact HIn.
          -- lia.
          -- unfold stack_room. eapply stores_in_store_ok; [exact ST23|].
             assert (HDW2 : mdef M2 (sp - (64 + (16 + MALLOC_STACK MI))) (64 + (16 + MALLOC_STACK MI))).
             { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST1 | exact HDW] | lia | lia |].
               intros a Ha [Ho|He]; [exact (proj1 (WIN a ltac:(lia)) Ho) | exact (proj2 (WIN a ltac:(lia)) (ly_errno_img a He))]. }
             replace (sp - 64 - MALLOC_STACK MI) with (sp - (64 + (16 + MALLOC_STACK MI)) + 16) by lia.
             apply (mdef_store_ok_off SEGS M2 _ _ 16 _ HDW2); lia.
          -- intros a Ha. apply WIN1. unfold zwin in *. lia.
          -- intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 KEPT6 LDEL CAPS2 BIGC2 OWN2 FR2 DEF2.
             assert (Hqd : q <> d).
             { intros ->. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (d, asz). split; [reflexivity|exact HIn]. }
             unhide SRCq. unhide HDRq.
             assert (FSEP : forall a, (sp - 64 <= a < sp) \/ (p <= a < p + 24) \/ (q <= a < q + ng) ->
                              ~ owned MI A1 a /\ ~ (d <= a < d + asz) /\ ~ zwin (sp - 64 - MALLOC_STACK MI) (sp - 64) a /\ ~ in_ranges (ly_img Ly.L) a).
             { intros a [Ha|[Ha|Ha]].
               - destruct (WIN1 a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unhide WINs; unfold zwin; lia).
               - destruct (HDR1 a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unfold zwin; unhide WINp'; lia).
               - destruct (Hqown a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unfold zwin; lia). }
             assert (AG36 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                      ((sp - 64 <= lo /\ hi <= sp) \/ (p <= lo /\ hi <= p + 24) \/ (q <= lo /\ hi <= q + ng)) ->
                      agree_on (zwin lo hi) M3 M6).
             { intros lo hi H1 H2 Hc a Ha. unfold zwin in Ha. apply FR2. rewrite u64_of_Z by lia.
               destruct (FSEP a ltac:(clear -Hc Ha; destruct Hc as [H|[H|H]]; [left|right;left|right;right]; lia)) as (X1 & X2 & X3 & X4).
               intros [H|[H|[H|H]]]; [exact (X1 H)|exact (X2 H)|exact (X3 H)|exact (X4 (ly_errno_img a H))]. }
             apply (TAIL A2 R6 M6 model2).
             ++ exact AI2.
             ++ exact MS2.
             ++ rewrite Hfs2. exact Hfs1.
             ++ rewrite Hfds2. exact Hfds1.
             ++ eapply (sx_through SEGS Ly.L ST); [ | exact FR2 | ].
                ** eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST23 |].
                   intros a Ha. apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). apply Hqown. unfold zwin in Ha; lia.
                ** intros a [Ho|[Hblk|[Hw|He]]].
                   --- eapply (owned_later_not_sx SEGS Ly.L MI ST ly_rw_img ly_relro_img ly_rw_not_relro); [exact AI | exact Hown_sx | exact NEWT1 | exact Ho].
                   --- apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). apply SRCsep. lia.
                   --- apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). apply WIN1. unfold zwin in Hw. lia.
                   --- split; [exact (Herr_sx a He) | intros Hr; exact (ly_rw_not_relro a (ly_errno_rw a He) Hr)].
             ++ rewrite (KEPT6 2%bv) by in_cs. unfold R5. gres. exact R4_2.
             ++ rewrite (KEPT6 8%bv) by in_cs. unfold R5. gres. exact R4_8.
             ++ rewrite (KEPT6 9%bv) by in_cs. unfold R5. gres. exact R4_9.
             ++ rewrite (KEPT6 19%bv) by in_cs. unfold R5. gres. exact R4_19.
             ++ rewrite (KEPT6 20%bv) by in_cs. unfold R5. gres. exact R4_20.
             ++ rewrite (KEPT6 22%bv) by in_cs. unfold R5. gres. exact R4_22.
             ++ rewrite (KEPT6 3%bv) by in_cs. unfold R5. gres. exact R4_3.
             ++ rewrite (KEPT6 4%bv) by in_cs. unfold R5. gres. exact R4_4.
             ++ intros r Hr. pose proof Hr as Hr'.
                repeat (destruct Hr as [<-|Hr]; [rewrite (KEPT6 _) by in_cs; unfold R5; gres; apply R4S; exact Hr' |]). destruct Hr.
             ++ intros a Ha. rewrite (AG36 (sp - 64) sp); [apply AG13; exact Ha | lia | lia | left; lia | exact Ha].
             ++ eapply (mdef_through (fun a => owned MI A1 a \/ ((d <= a < d + asz) \/ errno_win Ly.L a))); [exact DEF2 | exact HDp3 | lia | lia |].
                intros a Ha [Ho|[Hblk|He]]; [exact (proj1 (HDR1 a Ha) Ho)  |  lia | exact (proj2 (HDR1 a Ha) (ly_errno_img a He))].
             ++ eapply (mdef_through (fun a => owned MI A1 a \/ ((d <= a < d + asz) \/ errno_win Ly.L a))); [exact DEF2 | exact HDq3 | lia | lia |].
                intros a Ha [Ho|[Hblk|He]]; [exact (proj1 (Hqown a Ha) Ho)  |  | exact (proj2 (Hqown a Ha) (ly_errno_img a He))].
                destruct (ai_live_disjoint MI A1 M2 model1 q ng d asz AI1 HinQ (LIVE1 _ HIn) Hqd); lia.
             ++ rewrite <- CS3. apply rdn_agree_win; [lia | lia |]. apply AG36; [lia | lia | right; right; lia].
             ++ eapply live_del_keeps; [exact LDEL | exact HinQ | exact Hqd].
             ++ intros a Ha. split; [| apply HDR1; lia]. intros Ho. destruct (OWN2 a Ho) as [Ho1|Hblk]; [exact (proj1 (HDR1 a Ha) Ho1) | lia].
             ++ eapply eff_weaken.
                ** eapply (eff_trans MI); [exact EFF3 | | intros a Ha; apply (stack_sep A2 M6 model2 a AI2); unfold W_of, W in Ha; cbn in Ha; lia].
                   eapply (eff_of_del MI A1 A2 M3 M6 W FT d asz); try eassumption.
                   --- intros a Ha. unfold W_of, W, zwin in *. cbn. lia.
                   --- intros a Ha. unfold FT. right; left. cbn [sbuf_fp]. unfold zwin. lia.
                   --- intros a Ha. exact (proj2 (SRCsep a ltac:(lia))).
                ** intros a [H|H]; exact H.
             ++ cbn [sbuf_del lapply]. exists (live MI A1). split; [exact LADD|]. exists (live MI A2). split; [exact LDEL | reflexivity].
    }

    destruct m as [|d asz].
    -
      cbn [str_data str_cap] in Esrc, Eoc. unfold SSO_CAP in Eoc. subst src.
      assert (B0 : rdn SEGS M1 (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 (2 * n)]).
      { pose proof (fld1_rdn SEGS M1 p (2 * n)) as X. rewrite Z.mod_small in X by lia. apply X.
        eapply fld_agree; [lia|cbn; lia|exact HM|]. apply AG1; cbn; unhide WINp'; lia. }
      destruct (Z.lt_ge_cases n oc) as [LT|GE].
      +
        set (M2 := wbytes M1 (Z_to_bv 64 p) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (2 * n + 2)))]).
        set (M3 := wbytes (wbytes M2 (Z_to_bv 64 (p + 1 + n)) [bch]) (Z_to_bv 64 (p + 1 + n + 1)) [Z_to_bv 8 0]).
        assert (ST13 : stores_in (fun a => zwin (sp - 64) sp a \/ zwin p (p + 1) a \/ zwin (p + 1 + n) (p + 1 + n + 2) a) M M3).
        { unfold M3, M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1|] | | |] | | |] | | |];
            cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        * eapply msteps_trans.
          { apply (prologue fx R M sp ret p Hsp Hra Ha0); [ok_sub HOK | lia]. }
          fold M1.
          eapply msteps_trans.
          { norm_pc.
            lb_step F_8d1c0 D_8d1c0 (Z_to_bv 8 (2 * n)) ltac:(rdn_fix B0).
            replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * n)))) with (Z_to_bv 64 (2 * n)) by (rewrite u8_of_Z by lia; reflexivity).
            stepiv F_8d1c4 D_8d1c4 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
            sv F_8d1c8 D_8d1c8 (Z_to_bv 64 ch).
            stepb_ft F_8d1cc D_8d1cc ltac:(apply c_eq_refl).
            sv F_8d1d0 D_8d1d0 (Z_to_bv 64 44).
            stepb_tk F_8d1d4 D_8d1d4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            stepiv F_8d238 D_8d238 (Z_to_bv 64 n) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; change (2^1) with 2; rewrite Z.mul_comm; apply Z.div_mul; lia).
            stepiv F_8d23c D_8d23c (Z_to_bv 64 (p + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stepiv F_8d240 D_8d240 (Z_to_bv 64 (2 * n + 2)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stw F_8d244 D_8d244 (Z_to_bv 64 p) (Z_to_bv 64 (2 * n + 2)) ltac:(ok_mdef HDp1).
            stepj F_8d248 D_8d248.
            apply mst_refl. }
          fold M2.
          lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 0x8d2d8) by (apply bv_eq; vm_compute; reflexivity) end.
          apply (epilogue fx _ M2 sp ret (p + 1) n (Z_to_bv 64 ch)
                   (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv));
            [ gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity | lia | lia | lia | lia | unhide WINp'; lia
            | | | | | | | | | | exact Hret ].
          -- unfold M2. ok_mdef HDp1.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL1.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL2.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL3.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL4.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL5.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL6.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL7.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL8.
        * fold M1. fold M2. fold bch. fold M3.
          eapply (CONT A _ M3 model SShort).
          --   constructor.
             ++ eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST13 |].
                intros a [Hw|[Hhd|Hc]]; [apply WIN | apply HDR | apply HDR]; unfold zwin in *; lia.
             ++ exact MS.
             ++ reflexivity.
             ++ reflexivity.
             ++ eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST13 |].
                intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x124000)] a)
                  by (destruct Ha as [Ha|[Ha|Ha]]; [apply WIN | apply HDR | apply HDR]; unfold zwin in Ha; lia).
                destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
             ++ intros r Hr; unfold callee_saved in Hr.
                repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption] |]). destruct Hr.
          --
             assert (AG3 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= sp - 64 \/ sp <= lo) -> (hi <= p \/ p + 1 <= lo) ->
                           (hi <= p + 1 + n \/ p + 1 + n + 2 <= lo) -> agree_on (zwin lo hi) M M3).
             { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact ST13|]. intros a Ha. unfold zwin in *. lia. }
             unfold CRep.str_rep. rewrite Zlen_app1, <- En. cbn [str_cap str_data].
             split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact ST13|exact HDp]|].
             split; [unfold SSO_CAP; lia|].
             split. { unfold fld, M3, M2. peel1. replace (2 * (n + 1)) with (2 * n + 2) by lia.
                      change (word_to_le_bytes 1 (Z_to_bv 64 (2 * n + 2))) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (2 * n + 2)))].
                      change 1%nat with (length [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (2 * n + 2)))]).
                      apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia. }
             split.
             ++ intros i Hi. destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
                ** rewrite Znth_app_l by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
                   eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG3; cbn; unhide WINp'; lia.
                ** replace i with n by lia. rewrite En, Znth_app_r1, <- En. split; [exact Hchr|].
                   unfold fld, M3. peel1. rewrite <- Hbch.
                   change 1%nat with (length [bch]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
             ++ unfold fld, M3. replace (p + 1 + (n + 1)) with (p + 1 + n + 1) by lia.
                change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
                change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
          -- left. split; [exact LT|]. split; reflexivity.
          -- apply eff_store; [| exact (proj2 ST13)].
             intros a HF HW. apply (proj1 ST13). intros [Hw|[Hhd|Hc]].
             ++ apply HW. unfold W_of, W, zwin in *. cbn. lia.
             ++ apply HF. left. unfold zwin in *. lia.
             ++ apply HF. left. unfold zwin in *. lia.
      +
        assert (LEN : n = oc) by lia.
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        * eapply msteps_trans.
          { apply (prologue fx R M sp ret p Hsp Hra Ha0); [ok_sub HOK | lia]. }
          fold M1. norm_pc.
          lb_step F_8d1c0 D_8d1c0 (Z_to_bv 8 (2 * n)) ltac:(rdn_fix B0).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * n)))) with (Z_to_bv 64 (2 * n)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8d1c4 D_8d1c4 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
          sv F_8d1c8 D_8d1c8 (Z_to_bv 64 ch).
          stepb_ft F_8d1cc D_8d1cc ltac:(apply c_eq_refl).
          sv F_8d1d0 D_8d1d0 (Z_to_bv 64 44).
          stepb_ft F_8d1d4 D_8d1d4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_eq; lia).
          stepiv F_8d1d8 D_8d1d8 (Z_to_bv 64 (p + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          sv F_8d1dc D_8d1dc (Z_to_bv 64 48).
          sv F_8d1e0 D_8d1e0 (Z_to_bv 64 22).
          sv F_8d1e4 D_8d1e4 (Z_to_bv 64 23).
          stepj F_8d1e8 D_8d1e8.
          apply mst_refl.
        * lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x8d290) by (apply bv_eq; vm_compute; reflexivity); set (Rg := r) end.
          apply (GROW Rg LEN); unfold Rg; gres; try reflexivity; try assumption.
          -- rewrite Eoc. reflexivity.
          -- rewrite Eoc. reflexivity.
          -- intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity |]). destruct Hr.
    -
      cbn [str_data str_cap] in Esrc, Eoc. subst src.
      destruct HM as (Hd0 & Hd16 & Hdsz & Hsz8 & Hsz46 & HIn & Hdj & G0 & G1 & G2). unfold SSO_CAP in Hsz46.
      pose proof (Z.div_mod asz 8 ltac:(lia)) as Hd8. set (k8 := asz / 8) in Hd8. rewrite Hsz8, Z.add_0_r in Hd8.
      assert (Hodd : (asz + 1) mod 2 = 1).
      { rewrite Hd8. replace (8 * k8 + 1) with (1 + (4 * k8) * 2) by lia. rewrite Z_mod_plus_full. reflexivity. }
      assert (Hb0r : 0 <= (asz + 1) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
      assert (G0' : fld SEGS M1 p 8 (asz + 1)).
      { eapply fld_agree; [lia| cbn; lia | exact G0 |]. apply AG1; cbn; unhide WINp'; lia. }
      assert (G1' : fld SEGS M1 (p + 8) 8 n).
      { eapply fld_agree; [lia| cbn; lia | exact G1 |]. apply AG1; cbn; unhide WINp'; lia. }
      assert (G2' : fld SEGS M1 (p + 16) 8 d).
      { eapply fld_agree; [lia| cbn; lia | exact G2 |]. apply AG1; cbn; unhide WINp'; lia. }
      assert (B0 : rdn SEGS M1 (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 ((asz + 1) mod 256)]) by (apply fld8_byte0; exact G0').
      unfold fld in G0', G1', G2'.

      assert (PFX : msteps SEGS (@mkst fx R (Z_to_bv 64 0x8d1d8) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                              2%bv (Z_to_bv 64 (sp - 64))) 9%bv (Z_to_bv 64 p))
                              12%bv (Z_to_bv 64 ((asz + 1) mod 256))) 10%bv (Z_to_bv 64 1)) 8%bv (Z_to_bv 64 ch))
                              10%bv (Z_to_bv 64 (asz + 1))) 20%bv (Z_to_bv 64 n)) 21%bv (Z_to_bv 64 asz)) 10%bv (Z_to_bv 64 (asz - 1)))
                          (Z_to_bv 64 0x8d23c) M1 (seg_rom SEGS))).
      { eapply msteps_trans.
        { apply (prologue fx R M sp ret p Hsp Hra Ha0); [ok_sub HOK | lia]. }
        fold M1. norm_pc.
        lb_step F_8d1c0 D_8d1c0 (Z_to_bv 8 ((asz + 1) mod 256)) ltac:(rdn_fix B0).
        replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 ((asz + 1) mod 256)))) with (Z_to_bv 64 ((asz + 1) mod 256)) by (rewrite u8_of_Z by lia; reflexivity).
        stepiv F_8d1c4 D_8d1c4 (Z_to_bv 64 1) ltac:(gres; imm_norm; rewrite v_andi_Z by lia; rewrite odd_byte0 by lia; reflexivity).
        sv F_8d1c8 D_8d1c8 (Z_to_bv 64 ch).
        stepb_tk F_8d1cc D_8d1cc ltac:(rewrite c_eq_Z' by lia; reflexivity).
        ld_step F_8d1ec D_8d1ec (word_to_le_bytes 8 (Z_to_bv 64 (asz + 1))) (Z_to_bv 64 (asz + 1)) ltac:(rdn_fix G0') ltac:(b2z8).
        ld_step F_8d1f0 D_8d1f0 (word_to_le_bytes 8 (Z_to_bv 64 n)) (Z_to_bv 64 n) ltac:(rdn_fix G1') ltac:(b2z8).
        stepiv F_8d1f4 D_8d1f4 (Z_to_bv 64 asz)
          ltac:(gres; imm_norm; unfold v_andi; rewrite u64_of_Z by lia; change (bv_wrap 64 (-2)) with (2 ^ 64 - 2);
                rewrite land_m2_64 by lia; rewrite Hodd; f_equal; lia).
        stepiv F_8d1f8 D_8d1f8 (Z_to_bv 64 (asz - 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
        f_equal. apply bv_eq; vm_compute; reflexivity. }
      destruct (Z.lt_ge_cases n oc) as [LT|GE].
      +
        set (M2 := wbytes M1 (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n + 1)))).
        set (M3 := wbytes (wbytes M2 (Z_to_bv 64 (d + n)) [bch]) (Z_to_bv 64 (d + n + 1)) [Z_to_bv 8 0]).
        assert (ST13 : stores_in (fun a => zwin (sp - 64) sp a \/ zwin (p + 8) (p + 16) a \/ zwin (d + n) (d + n + 2) a) M M3).
        { unfold M3, M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1|] | | |] | | |] | | |];
            rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        * eapply msteps_trans; [exact PFX|].
          eapply msteps_trans.
          { norm_pc.
            stepb_tk F_8d1fc D_8d1fc ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            ld_step F_8d28c D_8d28c (word_to_le_bytes 8 (Z_to_bv 64 d)) (Z_to_bv 64 d) ltac:(rdn_fix G2') ltac:(b2z8).
            stepiv F_8d290 D_8d290 (Z_to_bv 64 (n + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stw F_8d294 D_8d294 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (n + 1)) ltac:(ok_mdef HDp1).
            apply mst_refl. }
          fold M2.
          lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 0x8d2d8) by (apply bv_eq; vm_compute; reflexivity) end.
          apply (epilogue fx _ M2 sp ret d n (Z_to_bv 64 ch)
                   (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv));
            [ gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity | lia | lia | lia | lia | unhide WINs; lia
            | | | | | | | | | | exact Hret ].
          -- unfold M2. ok_mdef HDs1.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL1.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL2.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL3.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL4.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL5.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL6.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL7.
          -- unfold M2. unhide WINp'. peel1. rdn_fix SL8.
        * fold M1. fold M2. fold bch. fold M3.
          eapply (CONT A _ M3 model (SLong d asz)).
          --   constructor.
             ++ eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST13 |].
                intros a [Hw|[Hhd|Hbk]]; [apply WIN | apply HDR | apply SRCsep]; unfold zwin in *; lia.
             ++ exact MS.
             ++ reflexivity.
             ++ reflexivity.
             ++ eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST13 |].
                intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x124000)] a)
                  by (destruct Ha as [Ha|[Ha|Ha]]; [apply WIN | apply HDR | apply SRCsep]; unfold zwin in Ha; lia).
                destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
             ++ intros r Hr; unfold callee_saved in Hr.
                repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption] |]). destruct Hr.
          --
             assert (AG3 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= sp - 64 \/ sp <= lo) -> (hi <= p + 8 \/ p + 16 <= lo) ->
                           (hi <= d + n \/ d + n + 2 <= lo) -> agree_on (zwin lo hi) M M3).
             { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact ST13|]. intros a Ha. unfold zwin in *. lia. }
             unfold CRep.str_rep. rewrite Zlen_app1, <- En. cbn [str_cap str_data].
             split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact ST13|exact HDp]|].
             split; [lia|].
             split. { split; [lia|]. split; [exact Hd16|]. split; [lia|]. split; [exact Hsz8|]. split; [unfold SSO_CAP; lia|].
                      split; [exact HIn|]. split; [exact Hdj|].
                      split. { eapply fld_agree; [lia|cbn; lia|exact G0|]. apply AG3; cbn; unhide WINp'; lia. }
                      split. { unfold fld, M3, M2. peel1. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
                      eapply fld_agree; [lia|cbn; lia|exact G2|]. apply AG3; cbn; unhide WINp'; lia. }
             split.
             ++ intros i Hi. destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
                ** rewrite Znth_app_l by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
                   eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG3; cbn; unhide WINs; lia.
                ** replace i with n by lia. rewrite En, Znth_app_r1, <- En. split; [exact Hchr|].
                   unfold fld, M3. peel1. rewrite <- Hbch.
                   change 1%nat with (length [bch]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
             ++ unfold fld, M3. replace (d + (n + 1)) with (d + n + 1) by lia.
                change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
                change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
          -- left. split; [exact LT|]. split; reflexivity.
          -- apply eff_store; [| exact (proj2 ST13)].
             intros a HF HW. apply (proj1 ST13). intros [Hw|[Hhd|Hbk]].
             ++ apply HW. unfold W_of, W, zwin in *. cbn. lia.
             ++ apply HF. left. unfold zwin in *. lia.
             ++ apply HF. right; left. cbn [sbuf_fp]. unfold zwin in *. lia.
      +
        assert (LEN : n = oc) by lia.
        destruct (ROOM LEN) as [HNMAX _]. cbn [str_grow] in HNMAX.
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        * eapply msteps_trans; [exact PFX|]. norm_pc.
          stepb_ft F_8d1fc D_8d1fc ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_eq; lia).
          stepiv F_8d200 D_8d200 (Z_to_bv 64 (2 ^ 64 - 8)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepb_ft F_8d204 D_8d204 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          ld_step F_8d208 D_8d208 (word_to_le_bytes 8 (Z_to_bv 64 d)) (Z_to_bv 64 d) ltac:(rdn_fix G2') ltac:(b2z8).
          stepiv F_8d20c D_8d20c (Z_to_bv 64 (2 ^ 64 - 27)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepiv F_8d210 D_8d210 (Z_to_bv 64 0x7ffffffffffffff2) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepb_ft F_8d214 D_8d214 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_8d218 D_8d218 (Z_to_bv 64 (2 * (asz - 1))) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^1) with 2; lia).
          stepiv F_8d21c D_8d21c (Z_to_bv 64 (2 * asz - 1))
            ltac:(gres; imm_norm; unfold v_ori; rewrite u64_of_Z by lia; change (bv_wrap 64 7) with 7; rewrite (str_grow_arith asz) by lia; reflexivity).
          sv F_8d220 D_8d220 (Z_to_bv 64 23).
          stepb_tk F_8d224 D_8d224 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          stepiv F_8d2cc D_8d2cc (Z_to_bv 64 (2 * asz)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          sv F_8d2d0 D_8d2d0 (Z_to_bv 64 12).
          stepb_tk F_8d2d4 D_8d2d4 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_8d1e4 D_8d1e4 (Z_to_bv 64 asz) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          stepj F_8d1e8 D_8d1e8.
          apply mst_refl.
        * lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x8d290) by (apply bv_eq; vm_compute; reflexivity); set (Rg := r) end.
          apply (GROW Rg LEN); unfold Rg; gres; try reflexivity; try assumption.
          -- rewrite Eoc. f_equal; lia.
          -- rewrite Eoc. f_equal; lia.
          -- intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity |]). destruct Hr.
  Qed.
End PushBack.
