(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_e1214_e126c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e1214 : bv 32 := 0x08b50663.
Lemma F_e1214 : fetch_word Plain.M.loaded_segments (0xe1248 : word) = Some W_e1214.
Proof. vm_refl. Qed.
Lemma D_e1214 : decode_any W_e1214 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1218 : bv 32 := 0x00a606b3.
Lemma F_e1218 : fetch_word Plain.M.loaded_segments (0xe124c : word) = Some W_e1218.
Proof. vm_refl. Qed.
Lemma D_e1218 : decode_any W_e1218 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_e121c : bv 32 := 0x00161713.
Lemma F_e121c : fetch_word Plain.M.loaded_segments (0xe1250 : word) = Some W_e121c.
Proof. vm_refl. Qed.
Lemma D_e121c : decode_any W_e121c = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1220 : bv 32 := 0x40d586b3.
Lemma F_e1220 : fetch_word Plain.M.loaded_segments (0xe1254 : word) = Some W_e1220.
Proof. vm_refl. Qed.
Lemma D_e1220 : decode_any W_e1220 = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1224 : bv 32 := 0x40e00733.
Lemma F_e1224 : fetch_word Plain.M.loaded_segments (0xe1258 : word) = Some W_e1224.
Proof. vm_refl. Qed.
Lemma D_e1224 : decode_any W_e1224 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1228 : bv 32 := 0x04d77063.
Lemma F_e1228 : fetch_word Plain.M.loaded_segments (0xe125c : word) = Some W_e1228.
Proof. vm_refl. Qed.
Lemma D_e1228 : decode_any W_e1228 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1268 : bv 32 := 0xba9ff06f.
Lemma F_e1268 : fetch_word Plain.M.loaded_segments (0xe129c : word) = Some W_e1268.
Proof. vm_refl. Qed.
Lemma D_e1268 : decode_any W_e1268 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.
End S1_code_e1214_e126c.

Module Lib_Musl_Memmove.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_PushBack.S1_code_e1214_e126c.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition MEMMOVE : Z := 0xe1248.

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

  Theorem memmove_spec : memmove_stmt SEGS MEMMOVE.
  Proof using.
    intros fx' mem0 dst src n bs rom regs ret MC Hn Hret H1 H10 H11 H12.
    destruct MC as [Hn0 Hlen Hsrc Hdst Hdisj Hnws Hnwd].
    pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.

    eapply (runs_trans SEGS _ (fun r => mkst r s1_memcpy_entry mem0 rom)
             (fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
                       /\ keeps regs r)).
    - eexists. split.
      + unfold MEMMOVE. norm_pc.
        stepb_ft F_e1214 D_e1214 ltac:(rewrite H10, H11; apply c_eq_neq; lia).
        stepn F_e1218 D_e1218.
        stepn F_e121c D_e121c.
        stepn F_e1220 D_e1220.
        stepn F_e1224 D_e1224.
        stepb_tk F_e1228 D_e1228 ltac:(idtac).
        { rewrite H10, H11, H12. unfold c_ltu, bv_ltu, v_sub, v_add, v_slli.
          rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small n), Z.mod_0_l by lia.
          apply memmove_test; lia. }
        stepj F_e1268 D_e1268. apply mst_refl.
      + cbv beta. gres. repeat split; try assumption.
        repeat (apply keeps_upd; [| cbv; intuition discriminate]). apply keeps_refl.
    - cbv beta. intros r1 (R1 & R10 & R11 & R12 & KR).
      destruct (s1_memcpy mem0 dst src n bs rom r1 ret (MCH _ _ _ _ _ _ Hn0 Hlen Hsrc Hdst Hdisj Hnws Hnwd)
                  Hret R1 R10 R11 R12) as (r2 & RUN & K2).
      exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.
End Memmove.
End Lib_Musl_Memmove.

Module S1_code_8b440_8b58c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8b440 : bv 32 := 0xfc010113.
Lemma F_8b440 : fetch_word Plain.M.loaded_segments (0x8b480 : word) = Some W_8b440.
Proof. vm_refl. Qed.
Lemma D_8b440 : decode_any W_8b440 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b444 : bv 32 := 0x02113c23.
Lemma F_8b444 : fetch_word Plain.M.loaded_segments (0x8b484 : word) = Some W_8b444.
Proof. vm_refl. Qed.
Lemma D_8b444 : decode_any W_8b444 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b448 : bv 32 := 0x02813823.
Lemma F_8b448 : fetch_word Plain.M.loaded_segments (0x8b488 : word) = Some W_8b448.
Proof. vm_refl. Qed.
Lemma D_8b448 : decode_any W_8b448 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b44c : bv 32 := 0x02913423.
Lemma F_8b44c : fetch_word Plain.M.loaded_segments (0x8b48c : word) = Some W_8b44c.
Proof. vm_refl. Qed.
Lemma D_8b44c : decode_any W_8b44c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b450 : bv 32 := 0x03213023.
Lemma F_8b450 : fetch_word Plain.M.loaded_segments (0x8b490 : word) = Some W_8b450.
Proof. vm_refl. Qed.
Lemma D_8b450 : decode_any W_8b450 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b454 : bv 32 := 0x01313c23.
Lemma F_8b454 : fetch_word Plain.M.loaded_segments (0x8b494 : word) = Some W_8b454.
Proof. vm_refl. Qed.
Lemma D_8b454 : decode_any W_8b454 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b458 : bv 32 := 0x01413823.
Lemma F_8b458 : fetch_word Plain.M.loaded_segments (0x8b498 : word) = Some W_8b458.
Proof. vm_refl. Qed.
Lemma D_8b458 : decode_any W_8b458 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b45c : bv 32 := 0x01513423.
Lemma F_8b45c : fetch_word Plain.M.loaded_segments (0x8b49c : word) = Some W_8b45c.
Proof. vm_refl. Qed.
Lemma D_8b45c : decode_any W_8b45c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b460 : bv 32 := 0x01613023.
Lemma F_8b460 : fetch_word Plain.M.loaded_segments (0x8b4a0 : word) = Some W_8b460.
Proof. vm_refl. Qed.
Lemma D_8b460 : decode_any W_8b460 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b464 : bv 32 := 0x00050493.
Lemma F_8b464 : fetch_word Plain.M.loaded_segments (0x8b4a4 : word) = Some W_8b464.
Proof. vm_refl. Qed.
Lemma D_8b464 : decode_any W_8b464 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b468 : bv 32 := 0x00054603.
Lemma F_8b468 : fetch_word Plain.M.loaded_segments (0x8b4a8 : word) = Some W_8b468.
Proof. vm_refl. Qed.
Lemma D_8b468 : decode_any W_8b468 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b46c : bv 32 := 0x00167513.
Lemma F_8b46c : fetch_word Plain.M.loaded_segments (0x8b4ac : word) = Some W_8b46c.
Proof. vm_refl. Qed.
Lemma D_8b46c : decode_any W_8b46c = Some (OpImm ALU_AND 10 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b470 : bv 32 := 0x00058413.
Lemma F_8b470 : fetch_word Plain.M.loaded_segments (0x8b4b0 : word) = Some W_8b470.
Proof. vm_refl. Qed.
Lemma D_8b470 : decode_any W_8b470 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b474 : bv 32 := 0x02051063.
Lemma F_8b474 : fetch_word Plain.M.loaded_segments (0x8b4b4 : word) = Some W_8b474.
Proof. vm_refl. Qed.
Lemma D_8b474 : decode_any W_8b474 = Some (Branch BC_NE 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b478 : bv 32 := 0x02c00513.
Lemma F_8b478 : fetch_word Plain.M.loaded_segments (0x8b4b8 : word) = Some W_8b478.
Proof. vm_refl. Qed.
Lemma D_8b478 : decode_any W_8b478 = Some (OpImm ALU_ADD 10 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b47c : bv 32 := 0x06a61263.
Lemma F_8b47c : fetch_word Plain.M.loaded_segments (0x8b4bc : word) = Some W_8b47c.
Proof. vm_refl. Qed.
Lemma D_8b47c : decode_any W_8b47c = Some (Branch BC_NE 12 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b480 : bv 32 := 0x00148913.
Lemma F_8b480 : fetch_word Plain.M.loaded_segments (0x8b4c0 : word) = Some W_8b480.
Proof. vm_refl. Qed.
Lemma D_8b480 : decode_any W_8b480 = Some (OpImm ALU_ADD 18 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b484 : bv 32 := 0x03000993.
Lemma F_8b484 : fetch_word Plain.M.loaded_segments (0x8b4c4 : word) = Some W_8b484.
Proof. vm_refl. Qed.
Lemma D_8b484 : decode_any W_8b484 = Some (OpImm ALU_ADD 19 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b488 : bv 32 := 0x01600513.
Lemma F_8b488 : fetch_word Plain.M.loaded_segments (0x8b4c8 : word) = Some W_8b488.
Proof. vm_refl. Qed.
Lemma D_8b488 : decode_any W_8b488 = Some (OpImm ALU_ADD 10 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b48c : bv 32 := 0x00150a93.
Lemma F_8b48c : fetch_word Plain.M.loaded_segments (0x8b4cc : word) = Some W_8b48c.
Proof. vm_refl. Qed.
Lemma D_8b48c : decode_any W_8b48c = Some (OpImm ALU_ADD 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b490 : bv 32 := 0x0680006f.
Lemma F_8b490 : fetch_word Plain.M.loaded_segments (0x8b4d0 : word) = Some W_8b490.
Proof. vm_refl. Qed.
Lemma D_8b490 : decode_any W_8b490 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b494 : bv 32 := 0x0004b503.
Lemma F_8b494 : fetch_word Plain.M.loaded_segments (0x8b4d4 : word) = Some W_8b494.
Proof. vm_refl. Qed.
Lemma D_8b494 : decode_any W_8b494 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b498 : bv 32 := 0x0084ba03.
Lemma F_8b498 : fetch_word Plain.M.loaded_segments (0x8b4d8 : word) = Some W_8b498.
Proof. vm_refl. Qed.
Lemma D_8b498 : decode_any W_8b498 = Some (Load SZ8 true 20 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b49c : bv 32 := 0xffe57a93.
Lemma F_8b49c : fetch_word Plain.M.loaded_segments (0x8b4dc : word) = Some W_8b49c.
Proof. vm_refl. Qed.
Lemma D_8b49c : decode_any W_8b49c = Some (OpImm ALU_AND 21 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4a0 : bv 32 := 0xfffa8513.
Lemma F_8b4a0 : fetch_word Plain.M.loaded_segments (0x8b4e0 : word) = Some W_8b4a0.
Proof. vm_refl. Qed.
Lemma D_8b4a0 : decode_any W_8b4a0 = Some (OpImm ALU_ADD 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4a4 : bv 32 := 0x08aa1863.
Lemma F_8b4a4 : fetch_word Plain.M.loaded_segments (0x8b4e4 : word) = Some W_8b4a4.
Proof. vm_refl. Qed.
Lemma D_8b4a4 : decode_any W_8b4a4 = Some (Branch BC_NE 20 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4a8 : bv 32 := 0xff800593.
Lemma F_8b4a8 : fetch_word Plain.M.loaded_segments (0x8b4e8 : word) = Some W_8b4a8.
Proof. vm_refl. Qed.
Lemma D_8b4a8 : decode_any W_8b4a8 = Some (OpImm ALU_ADD 11 0 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4ac : bv 32 := 0x0cba8e63.
Lemma F_8b4ac : fetch_word Plain.M.loaded_segments (0x8b4ec : word) = Some W_8b4ac.
Proof. vm_refl. Qed.
Lemma D_8b4ac : decode_any W_8b4ac = Some (Branch BC_EQ 21 11 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4b0 : bv 32 := 0x0104b903.
Lemma F_8b4b0 : fetch_word Plain.M.loaded_segments (0x8b4f0 : word) = Some W_8b4b0.
Proof. vm_refl. Qed.
Lemma D_8b4b0 : decode_any W_8b4b0 = Some (Load SZ8 true 18 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4b4 : bv 32 := 0xfe500593.
Lemma F_8b4b4 : fetch_word Plain.M.loaded_segments (0x8b4f4 : word) = Some W_8b4b4.
Proof. vm_refl. Qed.
Lemma D_8b4b4 : decode_any W_8b4b4 = Some (OpImm ALU_ADD 11 0 4069, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4b8 : bv 32 := 0x0015d593.
Lemma F_8b4b8 : fetch_word Plain.M.loaded_segments (0x8b4f8 : word) = Some W_8b4b8.
Proof. vm_refl. Qed.
Lemma D_8b4b8 : decode_any W_8b4b8 = Some (ShiftImm ALU_SRL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4bc : bv 32 := 0x02a5ec63.
Lemma F_8b4bc : fetch_word Plain.M.loaded_segments (0x8b4fc : word) = Some W_8b4bc.
Proof. vm_refl. Qed.
Lemma D_8b4bc : decode_any W_8b4bc = Some (Branch BC_LTU 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4c0 : bv 32 := 0x00151593.
Lemma F_8b4c0 : fetch_word Plain.M.loaded_segments (0x8b500 : word) = Some W_8b4c0.
Proof. vm_refl. Qed.
Lemma D_8b4c0 : decode_any W_8b4c0 = Some (ShiftImm ALU_SLL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4c4 : bv 32 := 0x0075e993.
Lemma F_8b4c4 : fetch_word Plain.M.loaded_segments (0x8b504 : word) = Some W_8b4c4.
Proof. vm_refl. Qed.
Lemma D_8b4c4 : decode_any W_8b4c4 = Some (OpImm ALU_OR 19 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4c8 : bv 32 := 0x01700593.
Lemma F_8b4c8 : fetch_word Plain.M.loaded_segments (0x8b508 : word) = Some W_8b4c8.
Proof. vm_refl. Qed.
Lemma D_8b4c8 : decode_any W_8b4c8 = Some (OpImm ALU_ADD 11 0 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4cc : bv 32 := 0x0ab99463.
Lemma F_8b4cc : fetch_word Plain.M.loaded_segments (0x8b50c : word) = Some W_8b4cc.
Proof. vm_refl. Qed.
Lemma D_8b4cc : decode_any W_8b4cc = Some (Branch BC_NE 19 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4e0 : bv 32 := 0x00165a13.
Lemma F_8b4e0 : fetch_word Plain.M.loaded_segments (0x8b520 : word) = Some W_8b4e0.
Proof. vm_refl. Qed.
Lemma D_8b4e0 : decode_any W_8b4e0 = Some (ShiftImm ALU_SRL 20 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4e4 : bv 32 := 0x00148513.
Lemma F_8b4e4 : fetch_word Plain.M.loaded_segments (0x8b524 : word) = Some W_8b4e4.
Proof. vm_refl. Qed.
Lemma D_8b4e4 : decode_any W_8b4e4 = Some (OpImm ALU_ADD 10 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4e8 : bv 32 := 0x00260613.
Lemma F_8b4e8 : fetch_word Plain.M.loaded_segments (0x8b528 : word) = Some W_8b4e8.
Proof. vm_refl. Qed.
Lemma D_8b4e8 : decode_any W_8b4e8 = Some (OpImm ALU_ADD 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4ec : bv 32 := 0x00c48023.
Lemma F_8b4ec : fetch_word Plain.M.loaded_segments (0x8b52c : word) = Some W_8b4ec.
Proof. vm_refl. Qed.
Lemma D_8b4ec : decode_any W_8b4ec = Some (Store SZ1 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4f0 : bv 32 := 0x0500006f.
Lemma F_8b4f0 : fetch_word Plain.M.loaded_segments (0x8b530 : word) = Some W_8b4f0.
Proof. vm_refl. Qed.
Lemma D_8b4f0 : decode_any W_8b4f0 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4f8 : bv 32 := 0x00050a13.
Lemma F_8b4f8 : fetch_word Plain.M.loaded_segments (0x8b538 : word) = Some W_8b4f8.
Proof. vm_refl. Qed.
Lemma D_8b4f8 : decode_any W_8b4f8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b4fc : bv 32 := 0x00098513.
Lemma F_8b4fc : fetch_word Plain.M.loaded_segments (0x8b53c : word) = Some W_8b4fc.
Proof. vm_refl. Qed.
Lemma D_8b4fc : decode_any W_8b4fc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b500 : bv 32 := 0x09d5a0ef.
Lemma F_8b500 : fetch_word Plain.M.loaded_segments (0x8b540 : word) = Some W_8b500.
Proof. vm_refl. Qed.
Lemma D_8b500 : decode_any W_8b500 = Some (Jal 1 370844, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b504 : bv 32 := 0x00050b13.
Lemma F_8b504 : fetch_word Plain.M.loaded_segments (0x8b544 : word) = Some W_8b504.
Proof. vm_refl. Qed.
Lemma D_8b504 : decode_any W_8b504 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b508 : bv 32 := 0x00090593.
Lemma F_8b508 : fetch_word Plain.M.loaded_segments (0x8b548 : word) = Some W_8b508.
Proof. vm_refl. Qed.
Lemma D_8b508 : decode_any W_8b508 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b50c : bv 32 := 0x000a0613.
Lemma F_8b50c : fetch_word Plain.M.loaded_segments (0x8b54c : word) = Some W_8b50c.
Proof. vm_refl. Qed.
Lemma D_8b50c : decode_any W_8b50c = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b510 : bv 32 := 0x4f9550ef.
Lemma F_8b510 : fetch_word Plain.M.loaded_segments (0x8b550 : word) = Some W_8b510.
Proof. vm_refl. Qed.
Lemma D_8b510 : decode_any W_8b510 = Some (Jal 1 351480, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b514 : bv 32 := 0x01700513.
Lemma F_8b514 : fetch_word Plain.M.loaded_segments (0x8b554 : word) = Some W_8b514.
Proof. vm_refl. Qed.
Lemma D_8b514 : decode_any W_8b514 = Some (OpImm ALU_ADD 10 0 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b518 : bv 32 := 0x00aa8863.
Lemma F_8b518 : fetch_word Plain.M.loaded_segments (0x8b558 : word) = Some W_8b518.
Proof. vm_refl. Qed.
Lemma D_8b518 : decode_any W_8b518 = Some (Branch BC_EQ 21 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b51c : bv 32 := 0x00090513.
Lemma F_8b51c : fetch_word Plain.M.loaded_segments (0x8b55c : word) = Some W_8b51c.
Proof. vm_refl. Qed.
Lemma D_8b51c : decode_any W_8b51c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b520 : bv 32 := 0x000a8593.
Lemma F_8b520 : fetch_word Plain.M.loaded_segments (0x8b560 : word) = Some W_8b520.
Proof. vm_refl. Qed.
Lemma D_8b520 : decode_any W_8b520 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b524 : bv 32 := 0xe10e20ef.
Lemma F_8b524 : fetch_word Plain.M.loaded_segments (0x8b564 : word) = Some W_8b524.
Proof. vm_refl. Qed.
Lemma D_8b524 : decode_any W_8b524 = Some (Jal 1 1975824, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b528 : bv 32 := 0x0019e513.
Lemma F_8b528 : fetch_word Plain.M.loaded_segments (0x8b568 : word) = Some W_8b528.
Proof. vm_refl. Qed.
Lemma D_8b528 : decode_any W_8b528 = Some (OpImm ALU_OR 10 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b52c : bv 32 := 0x00a4b023.
Lemma F_8b52c : fetch_word Plain.M.loaded_segments (0x8b56c : word) = Some W_8b52c.
Proof. vm_refl. Qed.
Lemma D_8b52c : decode_any W_8b52c = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b530 : bv 32 := 0x0164b823.
Lemma F_8b530 : fetch_word Plain.M.loaded_segments (0x8b570 : word) = Some W_8b530.
Proof. vm_refl. Qed.
Lemma D_8b530 : decode_any W_8b530 = Some (Store SZ8 9 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b534 : bv 32 := 0x0104b503.
Lemma F_8b534 : fetch_word Plain.M.loaded_segments (0x8b574 : word) = Some W_8b534.
Proof. vm_refl. Qed.
Lemma D_8b534 : decode_any W_8b534 = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b538 : bv 32 := 0x001a0593.
Lemma F_8b538 : fetch_word Plain.M.loaded_segments (0x8b578 : word) = Some W_8b538.
Proof. vm_refl. Qed.
Lemma D_8b538 : decode_any W_8b538 = Some (OpImm ALU_ADD 11 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b53c : bv 32 := 0x00b4b423.
Lemma F_8b53c : fetch_word Plain.M.loaded_segments (0x8b57c : word) = Some W_8b53c.
Proof. vm_refl. Qed.
Lemma D_8b53c : decode_any W_8b53c = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b540 : bv 32 := 0x01450533.
Lemma F_8b540 : fetch_word Plain.M.loaded_segments (0x8b580 : word) = Some W_8b540.
Proof. vm_refl. Qed.
Lemma D_8b540 : decode_any W_8b540 = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b544 : bv 32 := 0x00850023.
Lemma F_8b544 : fetch_word Plain.M.loaded_segments (0x8b584 : word) = Some W_8b544.
Proof. vm_refl. Qed.
Lemma D_8b544 : decode_any W_8b544 = Some (Store SZ1 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b548 : bv 32 := 0x000500a3.
Lemma F_8b548 : fetch_word Plain.M.loaded_segments (0x8b588 : word) = Some W_8b548.
Proof. vm_refl. Qed.
Lemma D_8b548 : decode_any W_8b548 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b54c : bv 32 := 0x03813083.
Lemma F_8b54c : fetch_word Plain.M.loaded_segments (0x8b58c : word) = Some W_8b54c.
Proof. vm_refl. Qed.
Lemma D_8b54c : decode_any W_8b54c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b550 : bv 32 := 0x03013403.
Lemma F_8b550 : fetch_word Plain.M.loaded_segments (0x8b590 : word) = Some W_8b550.
Proof. vm_refl. Qed.
Lemma D_8b550 : decode_any W_8b550 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b554 : bv 32 := 0x02813483.
Lemma F_8b554 : fetch_word Plain.M.loaded_segments (0x8b594 : word) = Some W_8b554.
Proof. vm_refl. Qed.
Lemma D_8b554 : decode_any W_8b554 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b558 : bv 32 := 0x02013903.
Lemma F_8b558 : fetch_word Plain.M.loaded_segments (0x8b598 : word) = Some W_8b558.
Proof. vm_refl. Qed.
Lemma D_8b558 : decode_any W_8b558 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b55c : bv 32 := 0x01813983.
Lemma F_8b55c : fetch_word Plain.M.loaded_segments (0x8b59c : word) = Some W_8b55c.
Proof. vm_refl. Qed.
Lemma D_8b55c : decode_any W_8b55c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b560 : bv 32 := 0x01013a03.
Lemma F_8b560 : fetch_word Plain.M.loaded_segments (0x8b5a0 : word) = Some W_8b560.
Proof. vm_refl. Qed.
Lemma D_8b560 : decode_any W_8b560 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b564 : bv 32 := 0x00813a83.
Lemma F_8b564 : fetch_word Plain.M.loaded_segments (0x8b5a4 : word) = Some W_8b564.
Proof. vm_refl. Qed.
Lemma D_8b564 : decode_any W_8b564 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b568 : bv 32 := 0x00013b03.
Lemma F_8b568 : fetch_word Plain.M.loaded_segments (0x8b5a8 : word) = Some W_8b568.
Proof. vm_refl. Qed.
Lemma D_8b568 : decode_any W_8b568 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b56c : bv 32 := 0x04010113.
Lemma F_8b56c : fetch_word Plain.M.loaded_segments (0x8b5ac : word) = Some W_8b56c.
Proof. vm_refl. Qed.
Lemma D_8b56c : decode_any W_8b56c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b570 : bv 32 := 0x00008067.
Lemma F_8b570 : fetch_word Plain.M.loaded_segments (0x8b5b0 : word) = Some W_8b570.
Proof. vm_refl. Qed.
Lemma D_8b570 : decode_any W_8b570 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b574 : bv 32 := 0x00198993.
Lemma F_8b574 : fetch_word Plain.M.loaded_segments (0x8b5b4 : word) = Some W_8b574.
Proof. vm_refl. Qed.
Lemma D_8b574 : decode_any W_8b574 = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b578 : bv 32 := 0x00c00593.
Lemma F_8b578 : fetch_word Plain.M.loaded_segments (0x8b5b8 : word) = Some W_8b578.
Proof. vm_refl. Qed.
Lemma D_8b578 : decode_any W_8b578 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b57c : bv 32 := 0xf0b578e3.
Lemma F_8b57c : fetch_word Plain.M.loaded_segments (0x8b5bc : word) = Some W_8b57c.
Proof. vm_refl. Qed.
Lemma D_8b57c : decode_any W_8b57c = Some (Branch BC_GEU 10 11 7952, 4%Z).
Proof. vm_refl. Qed.
End S1_code_8b440_8b58c.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemcpyBase SumMemcpy LibMaskBits S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts S1Facts Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_PushBack.Lib_Musl_Memmove. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_PushBack.S1_code_8b440_8b58c.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
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
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b480) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd R 2%bv (Z_to_bv 64 (sp - 64))) 9%bv (Z_to_bv 64 p))
                          (Z_to_bv 64 0x8b4a8) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret p Hsp Hra Ha0 HOK Hsp'.
    norm_pc.
    sv F_8b440 D_8b440 (Z_to_bv 64 (sp - 64)).
    stw F_8b444 D_8b444 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
    stw F_8b448 D_8b448 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
    stw F_8b44c D_8b44c (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
    stw F_8b450 D_8b450 (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
    stw F_8b454 D_8b454 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
    stw F_8b458 D_8b458 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
    stw F_8b45c D_8b45c (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
    stw F_8b460 D_8b460 (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
    sv F_8b464 D_8b464 (Z_to_bv 64 p).
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
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b580) M (seg_rom SEGS))
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
    stepiv F_8b540 D_8b540 (Z_to_bv 64 (x + len)) ltac:(gres; rewrite Ha0, Hs4; rewrite v_add_Z by lia; reflexivity).
    stw F_8b544 D_8b544 (Z_to_bv 64 (x + len)) chv ltac:(ok_sub HOKx).
    stw F_8b548 D_8b548 (Z_to_bv 64 (x + len + 1)) (Z_to_bv 64 0) ltac:(ok_sub HOKx).
    ld_step F_8b54c D_8b54c (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(peel1; rdn_fix L1) ltac:(b2z8).
    ld_step F_8b550 D_8b550 (word_to_le_bytes 8 v8) v8 ltac:(peel1; rdn_fix L8) ltac:(b2z8).
    ld_step F_8b554 D_8b554 (word_to_le_bytes 8 v9) v9 ltac:(peel1; rdn_fix L9) ltac:(b2z8).
    ld_step F_8b558 D_8b558 (word_to_le_bytes 8 v18) v18 ltac:(peel1; rdn_fix L18) ltac:(b2z8).
    ld_step F_8b55c D_8b55c (word_to_le_bytes 8 v19) v19 ltac:(peel1; rdn_fix L19) ltac:(b2z8).
    ld_step F_8b560 D_8b560 (word_to_le_bytes 8 v20) v20 ltac:(peel1; rdn_fix L20) ltac:(b2z8).
    ld_step F_8b564 D_8b564 (word_to_le_bytes 8 v21) v21 ltac:(peel1; rdn_fix L21) ltac:(b2z8).
    ld_step F_8b568 D_8b568 (word_to_le_bytes 8 v22) v22 ltac:(peel1; rdn_fix L22) ltac:(b2z8).
    sv F_8b56c D_8b56c (Z_to_bv 64 sp).
    stepjr F_8b570 D_8b570 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.
  Definition c8b3ec : str_consts :=
    {| sc_push_back := 0x8b480; sc_resize := 0x8b8b4; sc_makestring := 0x6602c;
       sc_push_stack := 64; sc_resize_stack := 80; sc_ms_stack := 128 |}.

  Theorem str_push_back_8b3ec_spec : str_push_back_stmt SEGS Ly.L MI ST c8b3ec.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret p ch m cs K.
    cbn [sc_push_back sc_push_stack c8b3ec]. lazy zeta.
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
                  /\ (forall a, src <= a < src + oc + 1 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a)).
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
    assert (HDR : forall a, p <= a < p + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. exact (placed_sep A M model p 24 a AI PLp Ha). }
    assert (WIN : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
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
      srealizes SEGS (mkCfg (@mkst fx Rg (Z_to_bv 64 0x8b538) M1 (seg_rom SEGS)) model) K).
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
        msteps SEGS (@mkst fx Rg (Z_to_bv 64 0x8b538) M1 (seg_rom SEGS))
                    (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) M1 (seg_rom SEGS))
        /\ getr Rn 10%bv = Z_to_bv 64 ng /\ getr Rn 1%bv = Z_to_bv 64 0x8b544
        /\ getr Rn 2%bv = Z_to_bv 64 (sp - 64) /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
        /\ getr Rn 8%bv = Z_to_bv 64 ch /\ getr Rn 9%bv = Z_to_bv 64 p /\ getr Rn 18%bv = Z_to_bv 64 src
        /\ getr Rn 19%bv = Z_to_bv 64 ng /\ getr Rn 20%bv = Z_to_bv 64 oc /\ getr Rn 21%bv = Z_to_bv 64 (oc + 1)
        /\ (forall r, In r [23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r)).
      { eexists. split.
        - norm_pc.
          sv F_8b4f8 D_8b4f8 (Z_to_bv 64 oc).
          sv F_8b4fc D_8b4fc (Z_to_bv 64 ng).
          stepj F_8b500 D_8b500.
          lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
          f_equal. apply bv_eq; vm_compute; reflexivity.
        - gres. repeat split; try reflexivity; try assumption.
          intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply RgS; exact Hr'|]). destruct Hr. }
      destruct B2 as (Rn & RUN2 & Rn10 & Rn1 & Rn2 & Rn3 & Rn4 & Rn8 & Rn9 & Rn18 & Rn19 & Rn20 & Rn21 & RnS).
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN2 | ].
      eapply (NEW fx A s Rn M1 model ng (sp - 64) 0x8b544 K).
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
        assert (Hqown : forall a, q <= a < q + ng -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
        assert (LIVE1 : forall blk, In blk (live MI A) -> In blk (live MI A1)) by (intros blk Hblk; eapply live_add_keeps; eassumption).
        assert (PLp1 : placed MI A1 p 24) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
        assert (PLs1 : placed MI A1 src (oc + 1)) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
        assert (HDRq : p + 24 <= q \/ q + ng <= p).
        { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 p 24 q ng AI AI1 PLp LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
        assert (SRCq : src + oc + 1 <= q \/ q + ng <= src).
        { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 src (oc + 1) q ng AI AI1 PLs LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
        hide HDRq. hide SRCq.
        assert (WIN1 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. apply (stack_sep A1 M2 model1 a AI1). lia. }
        assert (HDR1 : forall a, p <= a < p + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. exact (placed_sep A1 M2 model1 p 24 a AI1 PLp1 Ha). }
        assert (SRC1 : forall a, src <= a < src + oc + 1 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
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
          sv F_8b504 D_8b504 (Z_to_bv 64 q).
          sv F_8b508 D_8b508 (Z_to_bv 64 src).
          sv F_8b50c D_8b50c (Z_to_bv 64 oc).
          stepj F_8b510 D_8b510.
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
        destruct (memmove_spec fx M2 (Z_to_bv 64 q) (Z_to_bv 64 src) oc (str_bytes cs) (seg_rom SEGS) R3 (Z_to_bv 64 0x8b554)
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
          (forall a, p <= a < p + 24 -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x122000)] a) ->
          eff MI A A2 M M6 W FT -> lapply (live MI A) (LAdd q ng :: sbuf_del m) (live MI A2) ->
          srealizes SEGS (mkCfg (@mkst fx R6 (Z_to_bv 64 0x8b568) M6 (seg_rom SEGS)) model2) K).
        { intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 SX2 R6_2 R6_8 R6_9 R6_19 R6_20 R6_22 R6_3 R6_4 R6S AG6 HDp6 HDq6 CS6 HinQ2 HDR2 EFF6 LAP.
          assert (SLT : forall a vv, sp - 64 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some vv).
          { intros a vv H1 H2 H3. rewrite (rdn_agree_win SEGS M1 M6); [exact H3 | lia | cbn; lia |].
            eapply agree_on_weaken; [exact AG6|]. intros a' Ha. unfold zwin in *. cbn in Ha. lia. }
          assert (WIN2 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
          { intros a Ha. apply (stack_sep A2 M6 model2 a AI2). lia. }
          assert (Hqown2 : forall a, q <= a < q + ng -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
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
              stepiv F_8b528 D_8b528 (Z_to_bv 64 (ng + 1))
                ltac:(gres; rewrite R6_19; unfold v_ori; rewrite u64_of_Z by lia; imm_norm; change (bv_wrap 64 1) with 1; rewrite Hng1; reflexivity).
              stw F_8b52c D_8b52c (Z_to_bv 64 p) (Z_to_bv 64 (ng + 1)) ltac:(ok_mdef HDp6).
              stw F_8b530 D_8b530 (Z_to_bv 64 (p + 16)) (Z_to_bv 64 q) ltac:(ok_mdef HDp6).
              ld_step F_8b534 D_8b534 (word_to_le_bytes 8 (Z_to_bv 64 q)) (Z_to_bv 64 q)
                ltac:(peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia) ltac:(b2z8).
              stepiv F_8b538 D_8b538 (Z_to_bv 64 (oc + 1)) ltac:(gres; rewrite R6_20; imm_norm; rewrite v_addi_Z by lia; reflexivity).
              stw F_8b53c D_8b53c (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (oc + 1)) ltac:(ok_mdef HDp6).
              apply mst_refl.
            - fold M7.
              lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
                replace pc with (Z_to_bv 64 0x8b580) by (apply bv_eq; vm_compute; reflexivity) end.
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
              intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x122000)] a)
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
          { norm_pc. sv F_8b514 D_8b514 (Z_to_bv 64 23).
            stepb_tk F_8b518 D_8b518 ltac:(rewrite R4_21, Eoc; apply c_eq_refl). apply mst_refl. }
          lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x8b568) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
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
          { norm_pc. sv F_8b514 D_8b514 (Z_to_bv 64 23).
            stepb_ft F_8b518 D_8b518 ltac:(rewrite R4_21; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            sv F_8b51c D_8b51c (Z_to_bv 64 d).
            sv F_8b520 D_8b520 (Z_to_bv 64 asz).
            stepj F_8b524 D_8b524. apply mst_refl. }
          lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 DEL1) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
          eapply (op_delete1_spec MI fx A1 R5 M3 model1 d asz (sp - 64) 0x8b568 K).
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
            lb_step F_8b468 D_8b468 (Z_to_bv 8 (2 * n)) ltac:(rdn_fix B0).
            replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * n)))) with (Z_to_bv 64 (2 * n)) by (rewrite u8_of_Z by lia; reflexivity).
            stepiv F_8b46c D_8b46c (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
            sv F_8b470 D_8b470 (Z_to_bv 64 ch).
            stepb_ft F_8b474 D_8b474 ltac:(apply c_eq_refl).
            sv F_8b478 D_8b478 (Z_to_bv 64 44).
            stepb_tk F_8b47c D_8b47c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            stepiv F_8b4e0 D_8b4e0 (Z_to_bv 64 n) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; change (2^1) with 2; rewrite Z.mul_comm; apply Z.div_mul; lia).
            stepiv F_8b4e4 D_8b4e4 (Z_to_bv 64 (p + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stepiv F_8b4e8 D_8b4e8 (Z_to_bv 64 (2 * n + 2)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stw F_8b4ec D_8b4ec (Z_to_bv 64 p) (Z_to_bv 64 (2 * n + 2)) ltac:(ok_mdef HDp1).
            stepj F_8b4f0 D_8b4f0.
            apply mst_refl. }
          fold M2.
          lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 0x8b580) by (apply bv_eq; vm_compute; reflexivity) end.
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
                intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x122000)] a)
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
          lb_step F_8b468 D_8b468 (Z_to_bv 8 (2 * n)) ltac:(rdn_fix B0).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * n)))) with (Z_to_bv 64 (2 * n)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b46c D_8b46c (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
          sv F_8b470 D_8b470 (Z_to_bv 64 ch).
          stepb_ft F_8b474 D_8b474 ltac:(apply c_eq_refl).
          sv F_8b478 D_8b478 (Z_to_bv 64 44).
          stepb_ft F_8b47c D_8b47c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_eq; lia).
          stepiv F_8b480 D_8b480 (Z_to_bv 64 (p + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          sv F_8b484 D_8b484 (Z_to_bv 64 48).
          sv F_8b488 D_8b488 (Z_to_bv 64 22).
          sv F_8b48c D_8b48c (Z_to_bv 64 23).
          stepj F_8b490 D_8b490.
          apply mst_refl.
        * lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x8b538) by (apply bv_eq; vm_compute; reflexivity); set (Rg := r) end.
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

      assert (PFX : msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b480) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                              2%bv (Z_to_bv 64 (sp - 64))) 9%bv (Z_to_bv 64 p))
                              12%bv (Z_to_bv 64 ((asz + 1) mod 256))) 10%bv (Z_to_bv 64 1)) 8%bv (Z_to_bv 64 ch))
                              10%bv (Z_to_bv 64 (asz + 1))) 20%bv (Z_to_bv 64 n)) 21%bv (Z_to_bv 64 asz)) 10%bv (Z_to_bv 64 (asz - 1)))
                          (Z_to_bv 64 0x8b4e4) M1 (seg_rom SEGS))).
      { eapply msteps_trans.
        { apply (prologue fx R M sp ret p Hsp Hra Ha0); [ok_sub HOK | lia]. }
        fold M1. norm_pc.
        lb_step F_8b468 D_8b468 (Z_to_bv 8 ((asz + 1) mod 256)) ltac:(rdn_fix B0).
        replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 ((asz + 1) mod 256)))) with (Z_to_bv 64 ((asz + 1) mod 256)) by (rewrite u8_of_Z by lia; reflexivity).
        stepiv F_8b46c D_8b46c (Z_to_bv 64 1) ltac:(gres; imm_norm; rewrite v_andi_Z by lia; rewrite odd_byte0 by lia; reflexivity).
        sv F_8b470 D_8b470 (Z_to_bv 64 ch).
        stepb_tk F_8b474 D_8b474 ltac:(rewrite c_eq_Z' by lia; reflexivity).
        ld_step F_8b494 D_8b494 (word_to_le_bytes 8 (Z_to_bv 64 (asz + 1))) (Z_to_bv 64 (asz + 1)) ltac:(rdn_fix G0') ltac:(b2z8).
        ld_step F_8b498 D_8b498 (word_to_le_bytes 8 (Z_to_bv 64 n)) (Z_to_bv 64 n) ltac:(rdn_fix G1') ltac:(b2z8).
        stepiv F_8b49c D_8b49c (Z_to_bv 64 asz)
          ltac:(gres; imm_norm; unfold v_andi; rewrite u64_of_Z by lia; change (bv_wrap 64 (-2)) with (2 ^ 64 - 2);
                rewrite land_m2_64 by lia; rewrite Hodd; f_equal; lia).
        stepiv F_8b4a0 D_8b4a0 (Z_to_bv 64 (asz - 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
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
            stepb_tk F_8b4a4 D_8b4a4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            ld_step F_8b534 D_8b534 (word_to_le_bytes 8 (Z_to_bv 64 d)) (Z_to_bv 64 d) ltac:(rdn_fix G2') ltac:(b2z8).
            stepiv F_8b538 D_8b538 (Z_to_bv 64 (n + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stw F_8b53c D_8b53c (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (n + 1)) ltac:(ok_mdef HDp1).
            apply mst_refl. }
          fold M2.
          lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 0x8b580) by (apply bv_eq; vm_compute; reflexivity) end.
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
                intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x122000)] a)
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
          stepb_ft F_8b4a4 D_8b4a4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_eq; lia).
          stepiv F_8b4a8 D_8b4a8 (Z_to_bv 64 (2 ^ 64 - 8)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepb_ft F_8b4ac D_8b4ac ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          ld_step F_8b4b0 D_8b4b0 (word_to_le_bytes 8 (Z_to_bv 64 d)) (Z_to_bv 64 d) ltac:(rdn_fix G2') ltac:(b2z8).
          stepiv F_8b4b4 D_8b4b4 (Z_to_bv 64 (2 ^ 64 - 27)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepiv F_8b4b8 D_8b4b8 (Z_to_bv 64 0x7ffffffffffffff2) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
          stepb_ft F_8b4bc D_8b4bc ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_8b4c0 D_8b4c0 (Z_to_bv 64 (2 * (asz - 1))) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^1) with 2; lia).
          stepiv F_8b4c4 D_8b4c4 (Z_to_bv 64 (2 * asz - 1))
            ltac:(gres; imm_norm; unfold v_ori; rewrite u64_of_Z by lia; change (bv_wrap 64 7) with 7; rewrite (str_grow_arith asz) by lia; reflexivity).
          sv F_8b4c8 D_8b4c8 (Z_to_bv 64 23).
          stepb_tk F_8b4cc D_8b4cc ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          stepiv F_8b574 D_8b574 (Z_to_bv 64 (2 * asz)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          sv F_8b578 D_8b578 (Z_to_bv 64 12).
          stepb_tk F_8b57c D_8b57c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_8b48c D_8b48c (Z_to_bv 64 asz) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          stepj F_8b490 D_8b490.
          apply mst_refl.
        * lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x8b538) by (apply bv_eq; vm_compute; reflexivity); set (Rg := r) end.
          apply (GROW Rg LEN); unfold Rg; gres; try reflexivity; try assumption.
          -- rewrite Eoc. f_equal; lia.
          -- rewrite Eoc. f_equal; lia.
          -- intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity |]). destruct Hr.
  Qed.
End PushBack.
