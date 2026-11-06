(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushU8.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13850 : bv 32 := 0xffffe517.
Lemma F_13850 : fetch_word Ubsan.M.loaded_segments (0x13850 : word) = Some W_13850.
Proof. vm_refl. Qed.
Lemma D_13850 : decode_any W_13850 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13854 : bv 32 := 0x4e850513.
Lemma F_13854 : fetch_word Ubsan.M.loaded_segments (0x13854 : word) = Some W_13854.
Proof. vm_refl. Qed.
Lemma D_13854 : decode_any W_13854 = Some (OpImm ALU_ADD 10 10 1256, 4%Z).
Proof. vm_refl. Qed.

Definition W_13858 : bv 32 := 0x0000e597.
Lemma F_13858 : fetch_word Ubsan.M.loaded_segments (0x13858 : word) = Some W_13858.
Proof. vm_refl. Qed.
Lemma D_13858 : decode_any W_13858 = Some (Auipc 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1385c : bv 32 := 0x1d058593.
Lemma F_1385c : fetch_word Ubsan.M.loaded_segments (0x1385c : word) = Some W_1385c.
Proof. vm_refl. Qed.
Lemma D_1385c : decode_any W_1385c = Some (OpImm ALU_ADD 11 11 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_13860 : bv 32 := 0x000000ef.
Lemma F_13860 : fetch_word Ubsan.M.loaded_segments (0x13860 : word) = Some W_13860.
Proof. vm_refl. Qed.
Lemma D_13860 : decode_any W_13860 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13864 : bv 32 := 0x0040006f.
Lemma F_13864 : fetch_word Ubsan.M.loaded_segments (0x13864 : word) = Some W_13864.
Proof. vm_refl. Qed.
Lemma D_13864 : decode_any W_13864 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13868 : bv 32 := 0x00813083.
Lemma F_13868 : fetch_word Ubsan.M.loaded_segments (0x13868 : word) = Some W_13868.
Proof. vm_refl. Qed.
Lemma D_13868 : decode_any W_13868 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1386c : bv 32 := 0x00013403.
Lemma F_1386c : fetch_word Ubsan.M.loaded_segments (0x1386c : word) = Some W_1386c.
Proof. vm_refl. Qed.
Lemma D_1386c : decode_any W_1386c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13870 : bv 32 := 0x01010113.
Lemma F_13870 : fetch_word Ubsan.M.loaded_segments (0x13870 : word) = Some W_13870.
Proof. vm_refl. Qed.
Lemma D_13870 : decode_any W_13870 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13874 : bv 32 := 0x00008067.
Lemma F_13874 : fetch_word Ubsan.M.loaded_segments (0x13874 : word) = Some W_13874.
Proof. vm_refl. Qed.
Lemma D_13874 : decode_any W_13874 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13878 : bv 32 := 0xff010113.
Lemma F_13878 : fetch_word Ubsan.M.loaded_segments (0x13878 : word) = Some W_13878.
Proof. vm_refl. Qed.
Lemma D_13878 : decode_any W_13878 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1387c : bv 32 := 0x00113423.
Lemma F_1387c : fetch_word Ubsan.M.loaded_segments (0x1387c : word) = Some W_1387c.
Proof. vm_refl. Qed.
Lemma D_1387c : decode_any W_1387c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13880 : bv 32 := 0x00813023.
Lemma F_13880 : fetch_word Ubsan.M.loaded_segments (0x13880 : word) = Some W_13880.
Proof. vm_refl. Qed.
Lemma D_13880 : decode_any W_13880 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13884 : bv 32 := 0x01010413.
Lemma F_13884 : fetch_word Ubsan.M.loaded_segments (0x13884 : word) = Some W_13884.
Proof. vm_refl. Qed.
Lemma D_13884 : decode_any W_13884 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13888 : bv 32 := 0x0000e517.
Lemma F_13888 : fetch_word Ubsan.M.loaded_segments (0x13888 : word) = Some W_13888.
Proof. vm_refl. Qed.
Lemma D_13888 : decode_any W_13888 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1388c : bv 32 := 0x1e050513.
Lemma F_1388c : fetch_word Ubsan.M.loaded_segments (0x1388c : word) = Some W_1388c.
Proof. vm_refl. Qed.
Lemma D_1388c : decode_any W_1388c = Some (OpImm ALU_ADD 10 10 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_13890 : bv 32 := 0x00054503.
Lemma F_13890 : fetch_word Ubsan.M.loaded_segments (0x13890 : word) = Some W_13890.
Proof. vm_refl. Qed.
Lemma D_13890 : decode_any W_13890 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13894 : bv 32 := 0x00157513.
Lemma F_13894 : fetch_word Ubsan.M.loaded_segments (0x13894 : word) = Some W_13894.
Proof. vm_refl. Qed.
Lemma D_13894 : decode_any W_13894 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13898 : bv 32 := 0x00050663.
Lemma F_13898 : fetch_word Ubsan.M.loaded_segments (0x13898 : word) = Some W_13898.
Proof. vm_refl. Qed.
Lemma D_13898 : decode_any W_13898 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1389c : bv 32 := 0x0040006f.
Lemma F_1389c : fetch_word Ubsan.M.loaded_segments (0x1389c : word) = Some W_1389c.
Proof. vm_refl. Qed.
Lemma D_1389c : decode_any W_1389c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_138a0 : bv 32 := 0x0580006f.
Lemma F_138a0 : fetch_word Ubsan.M.loaded_segments (0x138a0 : word) = Some W_138a0.
Proof. vm_refl. Qed.
Lemma D_138a0 : decode_any W_138a0 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_138a4 : bv 32 := 0x0000e517.
Lemma F_138a4 : fetch_word Ubsan.M.loaded_segments (0x138a4 : word) = Some W_138a4.
Proof. vm_refl. Qed.
Lemma D_138a4 : decode_any W_138a4 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_138a8 : bv 32 := 0x1c450593.
Lemma F_138a8 : fetch_word Ubsan.M.loaded_segments (0x138a8 : word) = Some W_138a8.
Proof. vm_refl. Qed.
Lemma D_138a8 : decode_any W_138a8 = Some (OpImm ALU_ADD 11 10 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_138ac : bv 32 := 0x00100513.
Lemma F_138ac : fetch_word Ubsan.M.loaded_segments (0x138ac : word) = Some W_138ac.
Proof. vm_refl. Qed.
Lemma D_138ac : decode_any W_138ac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_138b0 : bv 32 := 0x00a58023.
Lemma F_138b0 : fetch_word Ubsan.M.loaded_segments (0x138b0 : word) = Some W_138b0.
Proof. vm_refl. Qed.
Lemma D_138b0 : decode_any W_138b0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138b4 : bv 32 := 0x0000d517.
Lemma F_138b4 : fetch_word Ubsan.M.loaded_segments (0x138b4 : word) = Some W_138b4.
Proof. vm_refl. Qed.
Lemma D_138b4 : decode_any W_138b4 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_138b8 : bv 32 := 0xec453503.
Lemma F_138b8 : fetch_word Ubsan.M.loaded_segments (0x138b8 : word) = Some W_138b8.
Proof. vm_refl. Qed.
Lemma D_138b8 : decode_any W_138b8 = Some (Load SZ8 true 10 10 3780, 4%Z).
Proof. vm_refl. Qed.

Definition W_138bc : bv 32 := 0x00050e63.
Lemma F_138bc : fetch_word Ubsan.M.loaded_segments (0x138bc : word) = Some W_138bc.
Proof. vm_refl. Qed.
Lemma D_138bc : decode_any W_138bc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_138c0 : bv 32 := 0x0040006f.
Lemma F_138c0 : fetch_word Ubsan.M.loaded_segments (0x138c0 : word) = Some W_138c0.
Proof. vm_refl. Qed.
Lemma D_138c0 : decode_any W_138c0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_138c4 : bv 32 := 0x0000e517.
Lemma F_138c4 : fetch_word Ubsan.M.loaded_segments (0x138c4 : word) = Some W_138c4.
Proof. vm_refl. Qed.
Lemma D_138c4 : decode_any W_138c4 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_138c8 : bv 32 := 0xf2450513.
Lemma F_138c8 : fetch_word Ubsan.M.loaded_segments (0x138c8 : word) = Some W_138c8.
Proof. vm_refl. Qed.
Lemma D_138c8 : decode_any W_138c8 = Some (OpImm ALU_ADD 10 10 3876, 4%Z).
Proof. vm_refl. Qed.

Definition W_138cc : bv 32 := 0x00053503.
Lemma F_138cc : fetch_word Ubsan.M.loaded_segments (0x138cc : word) = Some W_138cc.
Proof. vm_refl. Qed.
Lemma D_138cc : decode_any W_138cc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138d0 : bv 32 := 0x731030ef.
Lemma F_138d0 : fetch_word Ubsan.M.loaded_segments (0x138d0 : word) = Some W_138d0.
Proof. vm_refl. Qed.
Lemma D_138d0 : decode_any W_138d0 = Some (Jal 1 16176, 4%Z).
Proof. vm_refl. Qed.

Definition W_138d4 : bv 32 := 0x0040006f.
Lemma F_138d4 : fetch_word Ubsan.M.loaded_segments (0x138d4 : word) = Some W_138d4.
Proof. vm_refl. Qed.
Lemma D_138d4 : decode_any W_138d4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_138d8 : bv 32 := 0x0000d517.
Lemma F_138d8 : fetch_word Ubsan.M.loaded_segments (0x138d8 : word) = Some W_138d8.
Proof. vm_refl. Qed.
Lemma D_138d8 : decode_any W_138d8 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_138dc : bv 32 := 0xea853503.
Lemma F_138dc : fetch_word Ubsan.M.loaded_segments (0x138dc : word) = Some W_138dc.
Proof. vm_refl. Qed.
Lemma D_138dc : decode_any W_138dc = Some (Load SZ8 true 10 10 3752, 4%Z).
Proof. vm_refl. Qed.

Definition W_138e0 : bv 32 := 0x00050c63.
Lemma F_138e0 : fetch_word Ubsan.M.loaded_segments (0x138e0 : word) = Some W_138e0.
Proof. vm_refl. Qed.
Lemma D_138e0 : decode_any W_138e0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_138e4 : bv 32 := 0x0040006f.
Lemma F_138e4 : fetch_word Ubsan.M.loaded_segments (0x138e4 : word) = Some W_138e4.
Proof. vm_refl. Qed.
Lemma D_138e4 : decode_any W_138e4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_138e8 : bv 32 := 0xffffe517.
Lemma F_138e8 : fetch_word Ubsan.M.loaded_segments (0x138e8 : word) = Some W_138e8.
Proof. vm_refl. Qed.
Lemma D_138e8 : decode_any W_138e8 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_138ec : bv 32 := 0x45050513.
Lemma F_138ec : fetch_word Ubsan.M.loaded_segments (0x138ec : word) = Some W_138ec.
Proof. vm_refl. Qed.
Lemma D_138ec : decode_any W_138ec = Some (OpImm ALU_ADD 10 10 1104, 4%Z).
Proof. vm_refl. Qed.

Definition W_138f0 : bv 32 := 0x000000ef.
Lemma F_138f0 : fetch_word Ubsan.M.loaded_segments (0x138f0 : word) = Some W_138f0.
Proof. vm_refl. Qed.
Lemma D_138f0 : decode_any W_138f0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138f4 : bv 32 := 0x0040006f.
Lemma F_138f4 : fetch_word Ubsan.M.loaded_segments (0x138f4 : word) = Some W_138f4.
Proof. vm_refl. Qed.
Lemma D_138f4 : decode_any W_138f4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_138f8 : bv 32 := 0x00813083.
Lemma F_138f8 : fetch_word Ubsan.M.loaded_segments (0x138f8 : word) = Some W_138f8.
Proof. vm_refl. Qed.
Lemma D_138f8 : decode_any W_138f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_138fc : bv 32 := 0x00013403.
Lemma F_138fc : fetch_word Ubsan.M.loaded_segments (0x138fc : word) = Some W_138fc.
Proof. vm_refl. Qed.
Lemma D_138fc : decode_any W_138fc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13900 : bv 32 := 0x01010113.
Lemma F_13900 : fetch_word Ubsan.M.loaded_segments (0x13900 : word) = Some W_13900.
Proof. vm_refl. Qed.
Lemma D_13900 : decode_any W_13900 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13904 : bv 32 := 0x00008067.
Lemma F_13904 : fetch_word Ubsan.M.loaded_segments (0x13904 : word) = Some W_13904.
Proof. vm_refl. Qed.
Lemma D_13904 : decode_any W_13904 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d30 : bv 32 := 0x0001e517.
Lemma F_13d30 : fetch_word Ubsan.M.loaded_segments (0x13d30 : word) = Some W_13d30.
Proof. vm_refl. Qed.
Lemma D_13d30 : decode_any W_13d30 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d34 : bv 32 := 0xd4454503.
Lemma F_13d34 : fetch_word Ubsan.M.loaded_segments (0x13d34 : word) = Some W_13d34.
Proof. vm_refl. Qed.
Lemma D_13d34 : decode_any W_13d34 = Some (Load SZ1 false 10 10 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d38 : bv 32 := 0x00051463.
Lemma F_13d38 : fetch_word Ubsan.M.loaded_segments (0x13d38 : word) = Some W_13d38.
Proof. vm_refl. Qed.
Lemma D_13d38 : decode_any W_13d38 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d3c : bv 32 := 0x00008067.
Lemma F_13d3c : fetch_word Ubsan.M.loaded_segments (0x13d3c : word) = Some W_13d3c.
Proof. vm_refl. Qed.
Lemma D_13d3c : decode_any W_13d3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d40 : bv 32 := 0xff010113.
Lemma F_13d40 : fetch_word Ubsan.M.loaded_segments (0x13d40 : word) = Some W_13d40.
Proof. vm_refl. Qed.
Lemma D_13d40 : decode_any W_13d40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d44 : bv 32 := 0x00113423.
Lemma F_13d44 : fetch_word Ubsan.M.loaded_segments (0x13d44 : word) = Some W_13d44.
Proof. vm_refl. Qed.
Lemma D_13d44 : decode_any W_13d44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d48 : bv 32 := 0x0000d517.
Lemma F_13d48 : fetch_word Ubsan.M.loaded_segments (0x13d48 : word) = Some W_13d48.
Proof. vm_refl. Qed.
Lemma D_13d48 : decode_any W_13d48 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d4c : bv 32 := 0xa5053503.
Lemma F_13d4c : fetch_word Ubsan.M.loaded_segments (0x13d4c : word) = Some W_13d4c.
Proof. vm_refl. Qed.
Lemma D_13d4c : decode_any W_13d4c = Some (Load SZ8 true 10 10 2640, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d50 : bv 32 := 0x00053503.
Lemma F_13d50 : fetch_word Ubsan.M.loaded_segments (0x13d50 : word) = Some W_13d50.
Proof. vm_refl. Qed.
Lemma D_13d50 : decode_any W_13d50 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d54 : bv 32 := 0x421050ef.
Lemma F_13d54 : fetch_word Ubsan.M.loaded_segments (0x13d54 : word) = Some W_13d54.
Proof. vm_refl. Qed.
Lemma D_13d54 : decode_any W_13d54 = Some (Jal 1 23584, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d58 : bv 32 := 0x04d00513.
Lemma F_13d58 : fetch_word Ubsan.M.loaded_segments (0x13d58 : word) = Some W_13d58.
Proof. vm_refl. Qed.
Lemma D_13d58 : decode_any W_13d58 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13d5c : bv 32 := 0x12d0b0ef.
Lemma F_13d5c : fetch_word Ubsan.M.loaded_segments (0x13d5c : word) = Some W_13d5c.
Proof. vm_refl. Qed.
Lemma D_13d5c : decode_any W_13d5c = Some (Jal 1 47404, 4%Z).
Proof. vm_refl. Qed.

Definition W_17738 : bv 32 := 0xfd010113.
Lemma F_17738 : fetch_word Ubsan.M.loaded_segments (0x17738 : word) = Some W_17738.
Proof. vm_refl. Qed.
Lemma D_17738 : decode_any W_17738 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_1773c : bv 32 := 0x02113423.
Lemma F_1773c : fetch_word Ubsan.M.loaded_segments (0x1773c : word) = Some W_1773c.
Proof. vm_refl. Qed.
Lemma D_1773c : decode_any W_1773c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17740 : bv 32 := 0x02813023.
Lemma F_17740 : fetch_word Ubsan.M.loaded_segments (0x17740 : word) = Some W_17740.
Proof. vm_refl. Qed.
Lemma D_17740 : decode_any W_17740 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17744 : bv 32 := 0x00913c23.
Lemma F_17744 : fetch_word Ubsan.M.loaded_segments (0x17744 : word) = Some W_17744.
Proof. vm_refl. Qed.
Lemma D_17744 : decode_any W_17744 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17748 : bv 32 := 0x01213823.
Lemma F_17748 : fetch_word Ubsan.M.loaded_segments (0x17748 : word) = Some W_17748.
Proof. vm_refl. Qed.
Lemma D_17748 : decode_any W_17748 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1774c : bv 32 := 0x01313423.
Lemma F_1774c : fetch_word Ubsan.M.loaded_segments (0x1774c : word) = Some W_1774c.
Proof. vm_refl. Qed.
Lemma D_1774c : decode_any W_1774c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17750 : bv 32 := 0x0003a517.
Lemma F_17750 : fetch_word Ubsan.M.loaded_segments (0x17750 : word) = Some W_17750.
Proof. vm_refl. Qed.
Lemma D_17750 : decode_any W_17750 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17754 : bv 32 := 0x46050913.
Lemma F_17754 : fetch_word Ubsan.M.loaded_segments (0x17754 : word) = Some W_17754.
Proof. vm_refl. Qed.
Lemma D_17754 : decode_any W_17754 = Some (OpImm ALU_ADD 18 10 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_17758 : bv 32 := 0x00490413.
Lemma F_17758 : fetch_word Ubsan.M.loaded_segments (0x17758 : word) = Some W_17758.
Proof. vm_refl. Qed.
Lemma D_17758 : decode_any W_17758 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1775c : bv 32 := 0x00040513.
Lemma F_1775c : fetch_word Ubsan.M.loaded_segments (0x1775c : word) = Some W_1775c.
Proof. vm_refl. Qed.
Lemma D_1775c : decode_any W_1775c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17760 : bv 32 := 0x3f9070ef.
Lemma F_17760 : fetch_word Ubsan.M.loaded_segments (0x17760 : word) = Some W_17760.
Proof. vm_refl. Qed.
Lemma D_17760 : decode_any W_17760 = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_17764 : bv 32 := 0x01093503.
Lemma F_17764 : fetch_word Ubsan.M.loaded_segments (0x17764 : word) = Some W_17764.
Proof. vm_refl. Qed.
Lemma D_17764 : decode_any W_17764 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17768 : bv 32 := 0x06050863.
Lemma F_17768 : fetch_word Ubsan.M.loaded_segments (0x17768 : word) = Some W_17768.
Proof. vm_refl. Qed.
Lemma D_17768 : decode_any W_17768 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1776c : bv 32 := 0x00892583.
Lemma F_1776c : fetch_word Ubsan.M.loaded_segments (0x1776c : word) = Some W_1776c.
Proof. vm_refl. Qed.
Lemma D_1776c : decode_any W_1776c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17770 : bv 32 := 0x0180006f.
Lemma F_17770 : fetch_word Ubsan.M.loaded_segments (0x17770 : word) = Some W_17770.
Proof. vm_refl. Qed.
Lemma D_17770 : decode_any W_17770 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17774 : bv 32 := 0x00053503.
Lemma F_17774 : fetch_word Ubsan.M.loaded_segments (0x17774 : word) = Some W_17774.
Proof. vm_refl. Qed.
Lemma D_17774 : decode_any W_17774 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17778 : bv 32 := 0x02000593.
Lemma F_17778 : fetch_word Ubsan.M.loaded_segments (0x17778 : word) = Some W_17778.
Proof. vm_refl. Qed.
Lemma D_17778 : decode_any W_17778 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1777c : bv 32 := 0x00b92423.
Lemma F_1777c : fetch_word Ubsan.M.loaded_segments (0x1777c : word) = Some W_1777c.
Proof. vm_refl. Qed.
Lemma D_1777c : decode_any W_1777c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17780 : bv 32 := 0x00a93823.
Lemma F_17780 : fetch_word Ubsan.M.loaded_segments (0x17780 : word) = Some W_17780.
Proof. vm_refl. Qed.
Lemma D_17780 : decode_any W_17780 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17784 : bv 32 := 0x04050a63.
Lemma F_17784 : fetch_word Ubsan.M.loaded_segments (0x17784 : word) = Some W_17784.
Proof. vm_refl. Qed.
Lemma D_17784 : decode_any W_17784 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_17788 : bv 32 := 0xfff5861b.
Lemma F_17788 : fetch_word Ubsan.M.loaded_segments (0x17788 : word) = Some W_17788.
Proof. vm_refl. Qed.
Lemma D_17788 : decode_any W_17788 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1778c : bv 32 := 0x00c92423.
Lemma F_1778c : fetch_word Ubsan.M.loaded_segments (0x1778c : word) = Some W_1778c.
Proof. vm_refl. Qed.
Lemma D_1778c : decode_any W_1778c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17790 : bv 32 := 0xfeb052e3.
Lemma F_17790 : fetch_word Ubsan.M.loaded_segments (0x17790 : word) = Some W_17790.
Proof. vm_refl. Qed.
Lemma D_17790 : decode_any W_17790 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_17794 : bv 32 := 0x01093503.
Lemma F_17794 : fetch_word Ubsan.M.loaded_segments (0x17794 : word) = Some W_17794.
Proof. vm_refl. Qed.
Lemma D_17794 : decode_any W_17794 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17798 : bv 32 := 0x00361613.
Lemma F_17798 : fetch_word Ubsan.M.loaded_segments (0x17798 : word) = Some W_17798.
Proof. vm_refl. Qed.
Lemma D_17798 : decode_any W_17798 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1779c : bv 32 := 0x00c50533.
Lemma F_1779c : fetch_word Ubsan.M.loaded_segments (0x1779c : word) = Some W_1779c.
Proof. vm_refl. Qed.
Lemma D_1779c : decode_any W_1779c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_177a0 : bv 32 := 0x00853983.
Lemma F_177a0 : fetch_word Ubsan.M.loaded_segments (0x177a0 : word) = Some W_177a0.
Proof. vm_refl. Qed.
Lemma D_177a0 : decode_any W_177a0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_177a4 : bv 32 := 0x10853483.
Lemma F_177a4 : fetch_word Ubsan.M.loaded_segments (0x177a4 : word) = Some W_177a4.
Proof. vm_refl. Qed.
Lemma D_177a4 : decode_any W_177a4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_177a8 : bv 32 := 0x00040513.
Lemma F_177a8 : fetch_word Ubsan.M.loaded_segments (0x177a8 : word) = Some W_177a8.
Proof. vm_refl. Qed.
Lemma D_177a8 : decode_any W_177a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_177ac : bv 32 := 0x635070ef.
Lemma F_177ac : fetch_word Ubsan.M.loaded_segments (0x177ac : word) = Some W_177ac.
Proof. vm_refl. Qed.
Lemma D_177ac : decode_any W_177ac = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_177b0 : bv 32 := 0x00048513.
Lemma F_177b0 : fetch_word Ubsan.M.loaded_segments (0x177b0 : word) = Some W_177b0.
Proof. vm_refl. Qed.
Lemma D_177b0 : decode_any W_177b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_177b4 : bv 32 := 0x000980e7.
Lemma F_177b4 : fetch_word Ubsan.M.loaded_segments (0x177b4 : word) = Some W_177b4.
Proof. vm_refl. Qed.
Lemma D_177b4 : decode_any W_177b4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_177b8 : bv 32 := 0x00040513.
Lemma F_177b8 : fetch_word Ubsan.M.loaded_segments (0x177b8 : word) = Some W_177b8.
Proof. vm_refl. Qed.
Lemma D_177b8 : decode_any W_177b8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_177bc : bv 32 := 0x39d070ef.
Lemma F_177bc : fetch_word Ubsan.M.loaded_segments (0x177bc : word) = Some W_177bc.
Proof. vm_refl. Qed.
Lemma D_177bc : decode_any W_177bc = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_177c0 : bv 32 := 0x00892503.
Lemma F_177c0 : fetch_word Ubsan.M.loaded_segments (0x177c0 : word) = Some W_177c0.
Proof. vm_refl. Qed.
Lemma D_177c0 : decode_any W_177c0 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_177c4 : bv 32 := 0xfff5061b.
Lemma F_177c4 : fetch_word Ubsan.M.loaded_segments (0x177c4 : word) = Some W_177c4.
Proof. vm_refl. Qed.
Lemma D_177c4 : decode_any W_177c4 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_177c8 : bv 32 := 0x00c92423.
Lemma F_177c8 : fetch_word Ubsan.M.loaded_segments (0x177c8 : word) = Some W_177c8.
Proof. vm_refl. Qed.
Lemma D_177c8 : decode_any W_177c8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_177cc : bv 32 := 0xfca044e3.
Lemma F_177cc : fetch_word Ubsan.M.loaded_segments (0x177cc : word) = Some W_177cc.
Proof. vm_refl. Qed.
Lemma D_177cc : decode_any W_177cc = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_177d0 : bv 32 := 0x01093503.
Lemma F_177d0 : fetch_word Ubsan.M.loaded_segments (0x177d0 : word) = Some W_177d0.
Proof. vm_refl. Qed.
Lemma D_177d0 : decode_any W_177d0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_177d4 : bv 32 := 0xfa1ff06f.
Lemma F_177d4 : fetch_word Ubsan.M.loaded_segments (0x177d4 : word) = Some W_177d4.
Proof. vm_refl. Qed.
Lemma D_177d4 : decode_any W_177d4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_177d8 : bv 32 := 0x00100513.
Lemma F_177d8 : fetch_word Ubsan.M.loaded_segments (0x177d8 : word) = Some W_177d8.
Proof. vm_refl. Qed.
Lemma D_177d8 : decode_any W_177d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_177dc : bv 32 := 0x00a90023.
Lemma F_177dc : fetch_word Ubsan.M.loaded_segments (0x177dc : word) = Some W_177dc.
Proof. vm_refl. Qed.
Lemma D_177dc : decode_any W_177dc = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_177e0 : bv 32 := 0x00040513.
Lemma F_177e0 : fetch_word Ubsan.M.loaded_segments (0x177e0 : word) = Some W_177e0.
Proof. vm_refl. Qed.
Lemma D_177e0 : decode_any W_177e0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_177e4 : bv 32 := 0x02813083.
Lemma F_177e4 : fetch_word Ubsan.M.loaded_segments (0x177e4 : word) = Some W_177e4.
Proof. vm_refl. Qed.
Lemma D_177e4 : decode_any W_177e4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_177e8 : bv 32 := 0x02013403.
Lemma F_177e8 : fetch_word Ubsan.M.loaded_segments (0x177e8 : word) = Some W_177e8.
Proof. vm_refl. Qed.
Lemma D_177e8 : decode_any W_177e8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_177ec : bv 32 := 0x01813483.
Lemma F_177ec : fetch_word Ubsan.M.loaded_segments (0x177ec : word) = Some W_177ec.
Proof. vm_refl. Qed.
Lemma D_177ec : decode_any W_177ec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_177f0 : bv 32 := 0x01013903.
Lemma F_177f0 : fetch_word Ubsan.M.loaded_segments (0x177f0 : word) = Some W_177f0.
Proof. vm_refl. Qed.
Lemma D_177f0 : decode_any W_177f0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_177f4 : bv 32 := 0x00813983.
Lemma F_177f4 : fetch_word Ubsan.M.loaded_segments (0x177f4 : word) = Some W_177f4.
Proof. vm_refl. Qed.
Lemma D_177f4 : decode_any W_177f4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_177f8 : bv 32 := 0x03010113.
Lemma F_177f8 : fetch_word Ubsan.M.loaded_segments (0x177f8 : word) = Some W_177f8.
Proof. vm_refl. Qed.
Lemma D_177f8 : decode_any W_177f8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_177fc : bv 32 := 0x5e50706f.
Lemma F_177fc : fetch_word Ubsan.M.loaded_segments (0x177fc : word) = Some W_177fc.
Proof. vm_refl. Qed.
Lemma D_177fc : decode_any W_177fc = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_17800 : bv 32 := 0x00008067.
Lemma F_17800 : fetch_word Ubsan.M.loaded_segments (0x17800 : word) = Some W_17800.
Proof. vm_refl. Qed.
Lemma D_17800 : decode_any W_17800 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17804 : bv 32 := 0xfd010113.
Lemma F_17804 : fetch_word Ubsan.M.loaded_segments (0x17804 : word) = Some W_17804.
Proof. vm_refl. Qed.
Lemma D_17804 : decode_any W_17804 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_17808 : bv 32 := 0x02113423.
Lemma F_17808 : fetch_word Ubsan.M.loaded_segments (0x17808 : word) = Some W_17808.
Proof. vm_refl. Qed.
Lemma D_17808 : decode_any W_17808 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1780c : bv 32 := 0x02813023.
Lemma F_1780c : fetch_word Ubsan.M.loaded_segments (0x1780c : word) = Some W_1780c.
Proof. vm_refl. Qed.
Lemma D_1780c : decode_any W_1780c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17810 : bv 32 := 0x00913c23.
Lemma F_17810 : fetch_word Ubsan.M.loaded_segments (0x17810 : word) = Some W_17810.
Proof. vm_refl. Qed.
Lemma D_17810 : decode_any W_17810 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17814 : bv 32 := 0x01213823.
Lemma F_17814 : fetch_word Ubsan.M.loaded_segments (0x17814 : word) = Some W_17814.
Proof. vm_refl. Qed.
Lemma D_17814 : decode_any W_17814 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17818 : bv 32 := 0x01313423.
Lemma F_17818 : fetch_word Ubsan.M.loaded_segments (0x17818 : word) = Some W_17818.
Proof. vm_refl. Qed.
Lemma D_17818 : decode_any W_17818 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1781c : bv 32 := 0x00050493.
Lemma F_1781c : fetch_word Ubsan.M.loaded_segments (0x1781c : word) = Some W_1781c.
Proof. vm_refl. Qed.
Lemma D_1781c : decode_any W_1781c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17820 : bv 32 := 0x0003a517.
Lemma F_17820 : fetch_word Ubsan.M.loaded_segments (0x17820 : word) = Some W_17820.
Proof. vm_refl. Qed.
Lemma D_17820 : decode_any W_17820 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17824 : bv 32 := 0x39050993.
Lemma F_17824 : fetch_word Ubsan.M.loaded_segments (0x17824 : word) = Some W_17824.
Proof. vm_refl. Qed.
Lemma D_17824 : decode_any W_17824 = Some (OpImm ALU_ADD 19 10 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_17828 : bv 32 := 0x00498413.
Lemma F_17828 : fetch_word Ubsan.M.loaded_segments (0x17828 : word) = Some W_17828.
Proof. vm_refl. Qed.
Lemma D_17828 : decode_any W_17828 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1782c : bv 32 := 0x00040513.
Lemma F_1782c : fetch_word Ubsan.M.loaded_segments (0x1782c : word) = Some W_1782c.
Proof. vm_refl. Qed.
Lemma D_1782c : decode_any W_1782c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17830 : bv 32 := 0x329070ef.
Lemma F_17830 : fetch_word Ubsan.M.loaded_segments (0x17830 : word) = Some W_17830.
Proof. vm_refl. Qed.
Lemma D_17830 : decode_any W_17830 = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_17834 : bv 32 := 0x0009c503.
Lemma F_17834 : fetch_word Ubsan.M.loaded_segments (0x17834 : word) = Some W_17834.
Proof. vm_refl. Qed.
Lemma D_17834 : decode_any W_17834 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17838 : bv 32 := 0xfff00913.
Lemma F_17838 : fetch_word Ubsan.M.loaded_segments (0x17838 : word) = Some W_17838.
Proof. vm_refl. Qed.
Lemma D_17838 : decode_any W_17838 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1783c : bv 32 := 0x06051263.
Lemma F_1783c : fetch_word Ubsan.M.loaded_segments (0x1783c : word) = Some W_1783c.
Proof. vm_refl. Qed.
Lemma D_1783c : decode_any W_1783c = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_17840 : bv 32 := 0x0109b503.
Lemma F_17840 : fetch_word Ubsan.M.loaded_segments (0x17840 : word) = Some W_17840.
Proof. vm_refl. Qed.
Lemma D_17840 : decode_any W_17840 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17844 : bv 32 := 0x00051663.
Lemma F_17844 : fetch_word Ubsan.M.loaded_segments (0x17844 : word) = Some W_17844.
Proof. vm_refl. Qed.
Lemma D_17844 : decode_any W_17844 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17848 : bv 32 := 0x01898513.
Lemma F_17848 : fetch_word Ubsan.M.loaded_segments (0x17848 : word) = Some W_17848.
Proof. vm_refl. Qed.
Lemma D_17848 : decode_any W_17848 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1784c : bv 32 := 0x00a9b823.
Lemma F_1784c : fetch_word Ubsan.M.loaded_segments (0x1784c : word) = Some W_1784c.
Proof. vm_refl. Qed.
Lemma D_1784c : decode_any W_1784c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17850 : bv 32 := 0x0089a583.
Lemma F_17850 : fetch_word Ubsan.M.loaded_segments (0x17850 : word) = Some W_17850.
Proof. vm_refl. Qed.
Lemma D_17850 : decode_any W_17850 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17854 : bv 32 := 0x02000613.
Lemma F_17854 : fetch_word Ubsan.M.loaded_segments (0x17854 : word) = Some W_17854.
Proof. vm_refl. Qed.
Lemma D_17854 : decode_any W_17854 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17858 : bv 32 := 0x02c59263.
Lemma F_17858 : fetch_word Ubsan.M.loaded_segments (0x17858 : word) = Some W_17858.
Proof. vm_refl. Qed.
Lemma D_17858 : decode_any W_17858 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1785c : bv 32 := 0x20800513.
Lemma F_1785c : fetch_word Ubsan.M.loaded_segments (0x1785c : word) = Some W_1785c.
Proof. vm_refl. Qed.
Lemma D_1785c : decode_any W_1785c = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_17860 : bv 32 := 0x00100593.
Lemma F_17860 : fetch_word Ubsan.M.loaded_segments (0x17860 : word) = Some W_17860.
Proof. vm_refl. Qed.
Lemma D_17860 : decode_any W_17860 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17864 : bv 32 := 0x3f4000ef.
Lemma F_17864 : fetch_word Ubsan.M.loaded_segments (0x17864 : word) = Some W_17864.
Proof. vm_refl. Qed.
Lemma D_17864 : decode_any W_17864 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_17868 : bv 32 := 0x02050c63.
Lemma F_17868 : fetch_word Ubsan.M.loaded_segments (0x17868 : word) = Some W_17868.
Proof. vm_refl. Qed.
Lemma D_17868 : decode_any W_17868 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1786c : bv 32 := 0x00000593.
Lemma F_1786c : fetch_word Ubsan.M.loaded_segments (0x1786c : word) = Some W_1786c.
Proof. vm_refl. Qed.
Lemma D_1786c : decode_any W_1786c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17870 : bv 32 := 0x0109b603.
Lemma F_17870 : fetch_word Ubsan.M.loaded_segments (0x17870 : word) = Some W_17870.
Proof. vm_refl. Qed.
Lemma D_17870 : decode_any W_17870 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17874 : bv 32 := 0x00c53023.
Lemma F_17874 : fetch_word Ubsan.M.loaded_segments (0x17874 : word) = Some W_17874.
Proof. vm_refl. Qed.
Lemma D_17874 : decode_any W_17874 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17878 : bv 32 := 0x00a9b823.
Lemma F_17878 : fetch_word Ubsan.M.loaded_segments (0x17878 : word) = Some W_17878.
Proof. vm_refl. Qed.
Lemma D_17878 : decode_any W_17878 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1787c : bv 32 := 0x00000913.
Lemma F_1787c : fetch_word Ubsan.M.loaded_segments (0x1787c : word) = Some W_1787c.
Proof. vm_refl. Qed.
Lemma D_1787c : decode_any W_1787c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17880 : bv 32 := 0x00359613.
Lemma F_17880 : fetch_word Ubsan.M.loaded_segments (0x17880 : word) = Some W_17880.
Proof. vm_refl. Qed.
Lemma D_17880 : decode_any W_17880 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17884 : bv 32 := 0x00c50533.
Lemma F_17884 : fetch_word Ubsan.M.loaded_segments (0x17884 : word) = Some W_17884.
Proof. vm_refl. Qed.
Lemma D_17884 : decode_any W_17884 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17888 : bv 32 := 0x00000617.
Lemma F_17888 : fetch_word Ubsan.M.loaded_segments (0x17888 : word) = Some W_17888.
Proof. vm_refl. Qed.
Lemma D_17888 : decode_any W_17888 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1788c : bv 32 := 0x00158593.
Lemma F_1788c : fetch_word Ubsan.M.loaded_segments (0x1788c : word) = Some W_1788c.
Proof. vm_refl. Qed.
Lemma D_1788c : decode_any W_1788c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17890 : bv 32 := 0x04060613.
Lemma F_17890 : fetch_word Ubsan.M.loaded_segments (0x17890 : word) = Some W_17890.
Proof. vm_refl. Qed.
Lemma D_17890 : decode_any W_17890 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_17894 : bv 32 := 0x00c53423.
Lemma F_17894 : fetch_word Ubsan.M.loaded_segments (0x17894 : word) = Some W_17894.
Proof. vm_refl. Qed.
Lemma D_17894 : decode_any W_17894 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17898 : bv 32 := 0x10953423.
Lemma F_17898 : fetch_word Ubsan.M.loaded_segments (0x17898 : word) = Some W_17898.
Proof. vm_refl. Qed.
Lemma D_17898 : decode_any W_17898 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1789c : bv 32 := 0x00b9a423.
Lemma F_1789c : fetch_word Ubsan.M.loaded_segments (0x1789c : word) = Some W_1789c.
Proof. vm_refl. Qed.
Lemma D_1789c : decode_any W_1789c = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_178a0 : bv 32 := 0x00040513.
Lemma F_178a0 : fetch_word Ubsan.M.loaded_segments (0x178a0 : word) = Some W_178a0.
Proof. vm_refl. Qed.
Lemma D_178a0 : decode_any W_178a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178a4 : bv 32 := 0x53d070ef.
Lemma F_178a4 : fetch_word Ubsan.M.loaded_segments (0x178a4 : word) = Some W_178a4.
Proof. vm_refl. Qed.
Lemma D_178a4 : decode_any W_178a4 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_178a8 : bv 32 := 0x00090513.
Lemma F_178a8 : fetch_word Ubsan.M.loaded_segments (0x178a8 : word) = Some W_178a8.
Proof. vm_refl. Qed.
Lemma D_178a8 : decode_any W_178a8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178ac : bv 32 := 0x02813083.
Lemma F_178ac : fetch_word Ubsan.M.loaded_segments (0x178ac : word) = Some W_178ac.
Proof. vm_refl. Qed.
Lemma D_178ac : decode_any W_178ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_178b0 : bv 32 := 0x02013403.
Lemma F_178b0 : fetch_word Ubsan.M.loaded_segments (0x178b0 : word) = Some W_178b0.
Proof. vm_refl. Qed.
Lemma D_178b0 : decode_any W_178b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_178b4 : bv 32 := 0x01813483.
Lemma F_178b4 : fetch_word Ubsan.M.loaded_segments (0x178b4 : word) = Some W_178b4.
Proof. vm_refl. Qed.
Lemma D_178b4 : decode_any W_178b4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_178b8 : bv 32 := 0x01013903.
Lemma F_178b8 : fetch_word Ubsan.M.loaded_segments (0x178b8 : word) = Some W_178b8.
Proof. vm_refl. Qed.
Lemma D_178b8 : decode_any W_178b8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_178bc : bv 32 := 0x00813983.
Lemma F_178bc : fetch_word Ubsan.M.loaded_segments (0x178bc : word) = Some W_178bc.
Proof. vm_refl. Qed.
Lemma D_178bc : decode_any W_178bc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_178c0 : bv 32 := 0x03010113.
Lemma F_178c0 : fetch_word Ubsan.M.loaded_segments (0x178c0 : word) = Some W_178c0.
Proof. vm_refl. Qed.
Lemma D_178c0 : decode_any W_178c0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_178c4 : bv 32 := 0x00008067.
Lemma F_178c4 : fetch_word Ubsan.M.loaded_segments (0x178c4 : word) = Some W_178c4.
Proof. vm_refl. Qed.
Lemma D_178c4 : decode_any W_178c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178c8 : bv 32 := 0x00050067.
Lemma F_178c8 : fetch_word Ubsan.M.loaded_segments (0x178c8 : word) = Some W_178c8.
Proof. vm_refl. Qed.
Lemma D_178c8 : decode_any W_178c8 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178cc : bv 32 := 0x00008067.
Lemma F_178cc : fetch_word Ubsan.M.loaded_segments (0x178cc : word) = Some W_178cc.
Proof. vm_refl. Qed.
Lemma D_178cc : decode_any W_178cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178d0 : bv 32 := 0xfe010113.
Lemma F_178d0 : fetch_word Ubsan.M.loaded_segments (0x178d0 : word) = Some W_178d0.
Proof. vm_refl. Qed.
Lemma D_178d0 : decode_any W_178d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_178d4 : bv 32 := 0x00113c23.
Lemma F_178d4 : fetch_word Ubsan.M.loaded_segments (0x178d4 : word) = Some W_178d4.
Proof. vm_refl. Qed.
Lemma D_178d4 : decode_any W_178d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_178d8 : bv 32 := 0x00813823.
Lemma F_178d8 : fetch_word Ubsan.M.loaded_segments (0x178d8 : word) = Some W_178d8.
Proof. vm_refl. Qed.
Lemma D_178d8 : decode_any W_178d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_178dc : bv 32 := 0x00913423.
Lemma F_178dc : fetch_word Ubsan.M.loaded_segments (0x178dc : word) = Some W_178dc.
Proof. vm_refl. Qed.
Lemma D_178dc : decode_any W_178dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_178e0 : bv 32 := 0x00009517.
Lemma F_178e0 : fetch_word Ubsan.M.loaded_segments (0x178e0 : word) = Some W_178e0.
Proof. vm_refl. Qed.
Lemma D_178e0 : decode_any W_178e0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_178e4 : bv 32 := 0x00009597.
Lemma F_178e4 : fetch_word Ubsan.M.loaded_segments (0x178e4 : word) = Some W_178e4.
Proof. vm_refl. Qed.
Lemma D_178e4 : decode_any W_178e4 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_178e8 : bv 32 := 0xef853503.
Lemma F_178e8 : fetch_word Ubsan.M.loaded_segments (0x178e8 : word) = Some W_178e8.
Proof. vm_refl. Qed.
Lemma D_178e8 : decode_any W_178e8 = Some (Load SZ8 true 10 10 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_178ec : bv 32 := 0xefc5b403.
Lemma F_178ec : fetch_word Ubsan.M.loaded_segments (0x178ec : word) = Some W_178ec.
Proof. vm_refl. Qed.
Lemma D_178ec : decode_any W_178ec = Some (Load SZ8 true 8 11 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_178f0 : bv 32 := 0x00a47c63.
Lemma F_178f0 : fetch_word Ubsan.M.loaded_segments (0x178f0 : word) = Some W_178f0.
Proof. vm_refl. Qed.
Lemma D_178f0 : decode_any W_178f0 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_178f4 : bv 32 := 0xff853583.
Lemma F_178f4 : fetch_word Ubsan.M.loaded_segments (0x178f4 : word) = Some W_178f4.
Proof. vm_refl. Qed.
Lemma D_178f4 : decode_any W_178f4 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_178f8 : bv 32 := 0xff850493.
Lemma F_178f8 : fetch_word Ubsan.M.loaded_segments (0x178f8 : word) = Some W_178f8.
Proof. vm_refl. Qed.
Lemma D_178f8 : decode_any W_178f8 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_178fc : bv 32 := 0x000580e7.
Lemma F_178fc : fetch_word Ubsan.M.loaded_segments (0x178fc : word) = Some W_178fc.
Proof. vm_refl. Qed.
Lemma D_178fc : decode_any W_178fc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17900 : bv 32 := 0x00048513.
Lemma F_17900 : fetch_word Ubsan.M.loaded_segments (0x17900 : word) = Some W_17900.
Proof. vm_refl. Qed.
Lemma D_17900 : decode_any W_17900 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17904 : bv 32 := 0xfe9468e3.
Lemma F_17904 : fetch_word Ubsan.M.loaded_segments (0x17904 : word) = Some W_17904.
Proof. vm_refl. Qed.
Lemma D_17904 : decode_any W_17904 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_17908 : bv 32 := 0x01813083.
Lemma F_17908 : fetch_word Ubsan.M.loaded_segments (0x17908 : word) = Some W_17908.
Proof. vm_refl. Qed.
Lemma D_17908 : decode_any W_17908 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1790c : bv 32 := 0x01013403.
Lemma F_1790c : fetch_word Ubsan.M.loaded_segments (0x1790c : word) = Some W_1790c.
Proof. vm_refl. Qed.
Lemma D_1790c : decode_any W_1790c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17910 : bv 32 := 0x00813483.
Lemma F_17910 : fetch_word Ubsan.M.loaded_segments (0x17910 : word) = Some W_17910.
Proof. vm_refl. Qed.
Lemma D_17910 : decode_any W_17910 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17914 : bv 32 := 0x02010113.
Lemma F_17914 : fetch_word Ubsan.M.loaded_segments (0x17914 : word) = Some W_17914.
Proof. vm_refl. Qed.
Lemma D_17914 : decode_any W_17914 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17918 : bv 32 := 0xfb5ff06f.
Lemma F_17918 : fetch_word Ubsan.M.loaded_segments (0x17918 : word) = Some W_17918.
Proof. vm_refl. Qed.
Lemma D_17918 : decode_any W_17918 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1791c : bv 32 := 0xff010113.
Lemma F_1791c : fetch_word Ubsan.M.loaded_segments (0x1791c : word) = Some W_1791c.
Proof. vm_refl. Qed.
Lemma D_1791c : decode_any W_1791c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17920 : bv 32 := 0x00113423.
Lemma F_17920 : fetch_word Ubsan.M.loaded_segments (0x17920 : word) = Some W_17920.
Proof. vm_refl. Qed.
Lemma D_17920 : decode_any W_17920 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17924 : bv 32 := 0x00813023.
Lemma F_17924 : fetch_word Ubsan.M.loaded_segments (0x17924 : word) = Some W_17924.
Proof. vm_refl. Qed.
Lemma D_17924 : decode_any W_17924 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17928 : bv 32 := 0x00000593.
Lemma F_17928 : fetch_word Ubsan.M.loaded_segments (0x17928 : word) = Some W_17928.
Proof. vm_refl. Qed.
Lemma D_17928 : decode_any W_17928 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1792c : bv 32 := 0x00020613.
Lemma F_1792c : fetch_word Ubsan.M.loaded_segments (0x1792c : word) = Some W_1792c.
Proof. vm_refl. Qed.
Lemma D_1792c : decode_any W_1792c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17930 : bv 32 := 0xf5862603.
Lemma F_17930 : fetch_word Ubsan.M.loaded_segments (0x17930 : word) = Some W_17930.
Proof. vm_refl. Qed.
Lemma D_17930 : decode_any W_17930 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_17934 : bv 32 := 0x0003a697.
Lemma F_17934 : fetch_word Ubsan.M.loaded_segments (0x17934 : word) = Some W_17934.
Proof. vm_refl. Qed.
Lemma D_17934 : decode_any W_17934 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17938 : bv 32 := 0x49c68693.
Lemma F_17938 : fetch_word Ubsan.M.loaded_segments (0x17938 : word) = Some W_17938.
Proof. vm_refl. Qed.
Lemma D_17938 : decode_any W_17938 = Some (OpImm ALU_ADD 13 13 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1793c : bv 32 := 0x1606a72f.
Lemma F_1793c : fetch_word Ubsan.M.loaded_segments (0x1793c : word) = Some W_1793c.
Proof. vm_refl. Qed.
Lemma D_1793c : decode_any W_1793c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17940 : bv 32 := 0x00b71663.
Lemma F_17940 : fetch_word Ubsan.M.loaded_segments (0x17940 : word) = Some W_17940.
Proof. vm_refl. Qed.
Lemma D_17940 : decode_any W_17940 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17944 : bv 32 := 0x1ec6a7af.
Lemma F_17944 : fetch_word Ubsan.M.loaded_segments (0x17944 : word) = Some W_17944.
Proof. vm_refl. Qed.
Lemma D_17944 : decode_any W_17944 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17948 : bv 32 := 0xfe079ae3.
Lemma F_17948 : fetch_word Ubsan.M.loaded_segments (0x17948 : word) = Some W_17948.
Proof. vm_refl. Qed.
Lemma D_17948 : decode_any W_17948 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1794c : bv 32 := 0x0007059b.
Lemma F_1794c : fetch_word Ubsan.M.loaded_segments (0x1794c : word) = Some W_1794c.
Proof. vm_refl. Qed.
Lemma D_1794c : decode_any W_1794c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17950 : bv 32 := 0x02c58263.
Lemma F_17950 : fetch_word Ubsan.M.loaded_segments (0x17950 : word) = Some W_17950.
Proof. vm_refl. Qed.
Lemma D_17950 : decode_any W_17950 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_17954 : bv 32 := 0x02058263.
Lemma F_17954 : fetch_word Ubsan.M.loaded_segments (0x17954 : word) = Some W_17954.
Proof. vm_refl. Qed.
Lemma D_17954 : decode_any W_17954 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_17958 : bv 32 := 0x04900893.
Lemma F_17958 : fetch_word Ubsan.M.loaded_segments (0x17958 : word) = Some W_17958.
Proof. vm_refl. Qed.
Lemma D_17958 : decode_any W_17958 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_1795c : bv 32 := 0x00000593.
Lemma F_1795c : fetch_word Ubsan.M.loaded_segments (0x1795c : word) = Some W_1795c.
Proof. vm_refl. Qed.
Lemma D_1795c : decode_any W_1795c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17960 : bv 32 := 0x00000613.
Lemma F_17960 : fetch_word Ubsan.M.loaded_segments (0x17960 : word) = Some W_17960.
Proof. vm_refl. Qed.
Lemma D_17960 : decode_any W_17960 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17964 : bv 32 := 0x00000693.
Lemma F_17964 : fetch_word Ubsan.M.loaded_segments (0x17964 : word) = Some W_17964.
Proof. vm_refl. Qed.
Lemma D_17964 : decode_any W_17964 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17968 : bv 32 := 0x00000513.
Lemma F_17968 : fetch_word Ubsan.M.loaded_segments (0x17968 : word) = Some W_17968.
Proof. vm_refl. Qed.
Lemma D_17968 : decode_any W_17968 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1796c : bv 32 := 0x00000073.
Lemma F_1796c : fetch_word Ubsan.M.loaded_segments (0x1796c : word) = Some W_1796c.
Proof. vm_refl. Qed.
Lemma E_1796c : is_ecall W_1796c = true.
Proof. vm_refl. Qed.

Definition W_17970 : bv 32 := 0xff9ff06f.
Lemma F_17970 : fetch_word Ubsan.M.loaded_segments (0x17970 : word) = Some W_17970.
Proof. vm_refl. Qed.
Lemma D_17970 : decode_any W_17970 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_17974 : bv 32 := 0x00000023.
Lemma F_17974 : fetch_word Ubsan.M.loaded_segments (0x17974 : word) = Some W_17974.
Proof. vm_refl. Qed.
Lemma D_17974 : decode_any W_17974 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17978 : bv 32 := 0x00050413.
Lemma F_17978 : fetch_word Ubsan.M.loaded_segments (0x17978 : word) = Some W_17978.
Proof. vm_refl. Qed.
Lemma D_17978 : decode_any W_17978 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1797c : bv 32 := 0xdbdff0ef.
Lemma F_1797c : fetch_word Ubsan.M.loaded_segments (0x1797c : word) = Some W_1797c.
Proof. vm_refl. Qed.
Lemma D_1797c : decode_any W_1797c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_17980 : bv 32 := 0xf51ff0ef.
Lemma F_17980 : fetch_word Ubsan.M.loaded_segments (0x17980 : word) = Some W_17980.
Proof. vm_refl. Qed.
Lemma D_17980 : decode_any W_17980 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_17984 : bv 32 := 0x160020ef.
Lemma F_17984 : fetch_word Ubsan.M.loaded_segments (0x17984 : word) = Some W_17984.
Proof. vm_refl. Qed.
Lemma D_17984 : decode_any W_17984 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_17988 : bv 32 := 0x00040513.
Lemma F_17988 : fetch_word Ubsan.M.loaded_segments (0x17988 : word) = Some W_17988.
Proof. vm_refl. Qed.
Lemma D_17988 : decode_any W_17988 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1798c : bv 32 := 0xd91ff0ef.
Lemma F_1798c : fetch_word Ubsan.M.loaded_segments (0x1798c : word) = Some W_1798c.
Proof. vm_refl. Qed.
Lemma D_1798c : decode_any W_1798c = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f358 : bv 32 := 0x00033597.
Lemma F_1f358 : fetch_word Ubsan.M.loaded_segments (0x1f358 : word) = Some W_1f358.
Proof. vm_refl. Qed.
Lemma D_1f358 : decode_any W_1f358 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f35c : bv 32 := 0xaa358683.
Lemma F_1f35c : fetch_word Ubsan.M.loaded_segments (0x1f35c : word) = Some W_1f35c.
Proof. vm_refl. Qed.
Lemma D_1f35c : decode_any W_1f35c = Some (Load SZ1 true 13 11 2723, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f360 : bv 32 := 0x1e068863.
Lemma F_1f360 : fetch_word Ubsan.M.loaded_segments (0x1f360 : word) = Some W_1f360.
Proof. vm_refl. Qed.
Lemma D_1f360 : decode_any W_1f360 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f550 : bv 32 := 0x00008067.
Lemma F_1f550 : fetch_word Ubsan.M.loaded_segments (0x1f550 : word) = Some W_1f550.
Proof. vm_refl. Qed.
Lemma D_1f550 : decode_any W_1f550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f5e0 : bv 32 := 0x00052583.
Lemma F_1f5e0 : fetch_word Ubsan.M.loaded_segments (0x1f5e0 : word) = Some W_1f5e0.
Proof. vm_refl. Qed.
Lemma D_1f5e0 : decode_any W_1f5e0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f5e4 : bv 32 := 0x0005c463.
Lemma F_1f5e4 : fetch_word Ubsan.M.loaded_segments (0x1f5e4 : word) = Some W_1f5e4.
Proof. vm_refl. Qed.
Lemma D_1f5e4 : decode_any W_1f5e4 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f5e8 : bv 32 := 0x00008067.
Lemma F_1f5e8 : fetch_word Ubsan.M.loaded_segments (0x1f5e8 : word) = Some W_1f5e8.
Proof. vm_refl. Qed.
Lemma D_1f5e8 : decode_any W_1f5e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
