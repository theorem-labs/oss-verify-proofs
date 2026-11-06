(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_16810 : bv 32 := 0xfd010113.
Lemma F_16810 : fetch_word Plain.M.loaded_segments (0x16868 : word) = Some W_16810.
Proof. vm_refl. Qed.
Lemma D_16810 : decode_any W_16810 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16814 : bv 32 := 0x02113423.
Lemma F_16814 : fetch_word Plain.M.loaded_segments (0x1686c : word) = Some W_16814.
Proof. vm_refl. Qed.
Lemma D_16814 : decode_any W_16814 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16818 : bv 32 := 0x02813023.
Lemma F_16818 : fetch_word Plain.M.loaded_segments (0x16870 : word) = Some W_16818.
Proof. vm_refl. Qed.
Lemma D_16818 : decode_any W_16818 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1681c : bv 32 := 0x00913c23.
Lemma F_1681c : fetch_word Plain.M.loaded_segments (0x16874 : word) = Some W_1681c.
Proof. vm_refl. Qed.
Lemma D_1681c : decode_any W_1681c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16820 : bv 32 := 0x01213823.
Lemma F_16820 : fetch_word Plain.M.loaded_segments (0x16878 : word) = Some W_16820.
Proof. vm_refl. Qed.
Lemma D_16820 : decode_any W_16820 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16824 : bv 32 := 0x01313423.
Lemma F_16824 : fetch_word Plain.M.loaded_segments (0x1687c : word) = Some W_16824.
Proof. vm_refl. Qed.
Lemma D_16824 : decode_any W_16824 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16828 : bv 32 := 0x01413023.
Lemma F_16828 : fetch_word Plain.M.loaded_segments (0x16880 : word) = Some W_16828.
Proof. vm_refl. Qed.
Lemma D_16828 : decode_any W_16828 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1682c : bv 32 := 0x02000693.
Lemma F_1682c : fetch_word Plain.M.loaded_segments (0x16884 : word) = Some W_1682c.
Proof. vm_refl. Qed.
Lemma D_1682c : decode_any W_1682c = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16830 : bv 32 := 0x14c6ea63.
Lemma F_16830 : fetch_word Plain.M.loaded_segments (0x16888 : word) = Some W_16830.
Proof. vm_refl. Qed.
Lemma D_16830 : decode_any W_16830 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16834 : bv 32 := 0x101016b7.
Lemma F_16834 : fetch_word Plain.M.loaded_segments (0x1688c : word) = Some W_16834.
Proof. vm_refl. Qed.
Lemma D_16834 : decode_any W_16834 = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16838 : bv 32 := 0x00469693.
Lemma F_16838 : fetch_word Plain.M.loaded_segments (0x16890 : word) = Some W_16838.
Proof. vm_refl. Qed.
Lemma D_16838 : decode_any W_16838 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1683c : bv 32 := 0x11668693.
Lemma F_1683c : fetch_word Plain.M.loaded_segments (0x16894 : word) = Some W_1683c.
Proof. vm_refl. Qed.
Lemma D_1683c : decode_any W_1683c = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16840 : bv 32 := 0x00c6d6b3.
Lemma F_16840 : fetch_word Plain.M.loaded_segments (0x16898 : word) = Some W_16840.
Proof. vm_refl. Qed.
Lemma D_16840 : decode_any W_16840 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16844 : bv 32 := 0x0016f693.
Lemma F_16844 : fetch_word Plain.M.loaded_segments (0x1689c : word) = Some W_16844.
Proof. vm_refl. Qed.
Lemma D_16844 : decode_any W_16844 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16848 : bv 32 := 0x12068e63.
Lemma F_16848 : fetch_word Plain.M.loaded_segments (0x168a0 : word) = Some W_16848.
Proof. vm_refl. Qed.
Lemma D_16848 : decode_any W_16848 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1684c : bv 32 := 0x06a05a63.
Lemma F_1684c : fetch_word Plain.M.loaded_segments (0x168a4 : word) = Some W_1684c.
Proof. vm_refl. Qed.
Lemma D_1684c : decode_any W_1684c = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16850 : bv 32 := 0x08b05c63.
Lemma F_16850 : fetch_word Plain.M.loaded_segments (0x168a8 : word) = Some W_16850.
Proof. vm_refl. Qed.
Lemma D_16850 : decode_any W_16850 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16854 : bv 32 := 0x02a606b3.
Lemma F_16854 : fetch_word Plain.M.loaded_segments (0x168ac : word) = Some W_16854.
Proof. vm_refl. Qed.
Lemma D_16854 : decode_any W_16854 = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16858 : bv 32 := 0x20000737.
Lemma F_16858 : fetch_word Plain.M.loaded_segments (0x168b0 : word) = Some W_16858.
Proof. vm_refl. Qed.
Lemma D_16858 : decode_any W_16858 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1685c : bv 32 := 0xfe17071b.
Lemma F_1685c : fetch_word Plain.M.loaded_segments (0x168b4 : word) = Some W_1685c.
Proof. vm_refl. Qed.
Lemma D_1685c : decode_any W_1685c = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16860 : bv 32 := 0x0ae6e863.
Lemma F_16860 : fetch_word Plain.M.loaded_segments (0x168b8 : word) = Some W_16860.
Proof. vm_refl. Qed.
Lemma D_16860 : decode_any W_16860 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16910 : bv 32 := 0x01f68693.
Lemma F_16910 : fetch_word Plain.M.loaded_segments (0x16968 : word) = Some W_16910.
Proof. vm_refl. Qed.
Lemma D_16910 : decode_any W_16910 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16914 : bv 32 := 0x0056d413.
Lemma F_16914 : fetch_word Plain.M.loaded_segments (0x1696c : word) = Some W_16914.
Proof. vm_refl. Qed.
Lemma D_16914 : decode_any W_16914 = Some (ShiftImm ALU_SRL 8 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16918 : bv 32 := 0x02b406b3.
Lemma F_16918 : fetch_word Plain.M.loaded_segments (0x16970 : word) = Some W_16918.
Proof. vm_refl. Qed.
Lemma D_16918 : decode_any W_16918 = Some (Mul M_MUL 13 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1691c : bv 32 := 0x00269693.
Lemma F_1691c : fetch_word Plain.M.loaded_segments (0x16974 : word) = Some W_1691c.
Proof. vm_refl. Qed.
Lemma D_1691c : decode_any W_1691c = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16920 : bv 32 := 0x01f6d713.
Lemma F_16920 : fetch_word Plain.M.loaded_segments (0x16978 : word) = Some W_16920.
Proof. vm_refl. Qed.
Lemma D_16920 : decode_any W_16920 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16924 : bv 32 := 0x0a070463.
Lemma F_16924 : fetch_word Plain.M.loaded_segments (0x1697c : word) = Some W_16924.
Proof. vm_refl. Qed.
Lemma D_16924 : decode_any W_16924 = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16984 : bv 32 := 0x00016517.
Lemma F_16984 : fetch_word Plain.M.loaded_segments (0x169dc : word) = Some W_16984.
Proof. vm_refl. Qed.
Lemma D_16984 : decode_any W_16984 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16988 : bv 32 := 0xda453503.
Lemma F_16988 : fetch_word Plain.M.loaded_segments (0x169e0 : word) = Some W_16988.
Proof. vm_refl. Qed.
Lemma D_16988 : decode_any W_16988 = Some (Load SZ8 true 10 10 3492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1698c : bv 32 := 0x00052503.
Lemma F_1698c : fetch_word Plain.M.loaded_segments (0x169e4 : word) = Some W_1698c.
Proof. vm_refl. Qed.
Lemma D_1698c : decode_any W_1698c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16990 : bv 32 := 0x00500593.
Lemma F_16990 : fetch_word Plain.M.loaded_segments (0x169e8 : word) = Some W_16990.
Proof. vm_refl. Qed.
Lemma D_16990 : decode_any W_16990 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16994 : bv 32 := 0x0ca5c663.
Lemma F_16994 : fetch_word Plain.M.loaded_segments (0x169ec : word) = Some W_16994.
Proof. vm_refl. Qed.
Lemma D_16994 : decode_any W_16994 = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16998 : bv 32 := 0xffffa517.
Lemma F_16998 : fetch_word Plain.M.loaded_segments (0x169f0 : word) = Some W_16998.
Proof. vm_refl. Qed.
Lemma D_16998 : decode_any W_16998 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1699c : bv 32 := 0xffffa597.
Lemma F_1699c : fetch_word Plain.M.loaded_segments (0x169f4 : word) = Some W_1699c.
Proof. vm_refl. Qed.
Lemma D_1699c : decode_any W_1699c = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169a0 : bv 32 := 0xbd450513.
Lemma F_169a0 : fetch_word Plain.M.loaded_segments (0x169f8 : word) = Some W_169a0.
Proof. vm_refl. Qed.
Lemma D_169a0 : decode_any W_169a0 = Some (OpImm ALU_ADD 10 10 3028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169a4 : bv 32 := 0xf4758593.
Lemma F_169a4 : fetch_word Plain.M.loaded_segments (0x169fc : word) = Some W_169a4.
Proof. vm_refl. Qed.
Lemma D_169a4 : decode_any W_169a4 = Some (OpImm ALU_ADD 11 11 3911, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169a8 : bv 32 := 0x00000613.
Lemma F_169a8 : fetch_word Plain.M.loaded_segments (0x16a00 : word) = Some W_169a8.
Proof. vm_refl. Qed.
Lemma D_169a8 : decode_any W_169a8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169ac : bv 32 := 0x02813083.
Lemma F_169ac : fetch_word Plain.M.loaded_segments (0x16a04 : word) = Some W_169ac.
Proof. vm_refl. Qed.
Lemma D_169ac : decode_any W_169ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169b0 : bv 32 := 0x02013403.
Lemma F_169b0 : fetch_word Plain.M.loaded_segments (0x16a08 : word) = Some W_169b0.
Proof. vm_refl. Qed.
Lemma D_169b0 : decode_any W_169b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169b4 : bv 32 := 0x01813483.
Lemma F_169b4 : fetch_word Plain.M.loaded_segments (0x16a0c : word) = Some W_169b4.
Proof. vm_refl. Qed.
Lemma D_169b4 : decode_any W_169b4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169b8 : bv 32 := 0x01013903.
Lemma F_169b8 : fetch_word Plain.M.loaded_segments (0x16a10 : word) = Some W_169b8.
Proof. vm_refl. Qed.
Lemma D_169b8 : decode_any W_169b8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169bc : bv 32 := 0x00813983.
Lemma F_169bc : fetch_word Plain.M.loaded_segments (0x16a14 : word) = Some W_169bc.
Proof. vm_refl. Qed.
Lemma D_169bc : decode_any W_169bc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169c0 : bv 32 := 0x00013a03.
Lemma F_169c0 : fetch_word Plain.M.loaded_segments (0x16a18 : word) = Some W_169c0.
Proof. vm_refl. Qed.
Lemma D_169c0 : decode_any W_169c0 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169c4 : bv 32 := 0x03010113.
Lemma F_169c4 : fetch_word Plain.M.loaded_segments (0x16a1c : word) = Some W_169c4.
Proof. vm_refl. Qed.
Lemma D_169c4 : decode_any W_169c4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169c8 : bv 32 := 0xa59fe06f.
Lemma F_169c8 : fetch_word Plain.M.loaded_segments (0x16a20 : word) = Some W_169c8.
Proof. vm_refl. Qed.
Lemma D_169c8 : decode_any W_169c8 = Some (Jal 0 2091608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169cc : bv 32 := 0x04000737.
Lemma F_169cc : fetch_word Plain.M.loaded_segments (0x16a24 : word) = Some W_169cc.
Proof. vm_refl. Qed.
Lemma D_169cc : decode_any W_169cc = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169d0 : bv 32 := 0x0017071b.
Lemma F_169d0 : fetch_word Plain.M.loaded_segments (0x16a28 : word) = Some W_169d0.
Proof. vm_refl. Qed.
Lemma D_169d0 : decode_any W_169d0 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169d4 : bv 32 := 0x02e6e663.
Lemma F_169d4 : fetch_word Plain.M.loaded_segments (0x16a2c : word) = Some W_169d4.
Proof. vm_refl. Qed.
Lemma D_169d4 : decode_any W_169d4 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169d8 : bv 32 := 0x00016517.
Lemma F_169d8 : fetch_word Plain.M.loaded_segments (0x16a30 : word) = Some W_169d8.
Proof. vm_refl. Qed.
Lemma D_169d8 : decode_any W_169d8 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169dc : bv 32 := 0xd5053503.
Lemma F_169dc : fetch_word Plain.M.loaded_segments (0x16a34 : word) = Some W_169dc.
Proof. vm_refl. Qed.
Lemma D_169dc : decode_any W_169dc = Some (Load SZ8 true 10 10 3408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169e0 : bv 32 := 0x00052503.
Lemma F_169e0 : fetch_word Plain.M.loaded_segments (0x16a38 : word) = Some W_169e0.
Proof. vm_refl. Qed.
Lemma D_169e0 : decode_any W_169e0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169e4 : bv 32 := 0x00500593.
Lemma F_169e4 : fetch_word Plain.M.loaded_segments (0x16a3c : word) = Some W_169e4.
Proof. vm_refl. Qed.
Lemma D_169e4 : decode_any W_169e4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169e8 : bv 32 := 0x06a5cc63.
Lemma F_169e8 : fetch_word Plain.M.loaded_segments (0x16a40 : word) = Some W_169e8.
Proof. vm_refl. Qed.
Lemma D_169e8 : decode_any W_169e8 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169ec : bv 32 := 0xffffa517.
Lemma F_169ec : fetch_word Plain.M.loaded_segments (0x16a44 : word) = Some W_169ec.
Proof. vm_refl. Qed.
Lemma D_169ec : decode_any W_169ec = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169f0 : bv 32 := 0xffffa597.
Lemma F_169f0 : fetch_word Plain.M.loaded_segments (0x16a48 : word) = Some W_169f0.
Proof. vm_refl. Qed.
Lemma D_169f0 : decode_any W_169f0 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169f4 : bv 32 := 0xa1050513.
Lemma F_169f4 : fetch_word Plain.M.loaded_segments (0x16a4c : word) = Some W_169f4.
Proof. vm_refl. Qed.
Lemma D_169f4 : decode_any W_169f4 = Some (OpImm ALU_ADD 10 10 2576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169f8 : bv 32 := 0xef358593.
Lemma F_169f8 : fetch_word Plain.M.loaded_segments (0x16a50 : word) = Some W_169f8.
Proof. vm_refl. Qed.
Lemma D_169f8 : decode_any W_169f8 = Some (OpImm ALU_ADD 11 11 3827, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_169fc : bv 32 := 0x0600006f.
Lemma F_169fc : fetch_word Plain.M.loaded_segments (0x16a54 : word) = Some W_169fc.
Proof. vm_refl. Qed.
Lemma D_169fc : decode_any W_169fc = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a00 : bv 32 := 0x000056b7.
Lemma F_16a00 : fetch_word Plain.M.loaded_segments (0x16a58 : word) = Some W_16a00.
Proof. vm_refl. Qed.
Lemma D_16a00 : decode_any W_16a00 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a04 : bv 32 := 0xe216869b.
Lemma F_16a04 : fetch_word Plain.M.loaded_segments (0x16a5c : word) = Some W_16a04.
Proof. vm_refl. Qed.
Lemma D_16a04 : decode_any W_16a04 = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a08 : bv 32 := 0x02d56663.
Lemma F_16a08 : fetch_word Plain.M.loaded_segments (0x16a60 : word) = Some W_16a08.
Proof. vm_refl. Qed.
Lemma D_16a08 : decode_any W_16a08 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a0c : bv 32 := 0x00016517.
Lemma F_16a0c : fetch_word Plain.M.loaded_segments (0x16a64 : word) = Some W_16a0c.
Proof. vm_refl. Qed.
Lemma D_16a0c : decode_any W_16a0c = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a10 : bv 32 := 0xd1c53503.
Lemma F_16a10 : fetch_word Plain.M.loaded_segments (0x16a68 : word) = Some W_16a10.
Proof. vm_refl. Qed.
Lemma D_16a10 : decode_any W_16a10 = Some (Load SZ8 true 10 10 3356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a14 : bv 32 := 0x00052503.
Lemma F_16a14 : fetch_word Plain.M.loaded_segments (0x16a6c : word) = Some W_16a14.
Proof. vm_refl. Qed.
Lemma D_16a14 : decode_any W_16a14 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a18 : bv 32 := 0x00500593.
Lemma F_16a18 : fetch_word Plain.M.loaded_segments (0x16a70 : word) = Some W_16a18.
Proof. vm_refl. Qed.
Lemma D_16a18 : decode_any W_16a18 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a1c : bv 32 := 0x04a5c263.
Lemma F_16a1c : fetch_word Plain.M.loaded_segments (0x16a74 : word) = Some W_16a1c.
Proof. vm_refl. Qed.
Lemma D_16a1c : decode_any W_16a1c = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a20 : bv 32 := 0xffffa517.
Lemma F_16a20 : fetch_word Plain.M.loaded_segments (0x16a78 : word) = Some W_16a20.
Proof. vm_refl. Qed.
Lemma D_16a20 : decode_any W_16a20 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a24 : bv 32 := 0xffffa597.
Lemma F_16a24 : fetch_word Plain.M.loaded_segments (0x16a7c : word) = Some W_16a24.
Proof. vm_refl. Qed.
Lemma D_16a24 : decode_any W_16a24 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a28 : bv 32 := 0x7d750513.
Lemma F_16a28 : fetch_word Plain.M.loaded_segments (0x16a80 : word) = Some W_16a28.
Proof. vm_refl. Qed.
Lemma D_16a28 : decode_any W_16a28 = Some (OpImm ALU_ADD 10 10 2007, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a2c : bv 32 := 0xebf58593.
Lemma F_16a2c : fetch_word Plain.M.loaded_segments (0x16a84 : word) = Some W_16a2c.
Proof. vm_refl. Qed.
Lemma D_16a2c : decode_any W_16a2c = Some (OpImm ALU_ADD 11 11 3775, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a30 : bv 32 := 0x02c0006f.
Lemma F_16a30 : fetch_word Plain.M.loaded_segments (0x16a88 : word) = Some W_16a30.
Proof. vm_refl. Qed.
Lemma D_16a30 : decode_any W_16a30 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a34 : bv 32 := 0x04d5e863.
Lemma F_16a34 : fetch_word Plain.M.loaded_segments (0x16a8c : word) = Some W_16a34.
Proof. vm_refl. Qed.
Lemma D_16a34 : decode_any W_16a34 = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a38 : bv 32 := 0x00016517.
Lemma F_16a38 : fetch_word Plain.M.loaded_segments (0x16a90 : word) = Some W_16a38.
Proof. vm_refl. Qed.
Lemma D_16a38 : decode_any W_16a38 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a3c : bv 32 := 0xcf053503.
Lemma F_16a3c : fetch_word Plain.M.loaded_segments (0x16a94 : word) = Some W_16a3c.
Proof. vm_refl. Qed.
Lemma D_16a3c : decode_any W_16a3c = Some (Load SZ8 true 10 10 3312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a40 : bv 32 := 0x00052503.
Lemma F_16a40 : fetch_word Plain.M.loaded_segments (0x16a98 : word) = Some W_16a40.
Proof. vm_refl. Qed.
Lemma D_16a40 : decode_any W_16a40 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a44 : bv 32 := 0x00500593.
Lemma F_16a44 : fetch_word Plain.M.loaded_segments (0x16a9c : word) = Some W_16a44.
Proof. vm_refl. Qed.
Lemma D_16a44 : decode_any W_16a44 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a48 : bv 32 := 0x00a5cc63.
Lemma F_16a48 : fetch_word Plain.M.loaded_segments (0x16aa0 : word) = Some W_16a48.
Proof. vm_refl. Qed.
Lemma D_16a48 : decode_any W_16a48 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a4c : bv 32 := 0xffffa517.
Lemma F_16a4c : fetch_word Plain.M.loaded_segments (0x16aa4 : word) = Some W_16a4c.
Proof. vm_refl. Qed.
Lemma D_16a4c : decode_any W_16a4c = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a50 : bv 32 := 0xffffa597.
Lemma F_16a50 : fetch_word Plain.M.loaded_segments (0x16aa8 : word) = Some W_16a50.
Proof. vm_refl. Qed.
Lemma D_16a50 : decode_any W_16a50 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a54 : bv 32 := 0x2d650513.
Lemma F_16a54 : fetch_word Plain.M.loaded_segments (0x16aac : word) = Some W_16a54.
Proof. vm_refl. Qed.
Lemma D_16a54 : decode_any W_16a54 = Some (OpImm ALU_ADD 10 10 726, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a58 : bv 32 := 0xe9358593.
Lemma F_16a58 : fetch_word Plain.M.loaded_segments (0x16ab0 : word) = Some W_16a58.
Proof. vm_refl. Qed.
Lemma D_16a58 : decode_any W_16a58 = Some (OpImm ALU_ADD 11 11 3731, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a5c : bv 32 := 0x929fe0ef.
Lemma F_16a5c : fetch_word Plain.M.loaded_segments (0x16ab4 : word) = Some W_16a5c.
Proof. vm_refl. Qed.
Lemma D_16a5c : decode_any W_16a5c = Some (Jal 1 2091304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a60 : bv 32 := 0x00000513.
Lemma F_16a60 : fetch_word Plain.M.loaded_segments (0x16ab8 : word) = Some W_16a60.
Proof. vm_refl. Qed.
Lemma D_16a60 : decode_any W_16a60 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a64 : bv 32 := 0x02813083.
Lemma F_16a64 : fetch_word Plain.M.loaded_segments (0x16abc : word) = Some W_16a64.
Proof. vm_refl. Qed.
Lemma D_16a64 : decode_any W_16a64 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a68 : bv 32 := 0x02013403.
Lemma F_16a68 : fetch_word Plain.M.loaded_segments (0x16ac0 : word) = Some W_16a68.
Proof. vm_refl. Qed.
Lemma D_16a68 : decode_any W_16a68 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a6c : bv 32 := 0x01813483.
Lemma F_16a6c : fetch_word Plain.M.loaded_segments (0x16ac4 : word) = Some W_16a6c.
Proof. vm_refl. Qed.
Lemma D_16a6c : decode_any W_16a6c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a70 : bv 32 := 0x01013903.
Lemma F_16a70 : fetch_word Plain.M.loaded_segments (0x16ac8 : word) = Some W_16a70.
Proof. vm_refl. Qed.
Lemma D_16a70 : decode_any W_16a70 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a74 : bv 32 := 0x00813983.
Lemma F_16a74 : fetch_word Plain.M.loaded_segments (0x16acc : word) = Some W_16a74.
Proof. vm_refl. Qed.
Lemma D_16a74 : decode_any W_16a74 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a78 : bv 32 := 0x00013a03.
Lemma F_16a78 : fetch_word Plain.M.loaded_segments (0x16ad0 : word) = Some W_16a78.
Proof. vm_refl. Qed.
Lemma D_16a78 : decode_any W_16a78 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a7c : bv 32 := 0x03010113.
Lemma F_16a7c : fetch_word Plain.M.loaded_segments (0x16ad4 : word) = Some W_16a7c.
Proof. vm_refl. Qed.
Lemma D_16a7c : decode_any W_16a7c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a80 : bv 32 := 0x00008067.
Lemma F_16a80 : fetch_word Plain.M.loaded_segments (0x16ad8 : word) = Some W_16a80.
Proof. vm_refl. Qed.
Lemma D_16a80 : decode_any W_16a80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a84 : bv 32 := 0x00050993.
Lemma F_16a84 : fetch_word Plain.M.loaded_segments (0x16adc : word) = Some W_16a84.
Proof. vm_refl. Qed.
Lemma D_16a84 : decode_any W_16a84 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a88 : bv 32 := 0x00058913.
Lemma F_16a88 : fetch_word Plain.M.loaded_segments (0x16ae0 : word) = Some W_16a88.
Proof. vm_refl. Qed.
Lemma D_16a88 : decode_any W_16a88 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a8c : bv 32 := 0x00060a13.
Lemma F_16a8c : fetch_word Plain.M.loaded_segments (0x16ae4 : word) = Some W_16a8c.
Proof. vm_refl. Qed.
Lemma D_16a8c : decode_any W_16a8c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a90 : bv 32 := 0x00100513.
Lemma F_16a90 : fetch_word Plain.M.loaded_segments (0x16ae8 : word) = Some W_16a90.
Proof. vm_refl. Qed.
Lemma D_16a90 : decode_any W_16a90 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a94 : bv 32 := 0x04000593.
Lemma F_16a94 : fetch_word Plain.M.loaded_segments (0x16aec : word) = Some W_16a94.
Proof. vm_refl. Qed.
Lemma D_16a94 : decode_any W_16a94 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a98 : bv 32 := 0x00100493.
Lemma F_16a98 : fetch_word Plain.M.loaded_segments (0x16af0 : word) = Some W_16a98.
Proof. vm_refl. Qed.
Lemma D_16a98 : decode_any W_16a98 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a9c : bv 32 := 0x3ac0a0ef.
Lemma F_16a9c : fetch_word Plain.M.loaded_segments (0x16af4 : word) = Some W_16a9c.
Proof. vm_refl. Qed.
Lemma D_16a9c : decode_any W_16a9c = Some (Jal 1 41900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aa0 : bv 32 := 0x02050463.
Lemma F_16aa0 : fetch_word Plain.M.loaded_segments (0x16af8 : word) = Some W_16aa0.
Proof. vm_refl. Qed.
Lemma D_16aa0 : decode_any W_16aa0 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aa4 : bv 32 := 0xfe8a059b.
Lemma F_16aa4 : fetch_word Plain.M.loaded_segments (0x16afc : word) = Some W_16aa4.
Proof. vm_refl. Qed.
Lemma D_16aa4 : decode_any W_16aa4 = Some (OpImm32 11 20 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aa8 : bv 32 := 0xff75f593.
Lemma F_16aa8 : fetch_word Plain.M.loaded_segments (0x16b00 : word) = Some W_16aa8.
Proof. vm_refl. Qed.
Lemma D_16aa8 : decode_any W_16aa8 = Some (OpImm ALU_AND 11 11 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aac : bv 32 := 0x01352023.
Lemma F_16aac : fetch_word Plain.M.loaded_segments (0x16b04 : word) = Some W_16aac.
Proof. vm_refl. Qed.
Lemma D_16aac : decode_any W_16aac = Some (Store SZ4 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ab0 : bv 32 := 0x01252223.
Lemma F_16ab0 : fetch_word Plain.M.loaded_segments (0x16b08 : word) = Some W_16ab0.
Proof. vm_refl. Qed.
Lemma D_16ab0 : decode_any W_16ab0 = Some (Store SZ4 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ab4 : bv 32 := 0x01452423.
Lemma F_16ab4 : fetch_word Plain.M.loaded_segments (0x16b0c : word) = Some W_16ab4.
Proof. vm_refl. Qed.
Lemma D_16ab4 : decode_any W_16ab4 = Some (Store SZ4 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ab8 : bv 32 := 0x00852823.
Lemma F_16ab8 : fetch_word Plain.M.loaded_segments (0x16b10 : word) = Some W_16ab8.
Proof. vm_refl. Qed.
Lemma D_16ab8 : decode_any W_16ab8 = Some (Store SZ4 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16abc : bv 32 := 0x02058a63.
Lemma F_16abc : fetch_word Plain.M.loaded_segments (0x16b14 : word) = Some W_16abc.
Proof. vm_refl. Qed.
Lemma D_16abc : decode_any W_16abc = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ac0 : bv 32 := 0x00100593.
Lemma F_16ac0 : fetch_word Plain.M.loaded_segments (0x16b18 : word) = Some W_16ac0.
Proof. vm_refl. Qed.
Lemma D_16ac0 : decode_any W_16ac0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ac4 : bv 32 := 0x0300006f.
Lemma F_16ac4 : fetch_word Plain.M.loaded_segments (0x16b1c : word) = Some W_16ac4.
Proof. vm_refl. Qed.
Lemma D_16ac4 : decode_any W_16ac4 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ac8 : bv 32 := 0x00016517.
Lemma F_16ac8 : fetch_word Plain.M.loaded_segments (0x16b20 : word) = Some W_16ac8.
Proof. vm_refl. Qed.
Lemma D_16ac8 : decode_any W_16ac8 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16acc : bv 32 := 0xc6053503.
Lemma F_16acc : fetch_word Plain.M.loaded_segments (0x16b24 : word) = Some W_16acc.
Proof. vm_refl. Qed.
Lemma D_16acc : decode_any W_16acc = Some (Load SZ8 true 10 10 3168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ad0 : bv 32 := 0x00052503.
Lemma F_16ad0 : fetch_word Plain.M.loaded_segments (0x16b28 : word) = Some W_16ad0.
Proof. vm_refl. Qed.
Lemma D_16ad0 : decode_any W_16ad0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ad4 : bv 32 := 0x00500593.
Lemma F_16ad4 : fetch_word Plain.M.loaded_segments (0x16b2c : word) = Some W_16ad4.
Proof. vm_refl. Qed.
Lemma D_16ad4 : decode_any W_16ad4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ad8 : bv 32 := 0xf8a5c4e3.
Lemma F_16ad8 : fetch_word Plain.M.loaded_segments (0x16b30 : word) = Some W_16ad8.
Proof. vm_refl. Qed.
Lemma D_16ad8 : decode_any W_16ad8 = Some (Branch BC_LT 11 10 8072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16adc : bv 32 := 0xffffa517.
Lemma F_16adc : fetch_word Plain.M.loaded_segments (0x16b34 : word) = Some W_16adc.
Proof. vm_refl. Qed.
Lemma D_16adc : decode_any W_16adc = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ae0 : bv 32 := 0xffffa597.
Lemma F_16ae0 : fetch_word Plain.M.loaded_segments (0x16b38 : word) = Some W_16ae0.
Proof. vm_refl. Qed.
Lemma D_16ae0 : decode_any W_16ae0 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ae4 : bv 32 := 0x9eb50513.
Lemma F_16ae4 : fetch_word Plain.M.loaded_segments (0x16b3c : word) = Some W_16ae4.
Proof. vm_refl. Qed.
Lemma D_16ae4 : decode_any W_16ae4 = Some (OpImm ALU_ADD 10 10 2539, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ae8 : bv 32 := 0xe0358593.
Lemma F_16ae8 : fetch_word Plain.M.loaded_segments (0x16b40 : word) = Some W_16ae8.
Proof. vm_refl. Qed.
Lemma D_16ae8 : decode_any W_16ae8 = Some (OpImm ALU_ADD 11 11 3587, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aec : bv 32 := 0xebdff06f.
Lemma F_16aec : fetch_word Plain.M.loaded_segments (0x16b44 : word) = Some W_16aec.
Proof. vm_refl. Qed.
Lemma D_16aec : decode_any W_16aec = Some (Jal 0 2096828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16af0 : bv 32 := 0x00300593.
Lemma F_16af0 : fetch_word Plain.M.loaded_segments (0x16b48 : word) = Some W_16af0.
Proof. vm_refl. Qed.
Lemma D_16af0 : decode_any W_16af0 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16af4 : bv 32 := 0x00b52623.
Lemma F_16af4 : fetch_word Plain.M.loaded_segments (0x16b4c : word) = Some W_16af4.
Proof. vm_refl. Qed.
Lemma D_16af4 : decode_any W_16af4 = Some (Store SZ4 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16af8 : bv 32 := 0x0310000f.
Lemma F_16af8 : fetch_word Plain.M.loaded_segments (0x16b50 : word) = Some W_16af8.
Proof. vm_refl. Qed.
Lemma D_16af8 : decode_any W_16af8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16afc : bv 32 := 0x00952a23.
Lemma F_16afc : fetch_word Plain.M.loaded_segments (0x16b54 : word) = Some W_16afc.
Proof. vm_refl. Qed.
Lemma D_16afc : decode_any W_16afc = Some (Store SZ4 10 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b00 : bv 32 := 0x0330000f.
Lemma F_16b00 : fetch_word Plain.M.loaded_segments (0x16b58 : word) = Some W_16b00.
Proof. vm_refl. Qed.
Lemma D_16b00 : decode_any W_16b00 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b04 : bv 32 := 0x02052023.
Lemma F_16b04 : fetch_word Plain.M.loaded_segments (0x16b5c : word) = Some W_16b04.
Proof. vm_refl. Qed.
Lemma D_16b04 : decode_any W_16b04 = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b08 : bv 32 := 0xf5dff06f.
Lemma F_16b08 : fetch_word Plain.M.loaded_segments (0x16b60 : word) = Some W_16b08.
Proof. vm_refl. Qed.
Lemma D_16b08 : decode_any W_16b08 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

