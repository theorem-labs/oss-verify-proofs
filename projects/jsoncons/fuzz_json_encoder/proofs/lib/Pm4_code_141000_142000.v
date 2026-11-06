(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1415fc : bv 32 := 0x00020513.
Lemma F_1415fc : fetch_word Asan.M.loaded_segments (0x141640 : word) = Some W_1415fc.
Proof. vm_refl. Qed.
Lemma D_1415fc : decode_any W_1415fc = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141600 : bv 32 := 0xf5c50513.
Lemma F_141600 : fetch_word Asan.M.loaded_segments (0x141644 : word) = Some W_141600.
Proof. vm_refl. Qed.
Lemma D_141600 : decode_any W_141600 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141604 : bv 32 := 0x00008067.
Lemma F_141604 : fetch_word Asan.M.loaded_segments (0x141648 : word) = Some W_141604.
Proof. vm_refl. Qed.
Lemma D_141604 : decode_any W_141604 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1417f0 : bv 32 := 0xfd010113.
Lemma F_1417f0 : fetch_word Asan.M.loaded_segments (0x141834 : word) = Some W_1417f0.
Proof. vm_refl. Qed.
Lemma D_1417f0 : decode_any W_1417f0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1417f4 : bv 32 := 0x02113423.
Lemma F_1417f4 : fetch_word Asan.M.loaded_segments (0x141838 : word) = Some W_1417f4.
Proof. vm_refl. Qed.
Lemma D_1417f4 : decode_any W_1417f4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1417f8 : bv 32 := 0x02813023.
Lemma F_1417f8 : fetch_word Asan.M.loaded_segments (0x14183c : word) = Some W_1417f8.
Proof. vm_refl. Qed.
Lemma D_1417f8 : decode_any W_1417f8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1417fc : bv 32 := 0x00913c23.
Lemma F_1417fc : fetch_word Asan.M.loaded_segments (0x141840 : word) = Some W_1417fc.
Proof. vm_refl. Qed.
Lemma D_1417fc : decode_any W_1417fc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141800 : bv 32 := 0x01213823.
Lemma F_141800 : fetch_word Asan.M.loaded_segments (0x141844 : word) = Some W_141800.
Proof. vm_refl. Qed.
Lemma D_141800 : decode_any W_141800 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141804 : bv 32 := 0x01313423.
Lemma F_141804 : fetch_word Asan.M.loaded_segments (0x141848 : word) = Some W_141804.
Proof. vm_refl. Qed.
Lemma D_141804 : decode_any W_141804 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141808 : bv 32 := 0x01413023.
Lemma F_141808 : fetch_word Asan.M.loaded_segments (0x14184c : word) = Some W_141808.
Proof. vm_refl. Qed.
Lemma D_141808 : decode_any W_141808 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14180c : bv 32 := 0x00058493.
Lemma F_14180c : fetch_word Asan.M.loaded_segments (0x141850 : word) = Some W_14180c.
Proof. vm_refl. Qed.
Lemma D_14180c : decode_any W_14180c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141810 : bv 32 := 0x00050913.
Lemma F_141810 : fetch_word Asan.M.loaded_segments (0x141854 : word) = Some W_141810.
Proof. vm_refl. Qed.
Lemma D_141810 : decode_any W_141810 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141814 : bv 32 := 0x0057c517.
Lemma F_141814 : fetch_word Asan.M.loaded_segments (0x141858 : word) = Some W_141814.
Proof. vm_refl. Qed.
Lemma D_141814 : decode_any W_141814 = Some (Auipc 10 1404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141818 : bv 32 := 0x7c850a13.
Lemma F_141818 : fetch_word Asan.M.loaded_segments (0x14185c : word) = Some W_141818.
Proof. vm_refl. Qed.
Lemma D_141818 : decode_any W_141818 = Some (OpImm ALU_ADD 20 10 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14181c : bv 32 := 0x004a0413.
Lemma F_14181c : fetch_word Asan.M.loaded_segments (0x141860 : word) = Some W_14181c.
Proof. vm_refl. Qed.
Lemma D_14181c : decode_any W_14181c = Some (OpImm ALU_ADD 8 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141820 : bv 32 := 0x00040513.
Lemma F_141820 : fetch_word Asan.M.loaded_segments (0x141864 : word) = Some W_141820.
Proof. vm_refl. Qed.
Lemma D_141820 : decode_any W_141820 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141824 : bv 32 := 0x6f9110ef.
Lemma F_141824 : fetch_word Asan.M.loaded_segments (0x141868 : word) = Some W_141824.
Proof. vm_refl. Qed.
Lemma D_141824 : decode_any W_141824 = Some (Jal 1 73464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141828 : bv 32 := 0x000a4503.
Lemma F_141828 : fetch_word Asan.M.loaded_segments (0x14186c : word) = Some W_141828.
Proof. vm_refl. Qed.
Lemma D_141828 : decode_any W_141828 = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14182c : bv 32 := 0xfff00993.
Lemma F_14182c : fetch_word Asan.M.loaded_segments (0x141870 : word) = Some W_14182c.
Proof. vm_refl. Qed.
Lemma D_14182c : decode_any W_14182c = Some (OpImm ALU_ADD 19 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141830 : bv 32 := 0x04051e63.
Lemma F_141830 : fetch_word Asan.M.loaded_segments (0x141874 : word) = Some W_141830.
Proof. vm_refl. Qed.
Lemma D_141830 : decode_any W_141830 = Some (Branch BC_NE 10 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141834 : bv 32 := 0x010a3503.
Lemma F_141834 : fetch_word Asan.M.loaded_segments (0x141878 : word) = Some W_141834.
Proof. vm_refl. Qed.
Lemma D_141834 : decode_any W_141834 = Some (Load SZ8 true 10 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141838 : bv 32 := 0x00051663.
Lemma F_141838 : fetch_word Asan.M.loaded_segments (0x14187c : word) = Some W_141838.
Proof. vm_refl. Qed.
Lemma D_141838 : decode_any W_141838 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141844 : bv 32 := 0x008a2583.
Lemma F_141844 : fetch_word Asan.M.loaded_segments (0x141888 : word) = Some W_141844.
Proof. vm_refl. Qed.
Lemma D_141844 : decode_any W_141844 = Some (Load SZ4 true 11 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141848 : bv 32 := 0x02000613.
Lemma F_141848 : fetch_word Asan.M.loaded_segments (0x14188c : word) = Some W_141848.
Proof. vm_refl. Qed.
Lemma D_141848 : decode_any W_141848 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14184c : bv 32 := 0x02c59263.
Lemma F_14184c : fetch_word Asan.M.loaded_segments (0x141890 : word) = Some W_14184c.
Proof. vm_refl. Qed.
Lemma D_14184c : decode_any W_14184c = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141870 : bv 32 := 0x00000993.
Lemma F_141870 : fetch_word Asan.M.loaded_segments (0x1418b4 : word) = Some W_141870.
Proof. vm_refl. Qed.
Lemma D_141870 : decode_any W_141870 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141874 : bv 32 := 0x00359613.
Lemma F_141874 : fetch_word Asan.M.loaded_segments (0x1418b8 : word) = Some W_141874.
Proof. vm_refl. Qed.
Lemma D_141874 : decode_any W_141874 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141878 : bv 32 := 0x00c50533.
Lemma F_141878 : fetch_word Asan.M.loaded_segments (0x1418bc : word) = Some W_141878.
Proof. vm_refl. Qed.
Lemma D_141878 : decode_any W_141878 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14187c : bv 32 := 0x00158593.
Lemma F_14187c : fetch_word Asan.M.loaded_segments (0x1418c0 : word) = Some W_14187c.
Proof. vm_refl. Qed.
Lemma D_14187c : decode_any W_14187c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141880 : bv 32 := 0x01253423.
Lemma F_141880 : fetch_word Asan.M.loaded_segments (0x1418c4 : word) = Some W_141880.
Proof. vm_refl. Qed.
Lemma D_141880 : decode_any W_141880 = Some (Store SZ8 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141884 : bv 32 := 0x10953423.
Lemma F_141884 : fetch_word Asan.M.loaded_segments (0x1418c8 : word) = Some W_141884.
Proof. vm_refl. Qed.
Lemma D_141884 : decode_any W_141884 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141888 : bv 32 := 0x00ba2423.
Lemma F_141888 : fetch_word Asan.M.loaded_segments (0x1418cc : word) = Some W_141888.
Proof. vm_refl. Qed.
Lemma D_141888 : decode_any W_141888 = Some (Store SZ4 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14188c : bv 32 := 0x00040513.
Lemma F_14188c : fetch_word Asan.M.loaded_segments (0x1418d0 : word) = Some W_14188c.
Proof. vm_refl. Qed.
Lemma D_14188c : decode_any W_14188c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141890 : bv 32 := 0x114120ef.
Lemma F_141890 : fetch_word Asan.M.loaded_segments (0x1418d4 : word) = Some W_141890.
Proof. vm_refl. Qed.
Lemma D_141890 : decode_any W_141890 = Some (Jal 1 74004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141894 : bv 32 := 0x00098513.
Lemma F_141894 : fetch_word Asan.M.loaded_segments (0x1418d8 : word) = Some W_141894.
Proof. vm_refl. Qed.
Lemma D_141894 : decode_any W_141894 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141898 : bv 32 := 0x02813083.
Lemma F_141898 : fetch_word Asan.M.loaded_segments (0x1418dc : word) = Some W_141898.
Proof. vm_refl. Qed.
Lemma D_141898 : decode_any W_141898 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14189c : bv 32 := 0x02013403.
Lemma F_14189c : fetch_word Asan.M.loaded_segments (0x1418e0 : word) = Some W_14189c.
Proof. vm_refl. Qed.
Lemma D_14189c : decode_any W_14189c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1418a0 : bv 32 := 0x01813483.
Lemma F_1418a0 : fetch_word Asan.M.loaded_segments (0x1418e4 : word) = Some W_1418a0.
Proof. vm_refl. Qed.
Lemma D_1418a0 : decode_any W_1418a0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1418a4 : bv 32 := 0x01013903.
Lemma F_1418a4 : fetch_word Asan.M.loaded_segments (0x1418e8 : word) = Some W_1418a4.
Proof. vm_refl. Qed.
Lemma D_1418a4 : decode_any W_1418a4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1418a8 : bv 32 := 0x00813983.
Lemma F_1418a8 : fetch_word Asan.M.loaded_segments (0x1418ec : word) = Some W_1418a8.
Proof. vm_refl. Qed.
Lemma D_1418a8 : decode_any W_1418a8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1418ac : bv 32 := 0x00013a03.
Lemma F_1418ac : fetch_word Asan.M.loaded_segments (0x1418f0 : word) = Some W_1418ac.
Proof. vm_refl. Qed.
Lemma D_1418ac : decode_any W_1418ac = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1418b0 : bv 32 := 0x03010113.
Lemma F_1418b0 : fetch_word Asan.M.loaded_segments (0x1418f4 : word) = Some W_1418b0.
Proof. vm_refl. Qed.
Lemma D_1418b0 : decode_any W_1418b0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1418b4 : bv 32 := 0x00008067.
Lemma F_1418b4 : fetch_word Asan.M.loaded_segments (0x1418f8 : word) = Some W_1418b4.
Proof. vm_refl. Qed.
Lemma D_1418b4 : decode_any W_1418b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d28 : bv 32 := 0xfffff5b7.
Lemma F_141d28 : fetch_word Asan.M.loaded_segments (0x141d6c : word) = Some W_141d28.
Proof. vm_refl. Qed.
Lemma D_141d28 : decode_any W_141d28 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d2c : bv 32 := 0x0015859b.
Lemma F_141d2c : fetch_word Asan.M.loaded_segments (0x141d70 : word) = Some W_141d2c.
Proof. vm_refl. Qed.
Lemma D_141d2c : decode_any W_141d2c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d30 : bv 32 := 0x02b56663.
Lemma F_141d30 : fetch_word Asan.M.loaded_segments (0x141d74 : word) = Some W_141d30.
Proof. vm_refl. Qed.
Lemma D_141d30 : decode_any W_141d30 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d34 : bv 32 := 0xff010113.
Lemma F_141d34 : fetch_word Asan.M.loaded_segments (0x141d78 : word) = Some W_141d34.
Proof. vm_refl. Qed.
Lemma D_141d34 : decode_any W_141d34 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d38 : bv 32 := 0x00113423.
Lemma F_141d38 : fetch_word Asan.M.loaded_segments (0x141d7c : word) = Some W_141d38.
Proof. vm_refl. Qed.
Lemma D_141d38 : decode_any W_141d38 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d3c : bv 32 := 0x00813023.
Lemma F_141d3c : fetch_word Asan.M.loaded_segments (0x141d80 : word) = Some W_141d3c.
Proof. vm_refl. Qed.
Lemma D_141d3c : decode_any W_141d3c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d40 : bv 32 := 0x40a0043b.
Lemma F_141d40 : fetch_word Asan.M.loaded_segments (0x141d84 : word) = Some W_141d40.
Proof. vm_refl. Qed.
Lemma D_141d40 : decode_any W_141d40 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d44 : bv 32 := 0x8b9ff0ef.
Lemma F_141d44 : fetch_word Asan.M.loaded_segments (0x141d88 : word) = Some W_141d44.
Proof. vm_refl. Qed.
Lemma D_141d44 : decode_any W_141d44 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d48 : bv 32 := 0x00852023.
Lemma F_141d48 : fetch_word Asan.M.loaded_segments (0x141d8c : word) = Some W_141d48.
Proof. vm_refl. Qed.
Lemma D_141d48 : decode_any W_141d48 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d4c : bv 32 := 0xfff00513.
Lemma F_141d4c : fetch_word Asan.M.loaded_segments (0x141d90 : word) = Some W_141d4c.
Proof. vm_refl. Qed.
Lemma D_141d4c : decode_any W_141d4c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d50 : bv 32 := 0x00813083.
Lemma F_141d50 : fetch_word Asan.M.loaded_segments (0x141d94 : word) = Some W_141d50.
Proof. vm_refl. Qed.
Lemma D_141d50 : decode_any W_141d50 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d54 : bv 32 := 0x00013403.
Lemma F_141d54 : fetch_word Asan.M.loaded_segments (0x141d98 : word) = Some W_141d54.
Proof. vm_refl. Qed.
Lemma D_141d54 : decode_any W_141d54 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d58 : bv 32 := 0x01010113.
Lemma F_141d58 : fetch_word Asan.M.loaded_segments (0x141d9c : word) = Some W_141d58.
Proof. vm_refl. Qed.
Lemma D_141d58 : decode_any W_141d58 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d5c : bv 32 := 0x00008067.
Lemma F_141d5c : fetch_word Asan.M.loaded_segments (0x141da0 : word) = Some W_141d5c.
Proof. vm_refl. Qed.
Lemma D_141d5c : decode_any W_141d5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

