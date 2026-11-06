(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99ed0 : bv 32 := 0xfbf5059b.
Lemma F_99ed0 : fetch_word Asan.M.loaded_segments (0x99ed0 : word) = Some W_99ed0.
Proof. vm_refl. Qed.
Lemma D_99ed0 : decode_any W_99ed0 = Some (OpImm32 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ed4 : bv 32 := 0x01a5b593.
Lemma F_99ed4 : fetch_word Asan.M.loaded_segments (0x99ed4 : word) = Some W_99ed4.
Proof. vm_refl. Qed.
Lemma D_99ed4 : decode_any W_99ed4 = Some (OpImm ALU_SLTU 11 11 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ed8 : bv 32 := 0x00559593.
Lemma F_99ed8 : fetch_word Asan.M.loaded_segments (0x99ed8 : word) = Some W_99ed8.
Proof. vm_refl. Qed.
Lemma D_99ed8 : decode_any W_99ed8 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99edc : bv 32 := 0x00b56533.
Lemma F_99edc : fetch_word Asan.M.loaded_segments (0x99edc : word) = Some W_99edc.
Proof. vm_refl. Qed.
Lemma D_99edc : decode_any W_99edc = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ee0 : bv 32 := 0x00008067.
Lemma F_99ee0 : fetch_word Asan.M.loaded_segments (0x99ee0 : word) = Some W_99ee0.
Proof. vm_refl. Qed.
Lemma D_99ee0 : decode_any W_99ee0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a417c : bv 32 := 0x02060063.
Lemma F_a417c : fetch_word Asan.M.loaded_segments (0xa417c : word) = Some W_a417c.
Proof. vm_refl. Qed.
Lemma D_a417c : decode_any W_a417c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4180 : bv 32 := 0x00054683.
Lemma F_a4180 : fetch_word Asan.M.loaded_segments (0xa4180 : word) = Some W_a4180.
Proof. vm_refl. Qed.
Lemma D_a4180 : decode_any W_a4180 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4184 : bv 32 := 0x0005c703.
Lemma F_a4184 : fetch_word Asan.M.loaded_segments (0xa4184 : word) = Some W_a4184.
Proof. vm_refl. Qed.
Lemma D_a4184 : decode_any W_a4184 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4188 : bv 32 := 0x00e69e63.
Lemma F_a4188 : fetch_word Asan.M.loaded_segments (0xa4188 : word) = Some W_a4188.
Proof. vm_refl. Qed.
Lemma D_a4188 : decode_any W_a4188 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a418c : bv 32 := 0xfff60613.
Lemma F_a418c : fetch_word Asan.M.loaded_segments (0xa418c : word) = Some W_a418c.
Proof. vm_refl. Qed.
Lemma D_a418c : decode_any W_a418c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4190 : bv 32 := 0x00150513.
Lemma F_a4190 : fetch_word Asan.M.loaded_segments (0xa4190 : word) = Some W_a4190.
Proof. vm_refl. Qed.
Lemma D_a4190 : decode_any W_a4190 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4194 : bv 32 := 0x00158593.
Lemma F_a4194 : fetch_word Asan.M.loaded_segments (0xa4194 : word) = Some W_a4194.
Proof. vm_refl. Qed.
Lemma D_a4194 : decode_any W_a4194 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4198 : bv 32 := 0xfe0614e3.
Lemma F_a4198 : fetch_word Asan.M.loaded_segments (0xa4198 : word) = Some W_a4198.
Proof. vm_refl. Qed.
Lemma D_a4198 : decode_any W_a4198 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a419c : bv 32 := 0x00000513.
Lemma F_a419c : fetch_word Asan.M.loaded_segments (0xa419c : word) = Some W_a419c.
Proof. vm_refl. Qed.
Lemma D_a419c : decode_any W_a419c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41a0 : bv 32 := 0x00008067.
Lemma F_a41a0 : fetch_word Asan.M.loaded_segments (0xa41a0 : word) = Some W_a41a0.
Proof. vm_refl. Qed.
Lemma D_a41a0 : decode_any W_a41a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41a4 : bv 32 := 0x40e68533.
Lemma F_a41a4 : fetch_word Asan.M.loaded_segments (0xa41a4 : word) = Some W_a41a4.
Proof. vm_refl. Qed.
Lemma D_a41a4 : decode_any W_a41a4 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41a8 : bv 32 := 0x00008067.
Lemma F_a41a8 : fetch_word Asan.M.loaded_segments (0xa41a8 : word) = Some W_a41a8.
Proof. vm_refl. Qed.
Lemma D_a41a8 : decode_any W_a41a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a47fc : bv 32 := 0x00757593.
Lemma F_a47fc : fetch_word Asan.M.loaded_segments (0xa47fc : word) = Some W_a47fc.
Proof. vm_refl. Qed.
Lemma D_a47fc : decode_any W_a47fc = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4800 : bv 32 := 0x00050613.
Lemma F_a4800 : fetch_word Asan.M.loaded_segments (0xa4800 : word) = Some W_a4800.
Proof. vm_refl. Qed.
Lemma D_a4800 : decode_any W_a4800 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4804 : bv 32 := 0x02058a63.
Lemma F_a4804 : fetch_word Asan.M.loaded_segments (0xa4804 : word) = Some W_a4804.
Proof. vm_refl. Qed.
Lemma D_a4804 : decode_any W_a4804 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4808 : bv 32 := 0x00054583.
Lemma F_a4808 : fetch_word Asan.M.loaded_segments (0xa4808 : word) = Some W_a4808.
Proof. vm_refl. Qed.
Lemma D_a4808 : decode_any W_a4808 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a480c : bv 32 := 0x06058c63.
Lemma F_a480c : fetch_word Asan.M.loaded_segments (0xa480c : word) = Some W_a480c.
Proof. vm_refl. Qed.
Lemma D_a480c : decode_any W_a480c = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4810 : bv 32 := 0x00150613.
Lemma F_a4810 : fetch_word Asan.M.loaded_segments (0xa4810 : word) = Some W_a4810.
Proof. vm_refl. Qed.
Lemma D_a4810 : decode_any W_a4810 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4814 : bv 32 := 0x00050593.
Lemma F_a4814 : fetch_word Asan.M.loaded_segments (0xa4814 : word) = Some W_a4814.
Proof. vm_refl. Qed.
Lemma D_a4814 : decode_any W_a4814 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4818 : bv 32 := 0x00158693.
Lemma F_a4818 : fetch_word Asan.M.loaded_segments (0xa4818 : word) = Some W_a4818.
Proof. vm_refl. Qed.
Lemma D_a4818 : decode_any W_a4818 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a481c : bv 32 := 0x0076f693.
Lemma F_a481c : fetch_word Asan.M.loaded_segments (0xa481c : word) = Some W_a481c.
Proof. vm_refl. Qed.
Lemma D_a481c : decode_any W_a481c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4820 : bv 32 := 0x00068c63.
Lemma F_a4820 : fetch_word Asan.M.loaded_segments (0xa4820 : word) = Some W_a4820.
Proof. vm_refl. Qed.
Lemma D_a4820 : decode_any W_a4820 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4824 : bv 32 := 0x00064683.
Lemma F_a4824 : fetch_word Asan.M.loaded_segments (0xa4824 : word) = Some W_a4824.
Proof. vm_refl. Qed.
Lemma D_a4824 : decode_any W_a4824 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4828 : bv 32 := 0x00160613.
Lemma F_a4828 : fetch_word Asan.M.loaded_segments (0xa4828 : word) = Some W_a4828.
Proof. vm_refl. Qed.
Lemma D_a4828 : decode_any W_a4828 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a482c : bv 32 := 0x00158593.
Lemma F_a482c : fetch_word Asan.M.loaded_segments (0xa482c : word) = Some W_a482c.
Proof. vm_refl. Qed.
Lemma D_a482c : decode_any W_a482c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4830 : bv 32 := 0xfe0694e3.
Lemma F_a4830 : fetch_word Asan.M.loaded_segments (0xa4830 : word) = Some W_a4830.
Proof. vm_refl. Qed.
Lemma D_a4830 : decode_any W_a4830 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4834 : bv 32 := 0x0480006f.
Lemma F_a4834 : fetch_word Asan.M.loaded_segments (0xa4834 : word) = Some W_a4834.
Proof. vm_refl. Qed.
Lemma D_a4834 : decode_any W_a4834 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4838 : bv 32 := 0xfff6c597.
Lemma F_a4838 : fetch_word Asan.M.loaded_segments (0xa4838 : word) = Some W_a4838.
Proof. vm_refl. Qed.
Lemma D_a4838 : decode_any W_a4838 = Some (Auipc 11 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a483c : bv 32 := 0xfff6c717.
Lemma F_a483c : fetch_word Asan.M.loaded_segments (0xa483c : word) = Some W_a483c.
Proof. vm_refl. Qed.
Lemma D_a483c : decode_any W_a483c = Some (Auipc 14 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4840 : bv 32 := 0xb485b683.
Lemma F_a4840 : fetch_word Asan.M.loaded_segments (0xa4840 : word) = Some W_a4840.
Proof. vm_refl. Qed.
Lemma D_a4840 : decode_any W_a4840 = Some (Load SZ8 true 13 11 2888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4844 : bv 32 := 0xb2473703.
Lemma F_a4844 : fetch_word Asan.M.loaded_segments (0xa4844 : word) = Some W_a4844.
Proof. vm_refl. Qed.
Lemma D_a4844 : decode_any W_a4844 = Some (Load SZ8 true 14 14 2852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4848 : bv 32 := 0xff760593.
Lemma F_a4848 : fetch_word Asan.M.loaded_segments (0xa4848 : word) = Some W_a4848.
Proof. vm_refl. Qed.
Lemma D_a4848 : decode_any W_a4848 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a484c : bv 32 := 0xff860613.
Lemma F_a484c : fetch_word Asan.M.loaded_segments (0xa484c : word) = Some W_a484c.
Proof. vm_refl. Qed.
Lemma D_a484c : decode_any W_a484c = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4850 : bv 32 := 0x00863783.
Lemma F_a4850 : fetch_word Asan.M.loaded_segments (0xa4850 : word) = Some W_a4850.
Proof. vm_refl. Qed.
Lemma D_a4850 : decode_any W_a4850 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4854 : bv 32 := 0x00860613.
Lemma F_a4854 : fetch_word Asan.M.loaded_segments (0xa4854 : word) = Some W_a4854.
Proof. vm_refl. Qed.
Lemma D_a4854 : decode_any W_a4854 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4858 : bv 32 := 0x40f68833.
Lemma F_a4858 : fetch_word Asan.M.loaded_segments (0xa4858 : word) = Some W_a4858.
Proof. vm_refl. Qed.
Lemma D_a4858 : decode_any W_a4858 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a485c : bv 32 := 0x00f867b3.
Lemma F_a485c : fetch_word Asan.M.loaded_segments (0xa485c : word) = Some W_a485c.
Proof. vm_refl. Qed.
Lemma D_a485c : decode_any W_a485c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4860 : bv 32 := 0x00e7f7b3.
Lemma F_a4860 : fetch_word Asan.M.loaded_segments (0xa4860 : word) = Some W_a4860.
Proof. vm_refl. Qed.
Lemma D_a4860 : decode_any W_a4860 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4864 : bv 32 := 0x00858593.
Lemma F_a4864 : fetch_word Asan.M.loaded_segments (0xa4864 : word) = Some W_a4864.
Proof. vm_refl. Qed.
Lemma D_a4864 : decode_any W_a4864 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4868 : bv 32 := 0xfee784e3.
Lemma F_a4868 : fetch_word Asan.M.loaded_segments (0xa4868 : word) = Some W_a4868.
Proof. vm_refl. Qed.
Lemma D_a4868 : decode_any W_a4868 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a486c : bv 32 := 0x00064683.
Lemma F_a486c : fetch_word Asan.M.loaded_segments (0xa486c : word) = Some W_a486c.
Proof. vm_refl. Qed.
Lemma D_a486c : decode_any W_a486c = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4870 : bv 32 := 0x00160613.
Lemma F_a4870 : fetch_word Asan.M.loaded_segments (0xa4870 : word) = Some W_a4870.
Proof. vm_refl. Qed.
Lemma D_a4870 : decode_any W_a4870 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4874 : bv 32 := 0x00158593.
Lemma F_a4874 : fetch_word Asan.M.loaded_segments (0xa4874 : word) = Some W_a4874.
Proof. vm_refl. Qed.
Lemma D_a4874 : decode_any W_a4874 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4878 : bv 32 := 0xfe069ae3.
Lemma F_a4878 : fetch_word Asan.M.loaded_segments (0xa4878 : word) = Some W_a4878.
Proof. vm_refl. Qed.
Lemma D_a4878 : decode_any W_a4878 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a487c : bv 32 := 0x40a58533.
Lemma F_a487c : fetch_word Asan.M.loaded_segments (0xa487c : word) = Some W_a487c.
Proof. vm_refl. Qed.
Lemma D_a487c : decode_any W_a487c = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4880 : bv 32 := 0x00008067.
Lemma F_a4880 : fetch_word Asan.M.loaded_segments (0xa4880 : word) = Some W_a4880.
Proof. vm_refl. Qed.
Lemma D_a4880 : decode_any W_a4880 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4884 : bv 32 := 0x40a50533.
Lemma F_a4884 : fetch_word Asan.M.loaded_segments (0xa4884 : word) = Some W_a4884.
Proof. vm_refl. Qed.
Lemma D_a4884 : decode_any W_a4884 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4888 : bv 32 := 0x00008067.
Lemma F_a4888 : fetch_word Asan.M.loaded_segments (0xa4888 : word) = Some W_a4888.
Proof. vm_refl. Qed.
Lemma D_a4888 : decode_any W_a4888 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a4900 : bv 32 := 0xff010113.
Lemma F_a4900 : fetch_word Asan.M.loaded_segments (0xa4900 : word) = Some W_a4900.
Proof. vm_refl. Qed.
Lemma D_a4900 : decode_any W_a4900 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4904 : bv 32 := 0x00113423.
Lemma F_a4904 : fetch_word Asan.M.loaded_segments (0xa4904 : word) = Some W_a4904.
Proof. vm_refl. Qed.
Lemma D_a4904 : decode_any W_a4904 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4908 : bv 32 := 0x00813023.
Lemma F_a4908 : fetch_word Asan.M.loaded_segments (0xa4908 : word) = Some W_a4908.
Proof. vm_refl. Qed.
Lemma D_a4908 : decode_any W_a4908 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a490c : bv 32 := 0x00050413.
Lemma F_a490c : fetch_word Asan.M.loaded_segments (0xa490c : word) = Some W_a490c.
Proof. vm_refl. Qed.
Lemma D_a490c : decode_any W_a490c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4910 : bv 32 := 0x018000ef.
Lemma F_a4910 : fetch_word Asan.M.loaded_segments (0xa4910 : word) = Some W_a4910.
Proof. vm_refl. Qed.
Lemma D_a4910 : decode_any W_a4910 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4914 : bv 32 := 0x00040513.
Lemma F_a4914 : fetch_word Asan.M.loaded_segments (0xa4914 : word) = Some W_a4914.
Proof. vm_refl. Qed.
Lemma D_a4914 : decode_any W_a4914 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4918 : bv 32 := 0x00813083.
Lemma F_a4918 : fetch_word Asan.M.loaded_segments (0xa4918 : word) = Some W_a4918.
Proof. vm_refl. Qed.
Lemma D_a4918 : decode_any W_a4918 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a491c : bv 32 := 0x00013403.
Lemma F_a491c : fetch_word Asan.M.loaded_segments (0xa491c : word) = Some W_a491c.
Proof. vm_refl. Qed.
Lemma D_a491c : decode_any W_a491c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4920 : bv 32 := 0x01010113.
Lemma F_a4920 : fetch_word Asan.M.loaded_segments (0xa4920 : word) = Some W_a4920.
Proof. vm_refl. Qed.
Lemma D_a4920 : decode_any W_a4920 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4924 : bv 32 := 0x00008067.
Lemma F_a4924 : fetch_word Asan.M.loaded_segments (0xa4924 : word) = Some W_a4924.
Proof. vm_refl. Qed.
Lemma D_a4924 : decode_any W_a4924 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4928 : bv 32 := 0xff010113.
Lemma F_a4928 : fetch_word Asan.M.loaded_segments (0xa4928 : word) = Some W_a4928.
Proof. vm_refl. Qed.
Lemma D_a4928 : decode_any W_a4928 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a492c : bv 32 := 0x00113423.
Lemma F_a492c : fetch_word Asan.M.loaded_segments (0xa492c : word) = Some W_a492c.
Proof. vm_refl. Qed.
Lemma D_a492c : decode_any W_a492c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4930 : bv 32 := 0x00813023.
Lemma F_a4930 : fetch_word Asan.M.loaded_segments (0xa4930 : word) = Some W_a4930.
Proof. vm_refl. Qed.
Lemma D_a4930 : decode_any W_a4930 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4934 : bv 32 := 0x00050413.
Lemma F_a4934 : fetch_word Asan.M.loaded_segments (0xa4934 : word) = Some W_a4934.
Proof. vm_refl. Qed.
Lemma D_a4934 : decode_any W_a4934 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4938 : bv 32 := 0x00a5c6b3.
Lemma F_a4938 : fetch_word Asan.M.loaded_segments (0xa4938 : word) = Some W_a4938.
Proof. vm_refl. Qed.
Lemma D_a4938 : decode_any W_a4938 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a493c : bv 32 := 0x0076f693.
Lemma F_a493c : fetch_word Asan.M.loaded_segments (0xa493c : word) = Some W_a493c.
Proof. vm_refl. Qed.
Lemma D_a493c : decode_any W_a493c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4940 : bv 32 := 0x02068663.
Lemma F_a4940 : fetch_word Asan.M.loaded_segments (0xa4940 : word) = Some W_a4940.
Proof. vm_refl. Qed.
Lemma D_a4940 : decode_any W_a4940 = Some (Branch BC_EQ 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4944 : bv 32 := 0x0c060263.
Lemma F_a4944 : fetch_word Asan.M.loaded_segments (0xa4944 : word) = Some W_a4944.
Proof. vm_refl. Qed.
Lemma D_a4944 : decode_any W_a4944 = Some (Branch BC_EQ 12 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4948 : bv 32 := 0x00060693.
Lemma F_a4948 : fetch_word Asan.M.loaded_segments (0xa4948 : word) = Some W_a4948.
Proof. vm_refl. Qed.
Lemma D_a4948 : decode_any W_a4948 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a494c : bv 32 := 0x0005c603.
Lemma F_a494c : fetch_word Asan.M.loaded_segments (0xa494c : word) = Some W_a494c.
Proof. vm_refl. Qed.
Lemma D_a494c : decode_any W_a494c = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4950 : bv 32 := 0x00c40023.
Lemma F_a4950 : fetch_word Asan.M.loaded_segments (0xa4950 : word) = Some W_a4950.
Proof. vm_refl. Qed.
Lemma D_a4950 : decode_any W_a4950 = Some (Store SZ1 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4954 : bv 32 := 0x0a060c63.
Lemma F_a4954 : fetch_word Asan.M.loaded_segments (0xa4954 : word) = Some W_a4954.
Proof. vm_refl. Qed.
Lemma D_a4954 : decode_any W_a4954 = Some (Branch BC_EQ 12 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4958 : bv 32 := 0xfff68693.
Lemma F_a4958 : fetch_word Asan.M.loaded_segments (0xa4958 : word) = Some W_a4958.
Proof. vm_refl. Qed.
Lemma D_a4958 : decode_any W_a4958 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a495c : bv 32 := 0x00158593.
Lemma F_a495c : fetch_word Asan.M.loaded_segments (0xa495c : word) = Some W_a495c.
Proof. vm_refl. Qed.
Lemma D_a495c : decode_any W_a495c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4960 : bv 32 := 0x00140413.
Lemma F_a4960 : fetch_word Asan.M.loaded_segments (0xa4960 : word) = Some W_a4960.
Proof. vm_refl. Qed.
Lemma D_a4960 : decode_any W_a4960 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4964 : bv 32 := 0xfe0694e3.
Lemma F_a4964 : fetch_word Asan.M.loaded_segments (0xa4964 : word) = Some W_a4964.
Proof. vm_refl. Qed.
Lemma D_a4964 : decode_any W_a4964 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4968 : bv 32 := 0x0a40006f.
Lemma F_a4968 : fetch_word Asan.M.loaded_segments (0xa4968 : word) = Some W_a4968.
Proof. vm_refl. Qed.
Lemma D_a4968 : decode_any W_a4968 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a496c : bv 32 := 0x0075f693.
Lemma F_a496c : fetch_word Asan.M.loaded_segments (0xa496c : word) = Some W_a496c.
Proof. vm_refl. Qed.
Lemma D_a496c : decode_any W_a496c = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4970 : bv 32 := 0x00c03733.
Lemma F_a4970 : fetch_word Asan.M.loaded_segments (0xa4970 : word) = Some W_a4970.
Proof. vm_refl. Qed.
Lemma D_a4970 : decode_any W_a4970 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4974 : bv 32 := 0x04068063.
Lemma F_a4974 : fetch_word Asan.M.loaded_segments (0xa4974 : word) = Some W_a4974.
Proof. vm_refl. Qed.
Lemma D_a4974 : decode_any W_a4974 = Some (Branch BC_EQ 13 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4978 : bv 32 := 0x02060e63.
Lemma F_a4978 : fetch_word Asan.M.loaded_segments (0xa4978 : word) = Some W_a4978.
Proof. vm_refl. Qed.
Lemma D_a4978 : decode_any W_a4978 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a497c : bv 32 := 0x00158793.
Lemma F_a497c : fetch_word Asan.M.loaded_segments (0xa497c : word) = Some W_a497c.
Proof. vm_refl. Qed.
Lemma D_a497c : decode_any W_a497c = Some (OpImm ALU_ADD 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4980 : bv 32 := 0x00100813.
Lemma F_a4980 : fetch_word Asan.M.loaded_segments (0xa4980 : word) = Some W_a4980.
Proof. vm_refl. Qed.
Lemma D_a4980 : decode_any W_a4980 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4984 : bv 32 := 0x0005c703.
Lemma F_a4984 : fetch_word Asan.M.loaded_segments (0xa4984 : word) = Some W_a4984.
Proof. vm_refl. Qed.
Lemma D_a4984 : decode_any W_a4984 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4988 : bv 32 := 0x00060693.
Lemma F_a4988 : fetch_word Asan.M.loaded_segments (0xa4988 : word) = Some W_a4988.
Proof. vm_refl. Qed.
Lemma D_a4988 : decode_any W_a4988 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a498c : bv 32 := 0x00e40023.
Lemma F_a498c : fetch_word Asan.M.loaded_segments (0xa498c : word) = Some W_a498c.
Proof. vm_refl. Qed.
Lemma D_a498c : decode_any W_a498c = Some (Store SZ1 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4990 : bv 32 := 0x06070e63.
Lemma F_a4990 : fetch_word Asan.M.loaded_segments (0xa4990 : word) = Some W_a4990.
Proof. vm_refl. Qed.
Lemma D_a4990 : decode_any W_a4990 = Some (Branch BC_EQ 14 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4994 : bv 32 := 0xfff68613.
Lemma F_a4994 : fetch_word Asan.M.loaded_segments (0xa4994 : word) = Some W_a4994.
Proof. vm_refl. Qed.
Lemma D_a4994 : decode_any W_a4994 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4998 : bv 32 := 0x00158593.
Lemma F_a4998 : fetch_word Asan.M.loaded_segments (0xa4998 : word) = Some W_a4998.
Proof. vm_refl. Qed.
Lemma D_a4998 : decode_any W_a4998 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a499c : bv 32 := 0x00140413.
Lemma F_a499c : fetch_word Asan.M.loaded_segments (0xa499c : word) = Some W_a499c.
Proof. vm_refl. Qed.
Lemma D_a499c : decode_any W_a499c = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49a0 : bv 32 := 0x0077f893.
Lemma F_a49a0 : fetch_word Asan.M.loaded_segments (0xa49a0 : word) = Some W_a49a0.
Proof. vm_refl. Qed.
Lemma D_a49a0 : decode_any W_a49a0 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49a4 : bv 32 := 0x00c03733.
Lemma F_a49a4 : fetch_word Asan.M.loaded_segments (0xa49a4 : word) = Some W_a49a4.
Proof. vm_refl. Qed.
Lemma D_a49a4 : decode_any W_a49a4 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49a8 : bv 32 := 0x00088663.
Lemma F_a49a8 : fetch_word Asan.M.loaded_segments (0xa49a8 : word) = Some W_a49a8.
Proof. vm_refl. Qed.
Lemma D_a49a8 : decode_any W_a49a8 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49ac : bv 32 := 0x00178793.
Lemma F_a49ac : fetch_word Asan.M.loaded_segments (0xa49ac : word) = Some W_a49ac.
Proof. vm_refl. Qed.
Lemma D_a49ac : decode_any W_a49ac = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49b0 : bv 32 := 0xfd069ae3.
Lemma F_a49b0 : fetch_word Asan.M.loaded_segments (0xa49b0 : word) = Some W_a49b0.
Proof. vm_refl. Qed.
Lemma D_a49b0 : decode_any W_a49b0 = Some (Branch BC_NE 13 16 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49b4 : bv 32 := 0x04070a63.
Lemma F_a49b4 : fetch_word Asan.M.loaded_segments (0xa49b4 : word) = Some W_a49b4.
Proof. vm_refl. Qed.
Lemma D_a49b4 : decode_any W_a49b4 = Some (Branch BC_EQ 14 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49b8 : bv 32 := 0x0005c683.
Lemma F_a49b8 : fetch_word Asan.M.loaded_segments (0xa49b8 : word) = Some W_a49b8.
Proof. vm_refl. Qed.
Lemma D_a49b8 : decode_any W_a49b8 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49bc : bv 32 := 0x06068a63.
Lemma F_a49bc : fetch_word Asan.M.loaded_segments (0xa49bc : word) = Some W_a49bc.
Proof. vm_refl. Qed.
Lemma D_a49bc : decode_any W_a49bc = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49c0 : bv 32 := 0x00800693.
Lemma F_a49c0 : fetch_word Asan.M.loaded_segments (0xa49c0 : word) = Some W_a49c0.
Proof. vm_refl. Qed.
Lemma D_a49c0 : decode_any W_a49c0 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49c4 : bv 32 := 0xf8d660e3.
Lemma F_a49c4 : fetch_word Asan.M.loaded_segments (0xa49c4 : word) = Some W_a49c4.
Proof. vm_refl. Qed.
Lemma D_a49c4 : decode_any W_a49c4 = Some (Branch BC_LTU 12 13 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49c8 : bv 32 := 0xfff6c697.
Lemma F_a49c8 : fetch_word Asan.M.loaded_segments (0xa49c8 : word) = Some W_a49c8.
Proof. vm_refl. Qed.
Lemma D_a49c8 : decode_any W_a49c8 = Some (Auipc 13 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49cc : bv 32 := 0xfff6c717.
Lemma F_a49cc : fetch_word Asan.M.loaded_segments (0xa49cc : word) = Some W_a49cc.
Proof. vm_refl. Qed.
Lemma D_a49cc : decode_any W_a49cc = Some (Auipc 14 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49d0 : bv 32 := 0x9b86b683.
Lemma F_a49d0 : fetch_word Asan.M.loaded_segments (0xa49d0 : word) = Some W_a49d0.
Proof. vm_refl. Qed.
Lemma D_a49d0 : decode_any W_a49d0 = Some (Load SZ8 true 13 13 2488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49d4 : bv 32 := 0x99473703.
Lemma F_a49d4 : fetch_word Asan.M.loaded_segments (0xa49d4 : word) = Some W_a49d4.
Proof. vm_refl. Qed.
Lemma D_a49d4 : decode_any W_a49d4 = Some (Load SZ8 true 14 14 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49d8 : bv 32 := 0x00700793.
Lemma F_a49d8 : fetch_word Asan.M.loaded_segments (0xa49d8 : word) = Some W_a49d8.
Proof. vm_refl. Qed.
Lemma D_a49d8 : decode_any W_a49d8 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49dc : bv 32 := 0x0005b803.
Lemma F_a49dc : fetch_word Asan.M.loaded_segments (0xa49dc : word) = Some W_a49dc.
Proof. vm_refl. Qed.
Lemma D_a49dc : decode_any W_a49dc = Some (Load SZ8 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49e0 : bv 32 := 0x410688b3.
Lemma F_a49e0 : fetch_word Asan.M.loaded_segments (0xa49e0 : word) = Some W_a49e0.
Proof. vm_refl. Qed.
Lemma D_a49e0 : decode_any W_a49e0 = Some (Op ALU_SUB 17 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49e4 : bv 32 := 0x0108e8b3.
Lemma F_a49e4 : fetch_word Asan.M.loaded_segments (0xa49e4 : word) = Some W_a49e4.
Proof. vm_refl. Qed.
Lemma D_a49e4 : decode_any W_a49e4 = Some (Op ALU_OR 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49e8 : bv 32 := 0x00e8f8b3.
Lemma F_a49e8 : fetch_word Asan.M.loaded_segments (0xa49e8 : word) = Some W_a49e8.
Proof. vm_refl. Qed.
Lemma D_a49e8 : decode_any W_a49e8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49ec : bv 32 := 0xf4e89ee3.
Lemma F_a49ec : fetch_word Asan.M.loaded_segments (0xa49ec : word) = Some W_a49ec.
Proof. vm_refl. Qed.
Lemma D_a49ec : decode_any W_a49ec = Some (Branch BC_NE 17 14 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49f0 : bv 32 := 0x01043023.
Lemma F_a49f0 : fetch_word Asan.M.loaded_segments (0xa49f0 : word) = Some W_a49f0.
Proof. vm_refl. Qed.
Lemma D_a49f0 : decode_any W_a49f0 = Some (Store SZ8 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49f4 : bv 32 := 0xff860613.
Lemma F_a49f4 : fetch_word Asan.M.loaded_segments (0xa49f4 : word) = Some W_a49f4.
Proof. vm_refl. Qed.
Lemma D_a49f4 : decode_any W_a49f4 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49f8 : bv 32 := 0x00858593.
Lemma F_a49f8 : fetch_word Asan.M.loaded_segments (0xa49f8 : word) = Some W_a49f8.
Proof. vm_refl. Qed.
Lemma D_a49f8 : decode_any W_a49f8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a49fc : bv 32 := 0x00840413.
Lemma F_a49fc : fetch_word Asan.M.loaded_segments (0xa49fc : word) = Some W_a49fc.
Proof. vm_refl. Qed.
Lemma D_a49fc : decode_any W_a49fc = Some (OpImm ALU_ADD 8 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a00 : bv 32 := 0xfcc7eee3.
Lemma F_a4a00 : fetch_word Asan.M.loaded_segments (0xa4a00 : word) = Some W_a4a00.
Proof. vm_refl. Qed.
Lemma D_a4a00 : decode_any W_a4a00 = Some (Branch BC_LTU 15 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a04 : bv 32 := 0xf41ff06f.
Lemma F_a4a04 : fetch_word Asan.M.loaded_segments (0xa4a04 : word) = Some W_a4a04.
Proof. vm_refl. Qed.
Lemma D_a4a04 : decode_any W_a4a04 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a08 : bv 32 := 0x00000693.
Lemma F_a4a08 : fetch_word Asan.M.loaded_segments (0xa4a08 : word) = Some W_a4a08.
Proof. vm_refl. Qed.
Lemma D_a4a08 : decode_any W_a4a08 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a0c : bv 32 := 0x00040513.
Lemma F_a4a0c : fetch_word Asan.M.loaded_segments (0xa4a0c : word) = Some W_a4a0c.
Proof. vm_refl. Qed.
Lemma D_a4a0c : decode_any W_a4a0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a10 : bv 32 := 0x00000593.
Lemma F_a4a10 : fetch_word Asan.M.loaded_segments (0xa4a10 : word) = Some W_a4a10.
Proof. vm_refl. Qed.
Lemma D_a4a10 : decode_any W_a4a10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a14 : bv 32 := 0x00068613.
Lemma F_a4a14 : fetch_word Asan.M.loaded_segments (0xa4a14 : word) = Some W_a4a14.
Proof. vm_refl. Qed.
Lemma D_a4a14 : decode_any W_a4a14 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a18 : bv 32 := 0xc10af0ef.
Lemma F_a4a18 : fetch_word Asan.M.loaded_segments (0xa4a18 : word) = Some W_a4a18.
Proof. vm_refl. Qed.
Lemma D_a4a18 : decode_any W_a4a18 = Some (Jal 1 1766416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a1c : bv 32 := 0x00040513.
Lemma F_a4a1c : fetch_word Asan.M.loaded_segments (0xa4a1c : word) = Some W_a4a1c.
Proof. vm_refl. Qed.
Lemma D_a4a1c : decode_any W_a4a1c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a20 : bv 32 := 0x00813083.
Lemma F_a4a20 : fetch_word Asan.M.loaded_segments (0xa4a20 : word) = Some W_a4a20.
Proof. vm_refl. Qed.
Lemma D_a4a20 : decode_any W_a4a20 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a24 : bv 32 := 0x00013403.
Lemma F_a4a24 : fetch_word Asan.M.loaded_segments (0xa4a24 : word) = Some W_a4a24.
Proof. vm_refl. Qed.
Lemma D_a4a24 : decode_any W_a4a24 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a28 : bv 32 := 0x01010113.
Lemma F_a4a28 : fetch_word Asan.M.loaded_segments (0xa4a28 : word) = Some W_a4a28.
Proof. vm_refl. Qed.
Lemma D_a4a28 : decode_any W_a4a28 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a2c : bv 32 := 0x00008067.
Lemma F_a4a2c : fetch_word Asan.M.loaded_segments (0xa4a2c : word) = Some W_a4a2c.
Proof. vm_refl. Qed.
Lemma D_a4a2c : decode_any W_a4a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a30 : bv 32 := 0x00060693.
Lemma F_a4a30 : fetch_word Asan.M.loaded_segments (0xa4a30 : word) = Some W_a4a30.
Proof. vm_refl. Qed.
Lemma D_a4a30 : decode_any W_a4a30 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a34 : bv 32 := 0xfd9ff06f.
Lemma F_a4a34 : fetch_word Asan.M.loaded_segments (0xa4a34 : word) = Some W_a4a34.
Proof. vm_refl. Qed.
Lemma D_a4a34 : decode_any W_a4a34 = Some (Jal 0 2097112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a38 : bv 32 := 0xfe010113.
Lemma F_a4a38 : fetch_word Asan.M.loaded_segments (0xa4a38 : word) = Some W_a4a38.
Proof. vm_refl. Qed.
Lemma D_a4a38 : decode_any W_a4a38 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a3c : bv 32 := 0x00113c23.
Lemma F_a4a3c : fetch_word Asan.M.loaded_segments (0xa4a3c : word) = Some W_a4a3c.
Proof. vm_refl. Qed.
Lemma D_a4a3c : decode_any W_a4a3c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a40 : bv 32 := 0x00813823.
Lemma F_a4a40 : fetch_word Asan.M.loaded_segments (0xa4a40 : word) = Some W_a4a40.
Proof. vm_refl. Qed.
Lemma D_a4a40 : decode_any W_a4a40 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a44 : bv 32 := 0x00913423.
Lemma F_a4a44 : fetch_word Asan.M.loaded_segments (0xa4a44 : word) = Some W_a4a44.
Proof. vm_refl. Qed.
Lemma D_a4a44 : decode_any W_a4a44 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a48 : bv 32 := 0x00058413.
Lemma F_a4a48 : fetch_word Asan.M.loaded_segments (0xa4a48 : word) = Some W_a4a48.
Proof. vm_refl. Qed.
Lemma D_a4a48 : decode_any W_a4a48 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a4c : bv 32 := 0x00050493.
Lemma F_a4a4c : fetch_word Asan.M.loaded_segments (0xa4a4c : word) = Some W_a4a4c.
Proof. vm_refl. Qed.
Lemma D_a4a4c : decode_any W_a4a4c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a50 : bv 32 := 0x00000593.
Lemma F_a4a50 : fetch_word Asan.M.loaded_segments (0xa4a50 : word) = Some W_a4a50.
Proof. vm_refl. Qed.
Lemma D_a4a50 : decode_any W_a4a50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a54 : bv 32 := 0x00040613.
Lemma F_a4a54 : fetch_word Asan.M.loaded_segments (0xa4a54 : word) = Some W_a4a54.
Proof. vm_refl. Qed.
Lemma D_a4a54 : decode_any W_a4a54 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a58 : bv 32 := 0xff09f0ef.
Lemma F_a4a58 : fetch_word Asan.M.loaded_segments (0xa4a58 : word) = Some W_a4a58.
Proof. vm_refl. Qed.
Lemma D_a4a58 : decode_any W_a4a58 = Some (Jal 1 1701872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a5c : bv 32 := 0x00050463.
Lemma F_a4a5c : fetch_word Asan.M.loaded_segments (0xa4a5c : word) = Some W_a4a5c.
Proof. vm_refl. Qed.
Lemma D_a4a5c : decode_any W_a4a5c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a60 : bv 32 := 0x40950433.
Lemma F_a4a60 : fetch_word Asan.M.loaded_segments (0xa4a60 : word) = Some W_a4a60.
Proof. vm_refl. Qed.
Lemma D_a4a60 : decode_any W_a4a60 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a64 : bv 32 := 0x00040513.
Lemma F_a4a64 : fetch_word Asan.M.loaded_segments (0xa4a64 : word) = Some W_a4a64.
Proof. vm_refl. Qed.
Lemma D_a4a64 : decode_any W_a4a64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a68 : bv 32 := 0x01813083.
Lemma F_a4a68 : fetch_word Asan.M.loaded_segments (0xa4a68 : word) = Some W_a4a68.
Proof. vm_refl. Qed.
Lemma D_a4a68 : decode_any W_a4a68 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a6c : bv 32 := 0x01013403.
Lemma F_a4a6c : fetch_word Asan.M.loaded_segments (0xa4a6c : word) = Some W_a4a6c.
Proof. vm_refl. Qed.
Lemma D_a4a6c : decode_any W_a4a6c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a70 : bv 32 := 0x00813483.
Lemma F_a4a70 : fetch_word Asan.M.loaded_segments (0xa4a70 : word) = Some W_a4a70.
Proof. vm_refl. Qed.
Lemma D_a4a70 : decode_any W_a4a70 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a74 : bv 32 := 0x02010113.
Lemma F_a4a74 : fetch_word Asan.M.loaded_segments (0xa4a74 : word) = Some W_a4a74.
Proof. vm_refl. Qed.
Lemma D_a4a74 : decode_any W_a4a74 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a78 : bv 32 := 0x00008067.
Lemma F_a4a78 : fetch_word Asan.M.loaded_segments (0xa4a78 : word) = Some W_a4a78.
Proof. vm_refl. Qed.
Lemma D_a4a78 : decode_any W_a4a78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
