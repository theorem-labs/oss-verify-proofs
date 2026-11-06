(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_20068 : bv 32 := 0xff010113.
Lemma F_20068 : fetch_word Plain.M.loaded_segments (0x20068 : word) = Some W_20068.
Proof. vm_refl. Qed.
Lemma D_20068 : decode_any W_20068 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2006c : bv 32 := 0x00113423.
Lemma F_2006c : fetch_word Plain.M.loaded_segments (0x2006c : word) = Some W_2006c.
Proof. vm_refl. Qed.
Lemma D_2006c : decode_any W_2006c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20070 : bv 32 := 0x00813023.
Lemma F_20070 : fetch_word Plain.M.loaded_segments (0x20070 : word) = Some W_20070.
Proof. vm_refl. Qed.
Lemma D_20070 : decode_any W_20070 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20074 : bv 32 := 0x01010413.
Lemma F_20074 : fetch_word Plain.M.loaded_segments (0x20074 : word) = Some W_20074.
Proof. vm_refl. Qed.
Lemma D_20074 : decode_any W_20074 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20078 : bv 32 := 0x00040517.
Lemma F_20078 : fetch_word Plain.M.loaded_segments (0x20078 : word) = Some W_20078.
Proof. vm_refl. Qed.
Lemma D_20078 : decode_any W_20078 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_2007c : bv 32 := 0x84050513.
Lemma F_2007c : fetch_word Plain.M.loaded_segments (0x2007c : word) = Some W_2007c.
Proof. vm_refl. Qed.
Lemma D_2007c : decode_any W_2007c = Some (OpImm ALU_ADD 10 10 2112, 4%Z).
Proof. vm_refl. Qed.

Definition W_20080 : bv 32 := 0x00054503.
Lemma F_20080 : fetch_word Plain.M.loaded_segments (0x20080 : word) = Some W_20080.
Proof. vm_refl. Qed.
Lemma D_20080 : decode_any W_20080 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20084 : bv 32 := 0x00157513.
Lemma F_20084 : fetch_word Plain.M.loaded_segments (0x20084 : word) = Some W_20084.
Proof. vm_refl. Qed.
Lemma D_20084 : decode_any W_20084 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20088 : bv 32 := 0x00050663.
Lemma F_20088 : fetch_word Plain.M.loaded_segments (0x20088 : word) = Some W_20088.
Proof. vm_refl. Qed.
Lemma D_20088 : decode_any W_20088 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20094 : bv 32 := 0x00040517.
Lemma F_20094 : fetch_word Plain.M.loaded_segments (0x20094 : word) = Some W_20094.
Proof. vm_refl. Qed.
Lemma D_20094 : decode_any W_20094 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_20098 : bv 32 := 0x82450593.
Lemma F_20098 : fetch_word Plain.M.loaded_segments (0x20098 : word) = Some W_20098.
Proof. vm_refl. Qed.
Lemma D_20098 : decode_any W_20098 = Some (OpImm ALU_ADD 11 10 2084, 4%Z).
Proof. vm_refl. Qed.

Definition W_2009c : bv 32 := 0x00100513.
Lemma F_2009c : fetch_word Plain.M.loaded_segments (0x2009c : word) = Some W_2009c.
Proof. vm_refl. Qed.
Lemma D_2009c : decode_any W_2009c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_200a0 : bv 32 := 0x00a58023.
Lemma F_200a0 : fetch_word Plain.M.loaded_segments (0x200a0 : word) = Some W_200a0.
Proof. vm_refl. Qed.
Lemma D_200a0 : decode_any W_200a0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_200a4 : bv 32 := 0x0003e517.
Lemma F_200a4 : fetch_word Plain.M.loaded_segments (0x200a4 : word) = Some W_200a4.
Proof. vm_refl. Qed.
Lemma D_200a4 : decode_any W_200a4 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_200a8 : bv 32 := 0x42453503.
Lemma F_200a8 : fetch_word Plain.M.loaded_segments (0x200a8 : word) = Some W_200a8.
Proof. vm_refl. Qed.
Lemma D_200a8 : decode_any W_200a8 = Some (Load SZ8 true 10 10 1060, 4%Z).
Proof. vm_refl. Qed.

Definition W_200ac : bv 32 := 0x00050e63.
Lemma F_200ac : fetch_word Plain.M.loaded_segments (0x200ac : word) = Some W_200ac.
Proof. vm_refl. Qed.
Lemma D_200ac : decode_any W_200ac = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_200b0 : bv 32 := 0x0040006f.
Lemma F_200b0 : fetch_word Plain.M.loaded_segments (0x200b0 : word) = Some W_200b0.
Proof. vm_refl. Qed.
Lemma D_200b0 : decode_any W_200b0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_200b4 : bv 32 := 0x0003f517.
Lemma F_200b4 : fetch_word Plain.M.loaded_segments (0x200b4 : word) = Some W_200b4.
Proof. vm_refl. Qed.
Lemma D_200b4 : decode_any W_200b4 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_200b8 : bv 32 := 0x55450513.
Lemma F_200b8 : fetch_word Plain.M.loaded_segments (0x200b8 : word) = Some W_200b8.
Proof. vm_refl. Qed.
Lemma D_200b8 : decode_any W_200b8 = Some (OpImm ALU_ADD 10 10 1364, 4%Z).
Proof. vm_refl. Qed.

Definition W_200bc : bv 32 := 0x00053503.
Lemma F_200bc : fetch_word Plain.M.loaded_segments (0x200bc : word) = Some W_200bc.
Proof. vm_refl. Qed.
Lemma D_200bc : decode_any W_200bc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_200c0 : bv 32 := 0x2802b0ef.
Lemma F_200c0 : fetch_word Plain.M.loaded_segments (0x200c0 : word) = Some W_200c0.
Proof. vm_refl. Qed.
Lemma D_200c0 : decode_any W_200c0 = Some (Jal 1 176768, 4%Z).
Proof. vm_refl. Qed.

Definition W_200c4 : bv 32 := 0x0040006f.
Lemma F_200c4 : fetch_word Plain.M.loaded_segments (0x200c4 : word) = Some W_200c4.
Proof. vm_refl. Qed.
Lemma D_200c4 : decode_any W_200c4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_200c8 : bv 32 := 0x0003e517.
Lemma F_200c8 : fetch_word Plain.M.loaded_segments (0x200c8 : word) = Some W_200c8.
Proof. vm_refl. Qed.
Lemma D_200c8 : decode_any W_200c8 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_200cc : bv 32 := 0x40853503.
Lemma F_200cc : fetch_word Plain.M.loaded_segments (0x200cc : word) = Some W_200cc.
Proof. vm_refl. Qed.
Lemma D_200cc : decode_any W_200cc = Some (Load SZ8 true 10 10 1032, 4%Z).
Proof. vm_refl. Qed.

Definition W_200d0 : bv 32 := 0x00050c63.
Lemma F_200d0 : fetch_word Plain.M.loaded_segments (0x200d0 : word) = Some W_200d0.
Proof. vm_refl. Qed.
Lemma D_200d0 : decode_any W_200d0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_200e8 : bv 32 := 0x00813083.
Lemma F_200e8 : fetch_word Plain.M.loaded_segments (0x200e8 : word) = Some W_200e8.
Proof. vm_refl. Qed.
Lemma D_200e8 : decode_any W_200e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_200ec : bv 32 := 0x00013403.
Lemma F_200ec : fetch_word Plain.M.loaded_segments (0x200ec : word) = Some W_200ec.
Proof. vm_refl. Qed.
Lemma D_200ec : decode_any W_200ec = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_200f0 : bv 32 := 0x01010113.
Lemma F_200f0 : fetch_word Plain.M.loaded_segments (0x200f0 : word) = Some W_200f0.
Proof. vm_refl. Qed.
Lemma D_200f0 : decode_any W_200f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_200f4 : bv 32 := 0x00008067.
Lemma F_200f4 : fetch_word Plain.M.loaded_segments (0x200f4 : word) = Some W_200f4.
Proof. vm_refl. Qed.
Lemma D_200f4 : decode_any W_200f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20520 : bv 32 := 0x0004f517.
Lemma F_20520 : fetch_word Plain.M.loaded_segments (0x20520 : word) = Some W_20520.
Proof. vm_refl. Qed.
Lemma D_20520 : decode_any W_20520 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_20524 : bv 32 := 0x3a454503.
Lemma F_20524 : fetch_word Plain.M.loaded_segments (0x20524 : word) = Some W_20524.
Proof. vm_refl. Qed.
Lemma D_20524 : decode_any W_20524 = Some (Load SZ1 false 10 10 932, 4%Z).
Proof. vm_refl. Qed.

Definition W_20528 : bv 32 := 0x00051463.
Lemma F_20528 : fetch_word Plain.M.loaded_segments (0x20528 : word) = Some W_20528.
Proof. vm_refl. Qed.
Lemma D_20528 : decode_any W_20528 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2052c : bv 32 := 0x00008067.
Lemma F_2052c : fetch_word Plain.M.loaded_segments (0x2052c : word) = Some W_2052c.
Proof. vm_refl. Qed.
Lemma D_2052c : decode_any W_2052c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b278 : bv 32 := 0xfd010113.
Lemma F_4b278 : fetch_word Plain.M.loaded_segments (0x4b278 : word) = Some W_4b278.
Proof. vm_refl. Qed.
Lemma D_4b278 : decode_any W_4b278 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b27c : bv 32 := 0x02113423.
Lemma F_4b27c : fetch_word Plain.M.loaded_segments (0x4b27c : word) = Some W_4b27c.
Proof. vm_refl. Qed.
Lemma D_4b27c : decode_any W_4b27c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b280 : bv 32 := 0x02813023.
Lemma F_4b280 : fetch_word Plain.M.loaded_segments (0x4b280 : word) = Some W_4b280.
Proof. vm_refl. Qed.
Lemma D_4b280 : decode_any W_4b280 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b284 : bv 32 := 0x00913c23.
Lemma F_4b284 : fetch_word Plain.M.loaded_segments (0x4b284 : word) = Some W_4b284.
Proof. vm_refl. Qed.
Lemma D_4b284 : decode_any W_4b284 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b288 : bv 32 := 0x01213823.
Lemma F_4b288 : fetch_word Plain.M.loaded_segments (0x4b288 : word) = Some W_4b288.
Proof. vm_refl. Qed.
Lemma D_4b288 : decode_any W_4b288 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b28c : bv 32 := 0x01313423.
Lemma F_4b28c : fetch_word Plain.M.loaded_segments (0x4b28c : word) = Some W_4b28c.
Proof. vm_refl. Qed.
Lemma D_4b28c : decode_any W_4b28c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b290 : bv 32 := 0x00045517.
Lemma F_4b290 : fetch_word Plain.M.loaded_segments (0x4b290 : word) = Some W_4b290.
Proof. vm_refl. Qed.
Lemma D_4b290 : decode_any W_4b290 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b294 : bv 32 := 0x1f050913.
Lemma F_4b294 : fetch_word Plain.M.loaded_segments (0x4b294 : word) = Some W_4b294.
Proof. vm_refl. Qed.
Lemma D_4b294 : decode_any W_4b294 = Some (OpImm ALU_ADD 18 10 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b298 : bv 32 := 0x00490413.
Lemma F_4b298 : fetch_word Plain.M.loaded_segments (0x4b298 : word) = Some W_4b298.
Proof. vm_refl. Qed.
Lemma D_4b298 : decode_any W_4b298 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b29c : bv 32 := 0x00040513.
Lemma F_4b29c : fetch_word Plain.M.loaded_segments (0x4b29c : word) = Some W_4b29c.
Proof. vm_refl. Qed.
Lemma D_4b29c : decode_any W_4b29c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2a0 : bv 32 := 0x7890d0ef.
Lemma F_4b2a0 : fetch_word Plain.M.loaded_segments (0x4b2a0 : word) = Some W_4b2a0.
Proof. vm_refl. Qed.
Lemma D_4b2a0 : decode_any W_4b2a0 = Some (Jal 1 57224, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2a4 : bv 32 := 0x01093503.
Lemma F_4b2a4 : fetch_word Plain.M.loaded_segments (0x4b2a4 : word) = Some W_4b2a4.
Proof. vm_refl. Qed.
Lemma D_4b2a4 : decode_any W_4b2a4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2a8 : bv 32 := 0x06050863.
Lemma F_4b2a8 : fetch_word Plain.M.loaded_segments (0x4b2a8 : word) = Some W_4b2a8.
Proof. vm_refl. Qed.
Lemma D_4b2a8 : decode_any W_4b2a8 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2ac : bv 32 := 0x00892583.
Lemma F_4b2ac : fetch_word Plain.M.loaded_segments (0x4b2ac : word) = Some W_4b2ac.
Proof. vm_refl. Qed.
Lemma D_4b2ac : decode_any W_4b2ac = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2b0 : bv 32 := 0x0180006f.
Lemma F_4b2b0 : fetch_word Plain.M.loaded_segments (0x4b2b0 : word) = Some W_4b2b0.
Proof. vm_refl. Qed.
Lemma D_4b2b0 : decode_any W_4b2b0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2b4 : bv 32 := 0x00053503.
Lemma F_4b2b4 : fetch_word Plain.M.loaded_segments (0x4b2b4 : word) = Some W_4b2b4.
Proof. vm_refl. Qed.
Lemma D_4b2b4 : decode_any W_4b2b4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2b8 : bv 32 := 0x02000593.
Lemma F_4b2b8 : fetch_word Plain.M.loaded_segments (0x4b2b8 : word) = Some W_4b2b8.
Proof. vm_refl. Qed.
Lemma D_4b2b8 : decode_any W_4b2b8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2bc : bv 32 := 0x00b92423.
Lemma F_4b2bc : fetch_word Plain.M.loaded_segments (0x4b2bc : word) = Some W_4b2bc.
Proof. vm_refl. Qed.
Lemma D_4b2bc : decode_any W_4b2bc = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2c0 : bv 32 := 0x00a93823.
Lemma F_4b2c0 : fetch_word Plain.M.loaded_segments (0x4b2c0 : word) = Some W_4b2c0.
Proof. vm_refl. Qed.
Lemma D_4b2c0 : decode_any W_4b2c0 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2c4 : bv 32 := 0x04050a63.
Lemma F_4b2c4 : fetch_word Plain.M.loaded_segments (0x4b2c4 : word) = Some W_4b2c4.
Proof. vm_refl. Qed.
Lemma D_4b2c4 : decode_any W_4b2c4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2c8 : bv 32 := 0xfff5861b.
Lemma F_4b2c8 : fetch_word Plain.M.loaded_segments (0x4b2c8 : word) = Some W_4b2c8.
Proof. vm_refl. Qed.
Lemma D_4b2c8 : decode_any W_4b2c8 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2cc : bv 32 := 0x00c92423.
Lemma F_4b2cc : fetch_word Plain.M.loaded_segments (0x4b2cc : word) = Some W_4b2cc.
Proof. vm_refl. Qed.
Lemma D_4b2cc : decode_any W_4b2cc = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2d0 : bv 32 := 0xfeb052e3.
Lemma F_4b2d0 : fetch_word Plain.M.loaded_segments (0x4b2d0 : word) = Some W_4b2d0.
Proof. vm_refl. Qed.
Lemma D_4b2d0 : decode_any W_4b2d0 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2d4 : bv 32 := 0x01093503.
Lemma F_4b2d4 : fetch_word Plain.M.loaded_segments (0x4b2d4 : word) = Some W_4b2d4.
Proof. vm_refl. Qed.
Lemma D_4b2d4 : decode_any W_4b2d4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2d8 : bv 32 := 0x00361613.
Lemma F_4b2d8 : fetch_word Plain.M.loaded_segments (0x4b2d8 : word) = Some W_4b2d8.
Proof. vm_refl. Qed.
Lemma D_4b2d8 : decode_any W_4b2d8 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2dc : bv 32 := 0x00c50533.
Lemma F_4b2dc : fetch_word Plain.M.loaded_segments (0x4b2dc : word) = Some W_4b2dc.
Proof. vm_refl. Qed.
Lemma D_4b2dc : decode_any W_4b2dc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2e0 : bv 32 := 0x00853983.
Lemma F_4b2e0 : fetch_word Plain.M.loaded_segments (0x4b2e0 : word) = Some W_4b2e0.
Proof. vm_refl. Qed.
Lemma D_4b2e0 : decode_any W_4b2e0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2e4 : bv 32 := 0x10853483.
Lemma F_4b2e4 : fetch_word Plain.M.loaded_segments (0x4b2e4 : word) = Some W_4b2e4.
Proof. vm_refl. Qed.
Lemma D_4b2e4 : decode_any W_4b2e4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2e8 : bv 32 := 0x00040513.
Lemma F_4b2e8 : fetch_word Plain.M.loaded_segments (0x4b2e8 : word) = Some W_4b2e8.
Proof. vm_refl. Qed.
Lemma D_4b2e8 : decode_any W_4b2e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2ec : bv 32 := 0x1c40e0ef.
Lemma F_4b2ec : fetch_word Plain.M.loaded_segments (0x4b2ec : word) = Some W_4b2ec.
Proof. vm_refl. Qed.
Lemma D_4b2ec : decode_any W_4b2ec = Some (Jal 1 57796, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2f0 : bv 32 := 0x00048513.
Lemma F_4b2f0 : fetch_word Plain.M.loaded_segments (0x4b2f0 : word) = Some W_4b2f0.
Proof. vm_refl. Qed.
Lemma D_4b2f0 : decode_any W_4b2f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2f4 : bv 32 := 0x000980e7.
Lemma F_4b2f4 : fetch_word Plain.M.loaded_segments (0x4b2f4 : word) = Some W_4b2f4.
Proof. vm_refl. Qed.
Lemma D_4b2f4 : decode_any W_4b2f4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2f8 : bv 32 := 0x00040513.
Lemma F_4b2f8 : fetch_word Plain.M.loaded_segments (0x4b2f8 : word) = Some W_4b2f8.
Proof. vm_refl. Qed.
Lemma D_4b2f8 : decode_any W_4b2f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b2fc : bv 32 := 0x72d0d0ef.
Lemma F_4b2fc : fetch_word Plain.M.loaded_segments (0x4b2fc : word) = Some W_4b2fc.
Proof. vm_refl. Qed.
Lemma D_4b2fc : decode_any W_4b2fc = Some (Jal 1 57132, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b300 : bv 32 := 0x00892503.
Lemma F_4b300 : fetch_word Plain.M.loaded_segments (0x4b300 : word) = Some W_4b300.
Proof. vm_refl. Qed.
Lemma D_4b300 : decode_any W_4b300 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b304 : bv 32 := 0xfff5061b.
Lemma F_4b304 : fetch_word Plain.M.loaded_segments (0x4b304 : word) = Some W_4b304.
Proof. vm_refl. Qed.
Lemma D_4b304 : decode_any W_4b304 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b308 : bv 32 := 0x00c92423.
Lemma F_4b308 : fetch_word Plain.M.loaded_segments (0x4b308 : word) = Some W_4b308.
Proof. vm_refl. Qed.
Lemma D_4b308 : decode_any W_4b308 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b30c : bv 32 := 0xfca044e3.
Lemma F_4b30c : fetch_word Plain.M.loaded_segments (0x4b30c : word) = Some W_4b30c.
Proof. vm_refl. Qed.
Lemma D_4b30c : decode_any W_4b30c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b310 : bv 32 := 0x01093503.
Lemma F_4b310 : fetch_word Plain.M.loaded_segments (0x4b310 : word) = Some W_4b310.
Proof. vm_refl. Qed.
Lemma D_4b310 : decode_any W_4b310 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b314 : bv 32 := 0xfa1ff06f.
Lemma F_4b314 : fetch_word Plain.M.loaded_segments (0x4b314 : word) = Some W_4b314.
Proof. vm_refl. Qed.
Lemma D_4b314 : decode_any W_4b314 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b318 : bv 32 := 0x00100513.
Lemma F_4b318 : fetch_word Plain.M.loaded_segments (0x4b318 : word) = Some W_4b318.
Proof. vm_refl. Qed.
Lemma D_4b318 : decode_any W_4b318 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b31c : bv 32 := 0x00a90023.
Lemma F_4b31c : fetch_word Plain.M.loaded_segments (0x4b31c : word) = Some W_4b31c.
Proof. vm_refl. Qed.
Lemma D_4b31c : decode_any W_4b31c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b320 : bv 32 := 0x00040513.
Lemma F_4b320 : fetch_word Plain.M.loaded_segments (0x4b320 : word) = Some W_4b320.
Proof. vm_refl. Qed.
Lemma D_4b320 : decode_any W_4b320 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b324 : bv 32 := 0x02813083.
Lemma F_4b324 : fetch_word Plain.M.loaded_segments (0x4b324 : word) = Some W_4b324.
Proof. vm_refl. Qed.
Lemma D_4b324 : decode_any W_4b324 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b328 : bv 32 := 0x02013403.
Lemma F_4b328 : fetch_word Plain.M.loaded_segments (0x4b328 : word) = Some W_4b328.
Proof. vm_refl. Qed.
Lemma D_4b328 : decode_any W_4b328 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b32c : bv 32 := 0x01813483.
Lemma F_4b32c : fetch_word Plain.M.loaded_segments (0x4b32c : word) = Some W_4b32c.
Proof. vm_refl. Qed.
Lemma D_4b32c : decode_any W_4b32c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b330 : bv 32 := 0x01013903.
Lemma F_4b330 : fetch_word Plain.M.loaded_segments (0x4b330 : word) = Some W_4b330.
Proof. vm_refl. Qed.
Lemma D_4b330 : decode_any W_4b330 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b334 : bv 32 := 0x00813983.
Lemma F_4b334 : fetch_word Plain.M.loaded_segments (0x4b334 : word) = Some W_4b334.
Proof. vm_refl. Qed.
Lemma D_4b334 : decode_any W_4b334 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b338 : bv 32 := 0x03010113.
Lemma F_4b338 : fetch_word Plain.M.loaded_segments (0x4b338 : word) = Some W_4b338.
Proof. vm_refl. Qed.
Lemma D_4b338 : decode_any W_4b338 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b33c : bv 32 := 0x1740e06f.
Lemma F_4b33c : fetch_word Plain.M.loaded_segments (0x4b33c : word) = Some W_4b33c.
Proof. vm_refl. Qed.
Lemma D_4b33c : decode_any W_4b33c = Some (Jal 0 57716, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b340 : bv 32 := 0x00008067.
Lemma F_4b340 : fetch_word Plain.M.loaded_segments (0x4b340 : word) = Some W_4b340.
Proof. vm_refl. Qed.
Lemma D_4b340 : decode_any W_4b340 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b408 : bv 32 := 0x00050067.
Lemma F_4b408 : fetch_word Plain.M.loaded_segments (0x4b408 : word) = Some W_4b408.
Proof. vm_refl. Qed.
Lemma D_4b408 : decode_any W_4b408 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b40c : bv 32 := 0x00008067.
Lemma F_4b40c : fetch_word Plain.M.loaded_segments (0x4b40c : word) = Some W_4b40c.
Proof. vm_refl. Qed.
Lemma D_4b40c : decode_any W_4b40c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b410 : bv 32 := 0xfe010113.
Lemma F_4b410 : fetch_word Plain.M.loaded_segments (0x4b410 : word) = Some W_4b410.
Proof. vm_refl. Qed.
Lemma D_4b410 : decode_any W_4b410 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b414 : bv 32 := 0x00113c23.
Lemma F_4b414 : fetch_word Plain.M.loaded_segments (0x4b414 : word) = Some W_4b414.
Proof. vm_refl. Qed.
Lemma D_4b414 : decode_any W_4b414 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b418 : bv 32 := 0x00813823.
Lemma F_4b418 : fetch_word Plain.M.loaded_segments (0x4b418 : word) = Some W_4b418.
Proof. vm_refl. Qed.
Lemma D_4b418 : decode_any W_4b418 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b41c : bv 32 := 0x00913423.
Lemma F_4b41c : fetch_word Plain.M.loaded_segments (0x4b41c : word) = Some W_4b41c.
Proof. vm_refl. Qed.
Lemma D_4b41c : decode_any W_4b41c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b420 : bv 32 := 0x00013517.
Lemma F_4b420 : fetch_word Plain.M.loaded_segments (0x4b420 : word) = Some W_4b420.
Proof. vm_refl. Qed.
Lemma D_4b420 : decode_any W_4b420 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b424 : bv 32 := 0x00013597.
Lemma F_4b424 : fetch_word Plain.M.loaded_segments (0x4b424 : word) = Some W_4b424.
Proof. vm_refl. Qed.
Lemma D_4b424 : decode_any W_4b424 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b428 : bv 32 := 0x1d853503.
Lemma F_4b428 : fetch_word Plain.M.loaded_segments (0x4b428 : word) = Some W_4b428.
Proof. vm_refl. Qed.
Lemma D_4b428 : decode_any W_4b428 = Some (Load SZ8 true 10 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b42c : bv 32 := 0x1dc5b403.
Lemma F_4b42c : fetch_word Plain.M.loaded_segments (0x4b42c : word) = Some W_4b42c.
Proof. vm_refl. Qed.
Lemma D_4b42c : decode_any W_4b42c = Some (Load SZ8 true 8 11 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b430 : bv 32 := 0x00a47c63.
Lemma F_4b430 : fetch_word Plain.M.loaded_segments (0x4b430 : word) = Some W_4b430.
Proof. vm_refl. Qed.
Lemma D_4b430 : decode_any W_4b430 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b434 : bv 32 := 0xff853583.
Lemma F_4b434 : fetch_word Plain.M.loaded_segments (0x4b434 : word) = Some W_4b434.
Proof. vm_refl. Qed.
Lemma D_4b434 : decode_any W_4b434 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b438 : bv 32 := 0xff850493.
Lemma F_4b438 : fetch_word Plain.M.loaded_segments (0x4b438 : word) = Some W_4b438.
Proof. vm_refl. Qed.
Lemma D_4b438 : decode_any W_4b438 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b43c : bv 32 := 0x000580e7.
Lemma F_4b43c : fetch_word Plain.M.loaded_segments (0x4b43c : word) = Some W_4b43c.
Proof. vm_refl. Qed.
Lemma D_4b43c : decode_any W_4b43c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b440 : bv 32 := 0x00048513.
Lemma F_4b440 : fetch_word Plain.M.loaded_segments (0x4b440 : word) = Some W_4b440.
Proof. vm_refl. Qed.
Lemma D_4b440 : decode_any W_4b440 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b444 : bv 32 := 0xfe9468e3.
Lemma F_4b444 : fetch_word Plain.M.loaded_segments (0x4b444 : word) = Some W_4b444.
Proof. vm_refl. Qed.
Lemma D_4b444 : decode_any W_4b444 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b448 : bv 32 := 0x01813083.
Lemma F_4b448 : fetch_word Plain.M.loaded_segments (0x4b448 : word) = Some W_4b448.
Proof. vm_refl. Qed.
Lemma D_4b448 : decode_any W_4b448 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b44c : bv 32 := 0x01013403.
Lemma F_4b44c : fetch_word Plain.M.loaded_segments (0x4b44c : word) = Some W_4b44c.
Proof. vm_refl. Qed.
Lemma D_4b44c : decode_any W_4b44c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b450 : bv 32 := 0x00813483.
Lemma F_4b450 : fetch_word Plain.M.loaded_segments (0x4b450 : word) = Some W_4b450.
Proof. vm_refl. Qed.
Lemma D_4b450 : decode_any W_4b450 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b454 : bv 32 := 0x02010113.
Lemma F_4b454 : fetch_word Plain.M.loaded_segments (0x4b454 : word) = Some W_4b454.
Proof. vm_refl. Qed.
Lemma D_4b454 : decode_any W_4b454 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b458 : bv 32 := 0xfb5ff06f.
Lemma F_4b458 : fetch_word Plain.M.loaded_segments (0x4b458 : word) = Some W_4b458.
Proof. vm_refl. Qed.
Lemma D_4b458 : decode_any W_4b458 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b45c : bv 32 := 0xff010113.
Lemma F_4b45c : fetch_word Plain.M.loaded_segments (0x4b45c : word) = Some W_4b45c.
Proof. vm_refl. Qed.
Lemma D_4b45c : decode_any W_4b45c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b460 : bv 32 := 0x00113423.
Lemma F_4b460 : fetch_word Plain.M.loaded_segments (0x4b460 : word) = Some W_4b460.
Proof. vm_refl. Qed.
Lemma D_4b460 : decode_any W_4b460 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b464 : bv 32 := 0x00813023.
Lemma F_4b464 : fetch_word Plain.M.loaded_segments (0x4b464 : word) = Some W_4b464.
Proof. vm_refl. Qed.
Lemma D_4b464 : decode_any W_4b464 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b468 : bv 32 := 0x00000593.
Lemma F_4b468 : fetch_word Plain.M.loaded_segments (0x4b468 : word) = Some W_4b468.
Proof. vm_refl. Qed.
Lemma D_4b468 : decode_any W_4b468 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b46c : bv 32 := 0x00020613.
Lemma F_4b46c : fetch_word Plain.M.loaded_segments (0x4b46c : word) = Some W_4b46c.
Proof. vm_refl. Qed.
Lemma D_4b46c : decode_any W_4b46c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b470 : bv 32 := 0xf5862603.
Lemma F_4b470 : fetch_word Plain.M.loaded_segments (0x4b470 : word) = Some W_4b470.
Proof. vm_refl. Qed.
Lemma D_4b470 : decode_any W_4b470 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b474 : bv 32 := 0x00045697.
Lemma F_4b474 : fetch_word Plain.M.loaded_segments (0x4b474 : word) = Some W_4b474.
Proof. vm_refl. Qed.
Lemma D_4b474 : decode_any W_4b474 = Some (Auipc 13 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b478 : bv 32 := 0x22c68693.
Lemma F_4b478 : fetch_word Plain.M.loaded_segments (0x4b478 : word) = Some W_4b478.
Proof. vm_refl. Qed.
Lemma D_4b478 : decode_any W_4b478 = Some (OpImm ALU_ADD 13 13 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b47c : bv 32 := 0x1606a72f.
Lemma F_4b47c : fetch_word Plain.M.loaded_segments (0x4b47c : word) = Some W_4b47c.
Proof. vm_refl. Qed.
Lemma D_4b47c : decode_any W_4b47c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b480 : bv 32 := 0x00b71663.
Lemma F_4b480 : fetch_word Plain.M.loaded_segments (0x4b480 : word) = Some W_4b480.
Proof. vm_refl. Qed.
Lemma D_4b480 : decode_any W_4b480 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b484 : bv 32 := 0x1ec6a7af.
Lemma F_4b484 : fetch_word Plain.M.loaded_segments (0x4b484 : word) = Some W_4b484.
Proof. vm_refl. Qed.
Lemma D_4b484 : decode_any W_4b484 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b488 : bv 32 := 0xfe079ae3.
Lemma F_4b488 : fetch_word Plain.M.loaded_segments (0x4b488 : word) = Some W_4b488.
Proof. vm_refl. Qed.
Lemma D_4b488 : decode_any W_4b488 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b48c : bv 32 := 0x0007059b.
Lemma F_4b48c : fetch_word Plain.M.loaded_segments (0x4b48c : word) = Some W_4b48c.
Proof. vm_refl. Qed.
Lemma D_4b48c : decode_any W_4b48c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b490 : bv 32 := 0x02c58263.
Lemma F_4b490 : fetch_word Plain.M.loaded_segments (0x4b490 : word) = Some W_4b490.
Proof. vm_refl. Qed.
Lemma D_4b490 : decode_any W_4b490 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b494 : bv 32 := 0x02058263.
Lemma F_4b494 : fetch_word Plain.M.loaded_segments (0x4b494 : word) = Some W_4b494.
Proof. vm_refl. Qed.
Lemma D_4b494 : decode_any W_4b494 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b4b8 : bv 32 := 0x00050413.
Lemma F_4b4b8 : fetch_word Plain.M.loaded_segments (0x4b4b8 : word) = Some W_4b4b8.
Proof. vm_refl. Qed.
Lemma D_4b4b8 : decode_any W_4b4b8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b4bc : bv 32 := 0xdbdff0ef.
Lemma F_4b4bc : fetch_word Plain.M.loaded_segments (0x4b4bc : word) = Some W_4b4bc.
Proof. vm_refl. Qed.
Lemma D_4b4bc : decode_any W_4b4bc = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b4c0 : bv 32 := 0xf51ff0ef.
Lemma F_4b4c0 : fetch_word Plain.M.loaded_segments (0x4b4c0 : word) = Some W_4b4c0.
Proof. vm_refl. Qed.
Lemma D_4b4c0 : decode_any W_4b4c0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b4c4 : bv 32 := 0x561020ef.
Lemma F_4b4c4 : fetch_word Plain.M.loaded_segments (0x4b4c4 : word) = Some W_4b4c4.
Proof. vm_refl. Qed.
Lemma D_4b4c4 : decode_any W_4b4c4 = Some (Jal 1 11616, 4%Z).
Proof. vm_refl. Qed.

Definition W_59228 : bv 32 := 0x00037597.
Lemma F_59228 : fetch_word Plain.M.loaded_segments (0x59228 : word) = Some W_59228.
Proof. vm_refl. Qed.
Lemma D_59228 : decode_any W_59228 = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

Definition W_5922c : bv 32 := 0x4a358683.
Lemma F_5922c : fetch_word Plain.M.loaded_segments (0x5922c : word) = Some W_5922c.
Proof. vm_refl. Qed.
Lemma D_5922c : decode_any W_5922c = Some (Load SZ1 true 13 11 1187, 4%Z).
Proof. vm_refl. Qed.

Definition W_59230 : bv 32 := 0x1e068863.
Lemma F_59230 : fetch_word Plain.M.loaded_segments (0x59230 : word) = Some W_59230.
Proof. vm_refl. Qed.
Lemma D_59230 : decode_any W_59230 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_59420 : bv 32 := 0x00008067.
Lemma F_59420 : fetch_word Plain.M.loaded_segments (0x59420 : word) = Some W_59420.
Proof. vm_refl. Qed.
Lemma D_59420 : decode_any W_59420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_594b0 : bv 32 := 0x00052583.
Lemma F_594b0 : fetch_word Plain.M.loaded_segments (0x594b0 : word) = Some W_594b0.
Proof. vm_refl. Qed.
Lemma D_594b0 : decode_any W_594b0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_594b4 : bv 32 := 0x0005c463.
Lemma F_594b4 : fetch_word Plain.M.loaded_segments (0x594b4 : word) = Some W_594b4.
Proof. vm_refl. Qed.
Lemma D_594b4 : decode_any W_594b4 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_594b8 : bv 32 := 0x00008067.
Lemma F_594b8 : fetch_word Plain.M.loaded_segments (0x594b8 : word) = Some W_594b8.
Proof. vm_refl. Qed.
Lemma D_594b8 : decode_any W_594b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
