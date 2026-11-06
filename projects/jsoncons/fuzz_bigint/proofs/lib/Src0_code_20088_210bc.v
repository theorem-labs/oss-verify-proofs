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

Definition W_2014c : bv 32 := 0x24050a63.
Lemma F_2014c : fetch_word Plain.M.loaded_segments (0x2014c : word) = Some W_2014c.
Proof. vm_refl. Qed.
Lemma D_2014c : decode_any W_2014c = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_2018c : bv 32 := 0x01a9d513.
Lemma F_2018c : fetch_word Plain.M.loaded_segments (0x2018c : word) = Some W_2018c.
Proof. vm_refl. Qed.
Lemma D_2018c : decode_any W_2018c = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_20190 : bv 32 := 0x1a051863.
Lemma F_20190 : fetch_word Plain.M.loaded_segments (0x20190 : word) = Some W_20190.
Proof. vm_refl. Qed.
Lemma D_20190 : decode_any W_20190 = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_20194 : bv 32 := 0x00199a93.
Lemma F_20194 : fetch_word Plain.M.loaded_segments (0x20194 : word) = Some W_20194.
Proof. vm_refl. Qed.
Lemma D_20194 : decode_any W_20194 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20198 : bv 32 := 0x000a8513.
Lemma F_20198 : fetch_word Plain.M.loaded_segments (0x20198 : word) = Some W_20198.
Proof. vm_refl. Qed.
Lemma D_20198 : decode_any W_20198 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2019c : bv 32 := 0x7a82b0ef.
Lemma F_2019c : fetch_word Plain.M.loaded_segments (0x2019c : word) = Some W_2019c.
Proof. vm_refl. Qed.
Lemma D_2019c : decode_any W_2019c = Some (Jal 1 178088, 4%Z).
Proof. vm_refl. Qed.

Definition W_201a0 : bv 32 := 0x1c050063.
Lemma F_201a0 : fetch_word Plain.M.loaded_segments (0x201a0 : word) = Some W_201a0.
Proof. vm_refl. Qed.
Lemma D_201a0 : decode_any W_201a0 = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_201a4 : bv 32 := 0x00050493.
Lemma F_201a4 : fetch_word Plain.M.loaded_segments (0x201a4 : word) = Some W_201a4.
Proof. vm_refl. Qed.
Lemma D_201a4 : decode_any W_201a4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_201a8 : bv 32 := 0x00098a63.
Lemma F_201a8 : fetch_word Plain.M.loaded_segments (0x201a8 : word) = Some W_201a8.
Proof. vm_refl. Qed.
Lemma D_201a8 : decode_any W_201a8 = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_201ac : bv 32 := 0x00048513.
Lemma F_201ac : fetch_word Plain.M.loaded_segments (0x201ac : word) = Some W_201ac.
Proof. vm_refl. Qed.
Lemma D_201ac : decode_any W_201ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_201b0 : bv 32 := 0x000b8593.
Lemma F_201b0 : fetch_word Plain.M.loaded_segments (0x201b0 : word) = Some W_201b0.
Proof. vm_refl. Qed.
Lemma D_201b0 : decode_any W_201b0 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_201b4 : bv 32 := 0x00098613.
Lemma F_201b4 : fetch_word Plain.M.loaded_segments (0x201b4 : word) = Some W_201b4.
Proof. vm_refl. Qed.
Lemma D_201b4 : decode_any W_201b4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_201b8 : bv 32 := 0x76c380ef.
Lemma F_201b8 : fetch_word Plain.M.loaded_segments (0x201b8 : word) = Some W_201b8.
Proof. vm_refl. Qed.
Lemma D_201b8 : decode_any W_201b8 = Some (Jal 1 231276, 4%Z).
Proof. vm_refl. Qed.

Definition W_201ec : bv 32 := 0x000a0513.
Lemma F_201ec : fetch_word Plain.M.loaded_segments (0x201ec : word) = Some W_201ec.
Proof. vm_refl. Qed.
Lemma D_201ec : decode_any W_201ec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_201f0 : bv 32 := 0x62d390ef.
Lemma F_201f0 : fetch_word Plain.M.loaded_segments (0x201f0 : word) = Some W_201f0.
Proof. vm_refl. Qed.
Lemma D_201f0 : decode_any W_201f0 = Some (Jal 1 237100, 4%Z).
Proof. vm_refl. Qed.

Definition W_2026c : bv 32 := 0x000ac663.
Lemma F_2026c : fetch_word Plain.M.loaded_segments (0x2026c : word) = Some W_2026c.
Proof. vm_refl. Qed.
Lemma D_2026c : decode_any W_2026c = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20270 : bv 32 := 0x00050413.
Lemma F_20270 : fetch_word Plain.M.loaded_segments (0x20270 : word) = Some W_20270.
Proof. vm_refl. Qed.
Lemma D_20270 : decode_any W_20270 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20274 : bv 32 := 0x0780006f.
Lemma F_20274 : fetch_word Plain.M.loaded_segments (0x20274 : word) = Some W_20274.
Proof. vm_refl. Qed.
Lemma D_20274 : decode_any W_20274 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_20278 : bv 32 := 0x148000ef.
Lemma F_20278 : fetch_word Plain.M.loaded_segments (0x20278 : word) = Some W_20278.
Proof. vm_refl. Qed.
Lemma D_20278 : decode_any W_20278 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_2027c : bv 32 := 0x0fb00593.
Lemma F_2027c : fetch_word Plain.M.loaded_segments (0x2027c : word) = Some W_2027c.
Proof. vm_refl. Qed.
Lemma D_2027c : decode_any W_2027c = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_20280 : bv 32 := 0x00050413.
Lemma F_20280 : fetch_word Plain.M.loaded_segments (0x20280 : word) = Some W_20280.
Proof. vm_refl. Qed.
Lemma D_20280 : decode_any W_20280 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20284 : bv 32 := 0x06b56463.
Lemma F_20284 : fetch_word Plain.M.loaded_segments (0x20284 : word) = Some W_20284.
Proof. vm_refl. Qed.
Lemma D_20284 : decode_any W_20284 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_203c0 : bv 32 := 0x00000513.
Lemma F_203c0 : fetch_word Plain.M.loaded_segments (0x203c0 : word) = Some W_203c0.
Proof. vm_refl. Qed.
Lemma D_203c0 : decode_any W_203c0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_203c4 : bv 32 := 0x00008067.
Lemma F_203c4 : fetch_word Plain.M.loaded_segments (0x203c4 : word) = Some W_203c4.
Proof. vm_refl. Qed.
Lemma D_203c4 : decode_any W_203c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2096c : bv 32 := 0x00008067.
Lemma F_2096c : fetch_word Plain.M.loaded_segments (0x2096c : word) = Some W_2096c.
Proof. vm_refl. Qed.
Lemma D_2096c : decode_any W_2096c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20a2c : bv 32 := 0x00008067.
Lemma F_20a2c : fetch_word Plain.M.loaded_segments (0x20a2c : word) = Some W_20a2c.
Proof. vm_refl. Qed.
Lemma D_20a2c : decode_any W_20a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20ba4 : bv 32 := 0x00008067.
Lemma F_20ba4 : fetch_word Plain.M.loaded_segments (0x20ba4 : word) = Some W_20ba4.
Proof. vm_refl. Qed.
Lemma D_20ba4 : decode_any W_20ba4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20bf4 : bv 32 := 0x00054603.
Lemma F_20bf4 : fetch_word Plain.M.loaded_segments (0x20bf4 : word) = Some W_20bf4.
Proof. vm_refl. Qed.
Lemma D_20bf4 : decode_any W_20bf4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20bf8 : bv 32 := 0x00b61663.
Lemma F_20bf8 : fetch_word Plain.M.loaded_segments (0x20bf8 : word) = Some W_20bf8.
Proof. vm_refl. Qed.
Lemma D_20bf8 : decode_any W_20bf8 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20bfc : bv 32 := 0x00150513.
Lemma F_20bfc : fetch_word Plain.M.loaded_segments (0x20bfc : word) = Some W_20bfc.
Proof. vm_refl. Qed.
Lemma D_20bfc : decode_any W_20bfc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20c00 : bv 32 := 0xfe856ae3.
Lemma F_20c00 : fetch_word Plain.M.loaded_segments (0x20c00 : word) = Some W_20c00.
Proof. vm_refl. Qed.
Lemma D_20c00 : decode_any W_20c00 = Some (Branch BC_LTU 10 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_20c04 : bv 32 := 0x00850a63.
Lemma F_20c04 : fetch_word Plain.M.loaded_segments (0x20c04 : word) = Some W_20c04.
Proof. vm_refl. Qed.
Lemma D_20c04 : decode_any W_20c04 = Some (Branch BC_EQ 10 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d34 : bv 32 := 0x00008067.
Lemma F_20d34 : fetch_word Plain.M.loaded_segments (0x20d34 : word) = Some W_20d34.
Proof. vm_refl. Qed.
Lemma D_20d34 : decode_any W_20d34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20e84 : bv 32 := 0x00008067.
Lemma F_20e84 : fetch_word Plain.M.loaded_segments (0x20e84 : word) = Some W_20e84.
Proof. vm_refl. Qed.
Lemma D_20e84 : decode_any W_20e84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f70 : bv 32 := 0x02060663.
Lemma F_20f70 : fetch_word Plain.M.loaded_segments (0x20f70 : word) = Some W_20f70.
Proof. vm_refl. Qed.
Lemma D_20f70 : decode_any W_20f70 = Some (Branch BC_EQ 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f98 : bv 32 := 0xfe0692e3.
Lemma F_20f98 : fetch_word Plain.M.loaded_segments (0x20f98 : word) = Some W_20f98.
Proof. vm_refl. Qed.
Lemma D_20f98 : decode_any W_20f98 = Some (Branch BC_NE 13 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_20fb8 : bv 32 := 0x00008067.
Lemma F_20fb8 : fetch_word Plain.M.loaded_segments (0x20fb8 : word) = Some W_20fb8.
Proof. vm_refl. Qed.
Lemma D_20fb8 : decode_any W_20fb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_210b8 : bv 32 := 0x00008067.
Lemma F_210b8 : fetch_word Plain.M.loaded_segments (0x210b8 : word) = Some W_210b8.
Proof. vm_refl. Qed.
Lemma D_210b8 : decode_any W_210b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
