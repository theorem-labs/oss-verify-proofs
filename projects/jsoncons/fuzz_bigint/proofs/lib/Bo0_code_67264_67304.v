(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_67264 : bv 32 := 0xff010113.
Lemma F_67264 : fetch_word AsanUbsan.M.loaded_segments (0x67264 : word) = Some W_67264.
Proof. vm_refl. Qed.
Lemma D_67264 : decode_any W_67264 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_67268 : bv 32 := 0x00113423.
Lemma F_67268 : fetch_word AsanUbsan.M.loaded_segments (0x67268 : word) = Some W_67268.
Proof. vm_refl. Qed.
Lemma D_67268 : decode_any W_67268 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6726c : bv 32 := 0x00813023.
Lemma F_6726c : fetch_word AsanUbsan.M.loaded_segments (0x6726c : word) = Some W_6726c.
Proof. vm_refl. Qed.
Lemma D_6726c : decode_any W_6726c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67270 : bv 32 := 0x00078517.
Lemma F_67270 : fetch_word AsanUbsan.M.loaded_segments (0x67270 : word) = Some W_67270.
Proof. vm_refl. Qed.
Lemma D_67270 : decode_any W_67270 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_67274 : bv 32 := 0x1a850413.
Lemma F_67274 : fetch_word AsanUbsan.M.loaded_segments (0x67274 : word) = Some W_67274.
Proof. vm_refl. Qed.
Lemma D_67274 : decode_any W_67274 = Some (OpImm ALU_ADD 8 10 424, 4%Z).
Proof. vm_refl. Qed.

Definition W_67278 : bv 32 := 0x00040583.
Lemma F_67278 : fetch_word AsanUbsan.M.loaded_segments (0x67278 : word) = Some W_67278.
Proof. vm_refl. Qed.
Lemma D_67278 : decode_any W_67278 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6727c : bv 32 := 0x00100513.
Lemma F_6727c : fetch_word AsanUbsan.M.loaded_segments (0x6727c : word) = Some W_6727c.
Proof. vm_refl. Qed.
Lemma D_6727c : decode_any W_6727c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67280 : bv 32 := 0x0230000f.
Lemma F_67280 : fetch_word AsanUbsan.M.loaded_segments (0x67280 : word) = Some W_67280.
Proof. vm_refl. Qed.
Lemma D_67280 : decode_any W_67280 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67284 : bv 32 := 0x00a59a63.
Lemma F_67284 : fetch_word AsanUbsan.M.loaded_segments (0x67284 : word) = Some W_67284.
Proof. vm_refl. Qed.
Lemma D_67284 : decode_any W_67284 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_67288 : bv 32 := 0x00813083.
Lemma F_67288 : fetch_word AsanUbsan.M.loaded_segments (0x67288 : word) = Some W_67288.
Proof. vm_refl. Qed.
Lemma D_67288 : decode_any W_67288 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6728c : bv 32 := 0x00013403.
Lemma F_6728c : fetch_word AsanUbsan.M.loaded_segments (0x6728c : word) = Some W_6728c.
Proof. vm_refl. Qed.
Lemma D_6728c : decode_any W_6728c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67290 : bv 32 := 0x01010113.
Lemma F_67290 : fetch_word AsanUbsan.M.loaded_segments (0x67290 : word) = Some W_67290.
Proof. vm_refl. Qed.
Lemma D_67290 : decode_any W_67290 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67294 : bv 32 := 0x00008067.
Lemma F_67294 : fetch_word AsanUbsan.M.loaded_segments (0x67294 : word) = Some W_67294.
Proof. vm_refl. Qed.
Lemma D_67294 : decode_any W_67294 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67298 : bv 32 := 0x00240513.
Lemma F_67298 : fetch_word AsanUbsan.M.loaded_segments (0x67298 : word) = Some W_67298.
Proof. vm_refl. Qed.
Lemma D_67298 : decode_any W_67298 = Some (OpImm ALU_ADD 10 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6729c : bv 32 := 0x00ff05b7.
Lemma F_6729c : fetch_word AsanUbsan.M.loaded_segments (0x6729c : word) = Some W_6729c.
Proof. vm_refl. Qed.
Lemma D_6729c : decode_any W_6729c = Some (Lui 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_672a0 : bv 32 := 0xffc57513.
Lemma F_672a0 : fetch_word AsanUbsan.M.loaded_segments (0x672a0 : word) = Some W_672a0.
Proof. vm_refl. Qed.
Lemma D_672a0 : decode_any W_672a0 = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_672a4 : bv 32 := 0x00010637.
Lemma F_672a4 : fetch_word AsanUbsan.M.loaded_segments (0x672a4 : word) = Some W_672a4.
Proof. vm_refl. Qed.
Lemma D_672a4 : decode_any W_672a4 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_672a8 : bv 32 := 0x140526af.
Lemma F_672a8 : fetch_word AsanUbsan.M.loaded_segments (0x672a8 : word) = Some W_672a8.
Proof. vm_refl. Qed.
Lemma D_672a8 : decode_any W_672a8 = Some (Lr AW true false 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_672ac : bv 32 := 0x00060713.
Lemma F_672ac : fetch_word AsanUbsan.M.loaded_segments (0x672ac : word) = Some W_672ac.
Proof. vm_refl. Qed.
Lemma D_672ac : decode_any W_672ac = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_672b0 : bv 32 := 0x00e6c733.
Lemma F_672b0 : fetch_word AsanUbsan.M.loaded_segments (0x672b0 : word) = Some W_672b0.
Proof. vm_refl. Qed.
Lemma D_672b0 : decode_any W_672b0 = Some (Op ALU_XOR 14 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_672b4 : bv 32 := 0x00b77733.
Lemma F_672b4 : fetch_word AsanUbsan.M.loaded_segments (0x672b4 : word) = Some W_672b4.
Proof. vm_refl. Qed.
Lemma D_672b4 : decode_any W_672b4 = Some (Op ALU_AND 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_672b8 : bv 32 := 0x00e6c733.
Lemma F_672b8 : fetch_word AsanUbsan.M.loaded_segments (0x672b8 : word) = Some W_672b8.
Proof. vm_refl. Qed.
Lemma D_672b8 : decode_any W_672b8 = Some (Op ALU_XOR 14 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_672bc : bv 32 := 0x18e5272f.
Lemma F_672bc : fetch_word AsanUbsan.M.loaded_segments (0x672bc : word) = Some W_672bc.
Proof. vm_refl. Qed.
Lemma D_672bc : decode_any W_672bc = Some (Sc AW false false 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_672c0 : bv 32 := 0xfe0714e3.
Lemma F_672c0 : fetch_word AsanUbsan.M.loaded_segments (0x672c0 : word) = Some W_672c0.
Proof. vm_refl. Qed.
Lemma D_672c0 : decode_any W_672c0 = Some (Branch BC_NE 14 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_672c4 : bv 32 := 0x02869693.
Lemma F_672c4 : fetch_word AsanUbsan.M.loaded_segments (0x672c4 : word) = Some W_672c4.
Proof. vm_refl. Qed.
Lemma D_672c4 : decode_any W_672c4 = Some (ShiftImm ALU_SLL 13 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_672c8 : bv 32 := 0x0386d693.
Lemma F_672c8 : fetch_word AsanUbsan.M.loaded_segments (0x672c8 : word) = Some W_672c8.
Proof. vm_refl. Qed.
Lemma D_672c8 : decode_any W_672c8 = Some (ShiftImm ALU_SRL 13 13 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_672cc : bv 32 := 0x00068c63.
Lemma F_672cc : fetch_word AsanUbsan.M.loaded_segments (0x672cc : word) = Some W_672cc.
Proof. vm_refl. Qed.
Lemma D_672cc : decode_any W_672cc = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_672d0 : bv 32 := 0x00000513.
Lemma F_672d0 : fetch_word AsanUbsan.M.loaded_segments (0x672d0 : word) = Some W_672d0.
Proof. vm_refl. Qed.
Lemma D_672d0 : decode_any W_672d0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_672d4 : bv 32 := 0x00813083.
Lemma F_672d4 : fetch_word AsanUbsan.M.loaded_segments (0x672d4 : word) = Some W_672d4.
Proof. vm_refl. Qed.
Lemma D_672d4 : decode_any W_672d4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_672d8 : bv 32 := 0x00013403.
Lemma F_672d8 : fetch_word AsanUbsan.M.loaded_segments (0x672d8 : word) = Some W_672d8.
Proof. vm_refl. Qed.
Lemma D_672d8 : decode_any W_672d8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_672dc : bv 32 := 0x01010113.
Lemma F_672dc : fetch_word AsanUbsan.M.loaded_segments (0x672dc : word) = Some W_672dc.
Proof. vm_refl. Qed.
Lemma D_672dc : decode_any W_672dc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_672e0 : bv 32 := 0x00008067.
Lemma F_672e0 : fetch_word AsanUbsan.M.loaded_segments (0x672e0 : word) = Some W_672e0.
Proof. vm_refl. Qed.
Lemma D_672e0 : decode_any W_672e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_672e4 : bv 32 := 0xccdff0ef.
Lemma F_672e4 : fetch_word AsanUbsan.M.loaded_segments (0x672e4 : word) = Some W_672e4.
Proof. vm_refl. Qed.
Lemma D_672e4 : decode_any W_672e4 = Some (Jal 1 2096332, 4%Z).
Proof. vm_refl. Qed.

Definition W_672e8 : bv 32 := 0x00100513.
Lemma F_672e8 : fetch_word AsanUbsan.M.loaded_segments (0x672e8 : word) = Some W_672e8.
Proof. vm_refl. Qed.
Lemma D_672e8 : decode_any W_672e8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_672ec : bv 32 := 0x0310000f.
Lemma F_672ec : fetch_word AsanUbsan.M.loaded_segments (0x672ec : word) = Some W_672ec.
Proof. vm_refl. Qed.
Lemma D_672ec : decode_any W_672ec = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_672f0 : bv 32 := 0x00040123.
Lemma F_672f0 : fetch_word AsanUbsan.M.loaded_segments (0x672f0 : word) = Some W_672f0.
Proof. vm_refl. Qed.
Lemma D_672f0 : decode_any W_672f0 = Some (Store SZ1 8 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_672f4 : bv 32 := 0x00813083.
Lemma F_672f4 : fetch_word AsanUbsan.M.loaded_segments (0x672f4 : word) = Some W_672f4.
Proof. vm_refl. Qed.
Lemma D_672f4 : decode_any W_672f4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_672f8 : bv 32 := 0x00013403.
Lemma F_672f8 : fetch_word AsanUbsan.M.loaded_segments (0x672f8 : word) = Some W_672f8.
Proof. vm_refl. Qed.
Lemma D_672f8 : decode_any W_672f8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_672fc : bv 32 := 0x01010113.
Lemma F_672fc : fetch_word AsanUbsan.M.loaded_segments (0x672fc : word) = Some W_672fc.
Proof. vm_refl. Qed.
Lemma D_672fc : decode_any W_672fc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67300 : bv 32 := 0x00008067.
Lemma F_67300 : fetch_word AsanUbsan.M.loaded_segments (0x67300 : word) = Some W_67300.
Proof. vm_refl. Qed.
Lemma D_67300 : decode_any W_67300 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
