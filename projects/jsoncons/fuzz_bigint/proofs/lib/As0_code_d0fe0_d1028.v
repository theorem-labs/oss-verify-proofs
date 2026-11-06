(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d0fe0 : bv 32 := 0xff010113.
Lemma F_d0fe0 : fetch_word Asan.M.loaded_segments (0xd0fe0 : word) = Some W_d0fe0.
Proof. vm_refl. Qed.
Lemma D_d0fe0 : decode_any W_d0fe0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fe4 : bv 32 := 0x00113423.
Lemma F_d0fe4 : fetch_word Asan.M.loaded_segments (0xd0fe4 : word) = Some W_d0fe4.
Proof. vm_refl. Qed.
Lemma D_d0fe4 : decode_any W_d0fe4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fe8 : bv 32 := 0x00813023.
Lemma F_d0fe8 : fetch_word Asan.M.loaded_segments (0xd0fe8 : word) = Some W_d0fe8.
Proof. vm_refl. Qed.
Lemma D_d0fe8 : decode_any W_d0fe8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fec : bv 32 := 0x00153413.
Lemma F_d0fec : fetch_word Asan.M.loaded_segments (0xd0fec : word) = Some W_d0fec.
Proof. vm_refl. Qed.
Lemma D_d0fec : decode_any W_d0fec = Some (OpImm ALU_SLTU 8 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0ff0 : bv 32 := 0x00850433.
Lemma F_d0ff0 : fetch_word Asan.M.loaded_segments (0xd0ff0 : word) = Some W_d0ff0.
Proof. vm_refl. Qed.
Lemma D_d0ff0 : decode_any W_d0ff0 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0ff4 : bv 32 := 0x00040513.
Lemma F_d0ff4 : fetch_word Asan.M.loaded_segments (0xd0ff4 : word) = Some W_d0ff4.
Proof. vm_refl. Qed.
Lemma D_d0ff4 : decode_any W_d0ff4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0ff8 : bv 32 := 0xc618e0ef.
Lemma F_d0ff8 : fetch_word Asan.M.loaded_segments (0xd0ff8 : word) = Some W_d0ff8.
Proof. vm_refl. Qed.
Lemma D_d0ff8 : decode_any W_d0ff8 = Some (Jal 1 1633376, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0ffc : bv 32 := 0x00051e63.
Lemma F_d0ffc : fetch_word Asan.M.loaded_segments (0xd0ffc : word) = Some W_d0ffc.
Proof. vm_refl. Qed.
Lemma D_d0ffc : decode_any W_d0ffc = Some (Branch BC_NE 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1000 : bv 32 := 0xd64c30ef.
Lemma F_d1000 : fetch_word Asan.M.loaded_segments (0xd1000 : word) = Some W_d1000.
Proof. vm_refl. Qed.
Lemma D_d1000 : decode_any W_d1000 = Some (Jal 1 1848676, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1004 : bv 32 := 0x02050263.
Lemma F_d1004 : fetch_word Asan.M.loaded_segments (0xd1004 : word) = Some W_d1004.
Proof. vm_refl. Qed.
Lemma D_d1004 : decode_any W_d1004 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1008 : bv 32 := 0x000500e7.
Lemma F_d1008 : fetch_word Asan.M.loaded_segments (0xd1008 : word) = Some W_d1008.
Proof. vm_refl. Qed.
Lemma D_d1008 : decode_any W_d1008 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d100c : bv 32 := 0x00040513.
Lemma F_d100c : fetch_word Asan.M.loaded_segments (0xd100c : word) = Some W_d100c.
Proof. vm_refl. Qed.
Lemma D_d100c : decode_any W_d100c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1010 : bv 32 := 0xc498e0ef.
Lemma F_d1010 : fetch_word Asan.M.loaded_segments (0xd1010 : word) = Some W_d1010.
Proof. vm_refl. Qed.
Lemma D_d1010 : decode_any W_d1010 = Some (Jal 1 1633352, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1014 : bv 32 := 0xfe0506e3.
Lemma F_d1014 : fetch_word Asan.M.loaded_segments (0xd1014 : word) = Some W_d1014.
Proof. vm_refl. Qed.
Lemma D_d1014 : decode_any W_d1014 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1018 : bv 32 := 0x00813083.
Lemma F_d1018 : fetch_word Asan.M.loaded_segments (0xd1018 : word) = Some W_d1018.
Proof. vm_refl. Qed.
Lemma D_d1018 : decode_any W_d1018 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d101c : bv 32 := 0x00013403.
Lemma F_d101c : fetch_word Asan.M.loaded_segments (0xd101c : word) = Some W_d101c.
Proof. vm_refl. Qed.
Lemma D_d101c : decode_any W_d101c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1020 : bv 32 := 0x01010113.
Lemma F_d1020 : fetch_word Asan.M.loaded_segments (0xd1020 : word) = Some W_d1020.
Proof. vm_refl. Qed.
Lemma D_d1020 : decode_any W_d1020 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1024 : bv 32 := 0x00008067.
Lemma F_d1024 : fetch_word Asan.M.loaded_segments (0xd1024 : word) = Some W_d1024.
Proof. vm_refl. Qed.
Lemma D_d1024 : decode_any W_d1024 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
