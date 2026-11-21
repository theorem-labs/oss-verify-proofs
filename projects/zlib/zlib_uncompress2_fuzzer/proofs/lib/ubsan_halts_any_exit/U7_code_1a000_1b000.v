(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition TW_1a158 : bv 32 := 0x00200513.
Lemma TF_1a158 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a158 : word) = Some TW_1a158.
Proof. vm_refl. Qed.
Lemma TD_1a158 : decode_any TW_1a158 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a15c : bv 32 := 0x0007a597.
Lemma TF_1a15c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a15c : word) = Some TW_1a15c.
Proof. vm_refl. Qed.
Lemma TD_1a15c : decode_any TW_1a15c = Some (Auipc 11 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a160 : bv 32 := 0x02a92423.
Lemma TF_1a160 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a160 : word) = Some TW_1a160.
Proof. vm_refl. Qed.
Lemma TD_1a160 : decode_any TW_1a160 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a164 : bv 32 := 0x06000893.
Lemma TF_1a164 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a164 : word) = Some TW_1a164.
Proof. vm_refl. Qed.
Lemma TD_1a164 : decode_any TW_1a164 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a168 : bv 32 := 0x11c58513.
Lemma TF_1a168 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a168 : word) = Some TW_1a168.
Proof. vm_refl. Qed.
Lemma TD_1a168 : decode_any TW_1a168 = Some (OpImm ALU_ADD 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a16c : bv 32 := 0x03848593.
Lemma TF_1a16c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a16c : word) = Some TW_1a16c.
Proof. vm_refl. Qed.
Lemma TD_1a16c : decode_any TW_1a16c = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a170 : bv 32 := 0x00000073.
Lemma TF_1a170 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a170 : word) = Some TW_1a170.
Proof. vm_refl. Qed.
Lemma TD_1a170 : decode_any TW_1a170 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_1a170 : is_ecall TW_1a170 = true.
Proof. reflexivity. Qed.

Definition TW_1a174 : bv 32 := 0x07890613.
Lemma TF_1a174 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a174 : word) = Some TW_1a174.
Proof. vm_refl. Qed.
Lemma TD_1a174 : decode_any TW_1a174 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a178 : bv 32 := 0x02a92023.
Lemma TF_1a178 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a178 : word) = Some TW_1a178.
Proof. vm_refl. Qed.
Lemma TD_1a178 : decode_any TW_1a178 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a17c : bv 32 := 0x08b93c23.
Lemma TF_1a17c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a17c : word) = Some TW_1a17c.
Proof. vm_refl. Qed.
Lemma TD_1a17c : decode_any TW_1a17c = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a180 : bv 32 := 0x06c93c23.
Lemma TF_1a180 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a180 : word) = Some TW_1a180.
Proof. vm_refl. Qed.
Lemma TD_1a180 : decode_any TW_1a180 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a184 : bv 32 := 0x0007a517.
Lemma TF_1a184 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a184 : word) = Some TW_1a184.
Proof. vm_refl. Qed.
Lemma TD_1a184 : decode_any TW_1a184 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a188 : bv 32 := 0x35c53503.
Lemma TF_1a188 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a188 : word) = Some TW_1a188.
Proof. vm_refl. Qed.
Lemma TD_1a188 : decode_any TW_1a188 = Some (Load SZ8 true 10 10 860, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a18c : bv 32 := 0x01293423.
Lemma TF_1a18c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a18c : word) = Some TW_1a18c.
Proof. vm_refl. Qed.
Lemma TD_1a18c : decode_any TW_1a18c = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a190 : bv 32 := 0x01293823.
Lemma TF_1a190 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a190 : word) = Some TW_1a190.
Proof. vm_refl. Qed.
Lemma TD_1a190 : decode_any TW_1a190 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a194 : bv 32 := 0x00a93c23.
Lemma TF_1a194 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a194 : word) = Some TW_1a194.
Proof. vm_refl. Qed.
Lemma TD_1a194 : decode_any TW_1a194 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a198 : bv 32 := 0x0080006f.
Lemma TF_1a198 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a198 : word) = Some TW_1a198.
Proof. vm_refl. Qed.
Lemma TD_1a198 : decode_any TW_1a198 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a19c : bv 32 := 0x00000023.
Lemma TF_1a19c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a19c : word) = Some TW_1a19c.
Proof. vm_refl. Qed.
Lemma TD_1a19c : decode_any TW_1a19c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1a0 : bv 32 := 0x03813083.
Lemma TF_1a1a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1a0 : word) = Some TW_1a1a0.
Proof. vm_refl. Qed.
Lemma TD_1a1a0 : decode_any TW_1a1a0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1a4 : bv 32 := 0x03013403.
Lemma TF_1a1a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1a4 : word) = Some TW_1a1a4.
Proof. vm_refl. Qed.
Lemma TD_1a1a4 : decode_any TW_1a1a4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1a8 : bv 32 := 0x02813483.
Lemma TF_1a1a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1a8 : word) = Some TW_1a1a8.
Proof. vm_refl. Qed.
Lemma TD_1a1a8 : decode_any TW_1a1a8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1ac : bv 32 := 0x02013903.
Lemma TF_1a1ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1ac : word) = Some TW_1a1ac.
Proof. vm_refl. Qed.
Lemma TD_1a1ac : decode_any TW_1a1ac = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1b0 : bv 32 := 0x01813983.
Lemma TF_1a1b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1b0 : word) = Some TW_1a1b0.
Proof. vm_refl. Qed.
Lemma TD_1a1b0 : decode_any TW_1a1b0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1b4 : bv 32 := 0x01013a03.
Lemma TF_1a1b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1b4 : word) = Some TW_1a1b4.
Proof. vm_refl. Qed.
Lemma TD_1a1b4 : decode_any TW_1a1b4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1b8 : bv 32 := 0x00813a83.
Lemma TF_1a1b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1b8 : word) = Some TW_1a1b8.
Proof. vm_refl. Qed.
Lemma TD_1a1b8 : decode_any TW_1a1b8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1bc : bv 32 := 0x04010113.
Lemma TF_1a1bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1bc : word) = Some TW_1a1bc.
Proof. vm_refl. Qed.
Lemma TD_1a1bc : decode_any TW_1a1bc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1c0 : bv 32 := 0x00008067.
Lemma TF_1a1c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1c0 : word) = Some TW_1a1c0.
Proof. vm_refl. Qed.
Lemma TD_1a1c0 : decode_any TW_1a1c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a078 : bv 32 := 0xfd010113.
Lemma F_1a078 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1c4 : word) = Some W_1a078.
Proof. vm_refl. Qed.
Lemma D_1a078 : decode_any W_1a078 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a07c : bv 32 := 0x02113423.
Lemma F_1a07c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1c8 : word) = Some W_1a07c.
Proof. vm_refl. Qed.
Lemma D_1a07c : decode_any W_1a07c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a080 : bv 32 := 0x02813023.
Lemma F_1a080 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1cc : word) = Some W_1a080.
Proof. vm_refl. Qed.
Lemma D_1a080 : decode_any W_1a080 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a084 : bv 32 := 0x00913c23.
Lemma F_1a084 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1d0 : word) = Some W_1a084.
Proof. vm_refl. Qed.
Lemma D_1a084 : decode_any W_1a084 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a088 : bv 32 := 0x01213823.
Lemma F_1a088 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1d4 : word) = Some W_1a088.
Proof. vm_refl. Qed.
Lemma D_1a088 : decode_any W_1a088 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a08c : bv 32 := 0x01313423.
Lemma F_1a08c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1d8 : word) = Some W_1a08c.
Proof. vm_refl. Qed.
Lemma D_1a08c : decode_any W_1a08c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a090 : bv 32 := 0x0007a517.
Lemma F_1a090 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1dc : word) = Some W_1a090.
Proof. vm_refl. Qed.
Lemma D_1a090 : decode_any W_1a090 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a094 : bv 32 := 0x0d450913.
Lemma F_1a094 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1e0 : word) = Some W_1a094.
Proof. vm_refl. Qed.
Lemma D_1a094 : decode_any W_1a094 = Some (OpImm ALU_ADD 18 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a098 : bv 32 := 0x00490413.
Lemma F_1a098 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1e4 : word) = Some W_1a098.
Proof. vm_refl. Qed.
Lemma D_1a098 : decode_any W_1a098 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a09c : bv 32 := 0x00040513.
Lemma F_1a09c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1e8 : word) = Some W_1a09c.
Proof. vm_refl. Qed.
Lemma D_1a09c : decode_any W_1a09c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0a0 : bv 32 := 0x091070ef.
Lemma F_1a0a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1ec : word) = Some W_1a0a0.
Proof. vm_refl. Qed.
Lemma D_1a0a0 : decode_any W_1a0a0 = Some (Jal 1 30864, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0a4 : bv 32 := 0x01093503.
Lemma F_1a0a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1f0 : word) = Some W_1a0a4.
Proof. vm_refl. Qed.
Lemma D_1a0a4 : decode_any W_1a0a4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0a8 : bv 32 := 0x06050863.
Lemma F_1a0a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1f4 : word) = Some W_1a0a8.
Proof. vm_refl. Qed.
Lemma D_1a0a8 : decode_any W_1a0a8 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0ac : bv 32 := 0x00892583.
Lemma F_1a0ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1f8 : word) = Some W_1a0ac.
Proof. vm_refl. Qed.
Lemma D_1a0ac : decode_any W_1a0ac = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0b0 : bv 32 := 0x0180006f.
Lemma F_1a0b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a1fc : word) = Some W_1a0b0.
Proof. vm_refl. Qed.
Lemma D_1a0b0 : decode_any W_1a0b0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0b4 : bv 32 := 0x00053503.
Lemma F_1a0b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a200 : word) = Some W_1a0b4.
Proof. vm_refl. Qed.
Lemma D_1a0b4 : decode_any W_1a0b4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0b8 : bv 32 := 0x02000593.
Lemma F_1a0b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a204 : word) = Some W_1a0b8.
Proof. vm_refl. Qed.
Lemma D_1a0b8 : decode_any W_1a0b8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0bc : bv 32 := 0x00b92423.
Lemma F_1a0bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a208 : word) = Some W_1a0bc.
Proof. vm_refl. Qed.
Lemma D_1a0bc : decode_any W_1a0bc = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0c0 : bv 32 := 0x00a93823.
Lemma F_1a0c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a20c : word) = Some W_1a0c0.
Proof. vm_refl. Qed.
Lemma D_1a0c0 : decode_any W_1a0c0 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0c4 : bv 32 := 0x04050a63.
Lemma F_1a0c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a210 : word) = Some W_1a0c4.
Proof. vm_refl. Qed.
Lemma D_1a0c4 : decode_any W_1a0c4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0c8 : bv 32 := 0xfff5861b.
Lemma F_1a0c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a214 : word) = Some W_1a0c8.
Proof. vm_refl. Qed.
Lemma D_1a0c8 : decode_any W_1a0c8 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0cc : bv 32 := 0x00c92423.
Lemma F_1a0cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a218 : word) = Some W_1a0cc.
Proof. vm_refl. Qed.
Lemma D_1a0cc : decode_any W_1a0cc = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0d0 : bv 32 := 0xfeb052e3.
Lemma F_1a0d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a21c : word) = Some W_1a0d0.
Proof. vm_refl. Qed.
Lemma D_1a0d0 : decode_any W_1a0d0 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0d4 : bv 32 := 0x01093503.
Lemma F_1a0d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a220 : word) = Some W_1a0d4.
Proof. vm_refl. Qed.
Lemma D_1a0d4 : decode_any W_1a0d4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0d8 : bv 32 := 0x00361613.
Lemma F_1a0d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a224 : word) = Some W_1a0d8.
Proof. vm_refl. Qed.
Lemma D_1a0d8 : decode_any W_1a0d8 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0dc : bv 32 := 0x00c50533.
Lemma F_1a0dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a228 : word) = Some W_1a0dc.
Proof. vm_refl. Qed.
Lemma D_1a0dc : decode_any W_1a0dc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0e0 : bv 32 := 0x00853983.
Lemma F_1a0e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a22c : word) = Some W_1a0e0.
Proof. vm_refl. Qed.
Lemma D_1a0e0 : decode_any W_1a0e0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0e4 : bv 32 := 0x10853483.
Lemma F_1a0e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a230 : word) = Some W_1a0e4.
Proof. vm_refl. Qed.
Lemma D_1a0e4 : decode_any W_1a0e4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0e8 : bv 32 := 0x00040513.
Lemma F_1a0e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a234 : word) = Some W_1a0e8.
Proof. vm_refl. Qed.
Lemma D_1a0e8 : decode_any W_1a0e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0ec : bv 32 := 0x2cd070ef.
Lemma F_1a0ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a238 : word) = Some W_1a0ec.
Proof. vm_refl. Qed.
Lemma D_1a0ec : decode_any W_1a0ec = Some (Jal 1 31436, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0f0 : bv 32 := 0x00048513.
Lemma F_1a0f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a23c : word) = Some W_1a0f0.
Proof. vm_refl. Qed.
Lemma D_1a0f0 : decode_any W_1a0f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0f4 : bv 32 := 0x000980e7.
Lemma F_1a0f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a240 : word) = Some W_1a0f4.
Proof. vm_refl. Qed.
Lemma D_1a0f4 : decode_any W_1a0f4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0f8 : bv 32 := 0x00040513.
Lemma F_1a0f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a244 : word) = Some W_1a0f8.
Proof. vm_refl. Qed.
Lemma D_1a0f8 : decode_any W_1a0f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a0fc : bv 32 := 0x035070ef.
Lemma F_1a0fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a248 : word) = Some W_1a0fc.
Proof. vm_refl. Qed.
Lemma D_1a0fc : decode_any W_1a0fc = Some (Jal 1 30772, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a100 : bv 32 := 0x00892503.
Lemma F_1a100 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a24c : word) = Some W_1a100.
Proof. vm_refl. Qed.
Lemma D_1a100 : decode_any W_1a100 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a104 : bv 32 := 0xfff5061b.
Lemma F_1a104 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a250 : word) = Some W_1a104.
Proof. vm_refl. Qed.
Lemma D_1a104 : decode_any W_1a104 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a108 : bv 32 := 0x00c92423.
Lemma F_1a108 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a254 : word) = Some W_1a108.
Proof. vm_refl. Qed.
Lemma D_1a108 : decode_any W_1a108 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a10c : bv 32 := 0xfca044e3.
Lemma F_1a10c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a258 : word) = Some W_1a10c.
Proof. vm_refl. Qed.
Lemma D_1a10c : decode_any W_1a10c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a110 : bv 32 := 0x01093503.
Lemma F_1a110 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a25c : word) = Some W_1a110.
Proof. vm_refl. Qed.
Lemma D_1a110 : decode_any W_1a110 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a114 : bv 32 := 0xfa1ff06f.
Lemma F_1a114 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a260 : word) = Some W_1a114.
Proof. vm_refl. Qed.
Lemma D_1a114 : decode_any W_1a114 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a118 : bv 32 := 0x00100513.
Lemma F_1a118 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a264 : word) = Some W_1a118.
Proof. vm_refl. Qed.
Lemma D_1a118 : decode_any W_1a118 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a11c : bv 32 := 0x00a90023.
Lemma F_1a11c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a268 : word) = Some W_1a11c.
Proof. vm_refl. Qed.
Lemma D_1a11c : decode_any W_1a11c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a120 : bv 32 := 0x00040513.
Lemma F_1a120 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a26c : word) = Some W_1a120.
Proof. vm_refl. Qed.
Lemma D_1a120 : decode_any W_1a120 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a124 : bv 32 := 0x02813083.
Lemma F_1a124 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a270 : word) = Some W_1a124.
Proof. vm_refl. Qed.
Lemma D_1a124 : decode_any W_1a124 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a128 : bv 32 := 0x02013403.
Lemma F_1a128 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a274 : word) = Some W_1a128.
Proof. vm_refl. Qed.
Lemma D_1a128 : decode_any W_1a128 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a12c : bv 32 := 0x01813483.
Lemma F_1a12c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a278 : word) = Some W_1a12c.
Proof. vm_refl. Qed.
Lemma D_1a12c : decode_any W_1a12c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a130 : bv 32 := 0x01013903.
Lemma F_1a130 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a27c : word) = Some W_1a130.
Proof. vm_refl. Qed.
Lemma D_1a130 : decode_any W_1a130 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a134 : bv 32 := 0x00813983.
Lemma F_1a134 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a280 : word) = Some W_1a134.
Proof. vm_refl. Qed.
Lemma D_1a134 : decode_any W_1a134 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a138 : bv 32 := 0x03010113.
Lemma F_1a138 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a284 : word) = Some W_1a138.
Proof. vm_refl. Qed.
Lemma D_1a138 : decode_any W_1a138 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a13c : bv 32 := 0x27d0706f.
Lemma F_1a13c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a288 : word) = Some W_1a13c.
Proof. vm_refl. Qed.
Lemma D_1a13c : decode_any W_1a13c = Some (Jal 0 31356, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a140 : bv 32 := 0x00008067.
Lemma F_1a140 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a28c : word) = Some W_1a140.
Proof. vm_refl. Qed.
Lemma D_1a140 : decode_any W_1a140 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a208 : bv 32 := 0x00050067.
Lemma F_1a208 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a354 : word) = Some W_1a208.
Proof. vm_refl. Qed.
Lemma D_1a208 : decode_any W_1a208 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a20c : bv 32 := 0x00008067.
Lemma F_1a20c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a358 : word) = Some W_1a20c.
Proof. vm_refl. Qed.
Lemma D_1a20c : decode_any W_1a20c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a210 : bv 32 := 0xfe010113.
Lemma F_1a210 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a35c : word) = Some W_1a210.
Proof. vm_refl. Qed.
Lemma D_1a210 : decode_any W_1a210 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a214 : bv 32 := 0x00113c23.
Lemma F_1a214 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a360 : word) = Some W_1a214.
Proof. vm_refl. Qed.
Lemma D_1a214 : decode_any W_1a214 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a218 : bv 32 := 0x00813823.
Lemma F_1a218 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a364 : word) = Some W_1a218.
Proof. vm_refl. Qed.
Lemma D_1a218 : decode_any W_1a218 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a21c : bv 32 := 0x00913423.
Lemma F_1a21c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a368 : word) = Some W_1a21c.
Proof. vm_refl. Qed.
Lemma D_1a21c : decode_any W_1a21c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a220 : bv 32 := 0x00009517.
Lemma F_1a220 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a36c : word) = Some W_1a220.
Proof. vm_refl. Qed.
Lemma D_1a220 : decode_any W_1a220 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a224 : bv 32 := 0x00009597.
Lemma F_1a224 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a370 : word) = Some W_1a224.
Proof. vm_refl. Qed.
Lemma D_1a224 : decode_any W_1a224 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a228 : bv 32 := 0xb8c53503.
Lemma F_1a228 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a374 : word) = Some W_1a228.
Proof. vm_refl. Qed.
Lemma D_1a228 : decode_any W_1a228 = Some (Load SZ8 true 10 10 2956, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a22c : bv 32 := 0xb905b403.
Lemma F_1a22c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a378 : word) = Some W_1a22c.
Proof. vm_refl. Qed.
Lemma D_1a22c : decode_any W_1a22c = Some (Load SZ8 true 8 11 2960, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a230 : bv 32 := 0x00a47c63.
Lemma F_1a230 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a37c : word) = Some W_1a230.
Proof. vm_refl. Qed.
Lemma D_1a230 : decode_any W_1a230 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a234 : bv 32 := 0xff853583.
Lemma F_1a234 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a380 : word) = Some W_1a234.
Proof. vm_refl. Qed.
Lemma D_1a234 : decode_any W_1a234 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a238 : bv 32 := 0xff850493.
Lemma F_1a238 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a384 : word) = Some W_1a238.
Proof. vm_refl. Qed.
Lemma D_1a238 : decode_any W_1a238 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a23c : bv 32 := 0x000580e7.
Lemma F_1a23c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a388 : word) = Some W_1a23c.
Proof. vm_refl. Qed.
Lemma D_1a23c : decode_any W_1a23c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a240 : bv 32 := 0x00048513.
Lemma F_1a240 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a38c : word) = Some W_1a240.
Proof. vm_refl. Qed.
Lemma D_1a240 : decode_any W_1a240 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a244 : bv 32 := 0xfe9468e3.
Lemma F_1a244 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a390 : word) = Some W_1a244.
Proof. vm_refl. Qed.
Lemma D_1a244 : decode_any W_1a244 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a248 : bv 32 := 0x01813083.
Lemma F_1a248 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a394 : word) = Some W_1a248.
Proof. vm_refl. Qed.
Lemma D_1a248 : decode_any W_1a248 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a24c : bv 32 := 0x01013403.
Lemma F_1a24c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a398 : word) = Some W_1a24c.
Proof. vm_refl. Qed.
Lemma D_1a24c : decode_any W_1a24c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a250 : bv 32 := 0x00813483.
Lemma F_1a250 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a39c : word) = Some W_1a250.
Proof. vm_refl. Qed.
Lemma D_1a250 : decode_any W_1a250 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a254 : bv 32 := 0x02010113.
Lemma F_1a254 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3a0 : word) = Some W_1a254.
Proof. vm_refl. Qed.
Lemma D_1a254 : decode_any W_1a254 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a258 : bv 32 := 0xfb5ff06f.
Lemma F_1a258 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3a4 : word) = Some W_1a258.
Proof. vm_refl. Qed.
Lemma D_1a258 : decode_any W_1a258 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a25c : bv 32 := 0xff010113.
Lemma F_1a25c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3a8 : word) = Some W_1a25c.
Proof. vm_refl. Qed.
Lemma D_1a25c : decode_any W_1a25c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a260 : bv 32 := 0x00113423.
Lemma F_1a260 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3ac : word) = Some W_1a260.
Proof. vm_refl. Qed.
Lemma D_1a260 : decode_any W_1a260 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a264 : bv 32 := 0x00813023.
Lemma F_1a264 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3b0 : word) = Some W_1a264.
Proof. vm_refl. Qed.
Lemma D_1a264 : decode_any W_1a264 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a268 : bv 32 := 0x00000593.
Lemma F_1a268 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3b4 : word) = Some W_1a268.
Proof. vm_refl. Qed.
Lemma D_1a268 : decode_any W_1a268 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a26c : bv 32 := 0x00020613.
Lemma F_1a26c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3b8 : word) = Some W_1a26c.
Proof. vm_refl. Qed.
Lemma D_1a26c : decode_any W_1a26c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a270 : bv 32 := 0xf5862603.
Lemma F_1a270 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3bc : word) = Some W_1a270.
Proof. vm_refl. Qed.
Lemma D_1a270 : decode_any W_1a270 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a274 : bv 32 := 0x0007a697.
Lemma F_1a274 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3c0 : word) = Some W_1a274.
Proof. vm_refl. Qed.
Lemma D_1a274 : decode_any W_1a274 = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a278 : bv 32 := 0x11068693.
Lemma F_1a278 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3c4 : word) = Some W_1a278.
Proof. vm_refl. Qed.
Lemma D_1a278 : decode_any W_1a278 = Some (OpImm ALU_ADD 13 13 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a27c : bv 32 := 0x1606a72f.
Lemma F_1a27c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3c8 : word) = Some W_1a27c.
Proof. vm_refl. Qed.
Lemma D_1a27c : decode_any W_1a27c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a280 : bv 32 := 0x00b71663.
Lemma F_1a280 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3cc : word) = Some W_1a280.
Proof. vm_refl. Qed.
Lemma D_1a280 : decode_any W_1a280 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a284 : bv 32 := 0x1ec6a7af.
Lemma F_1a284 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3d0 : word) = Some W_1a284.
Proof. vm_refl. Qed.
Lemma D_1a284 : decode_any W_1a284 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a288 : bv 32 := 0xfe079ae3.
Lemma F_1a288 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3d4 : word) = Some W_1a288.
Proof. vm_refl. Qed.
Lemma D_1a288 : decode_any W_1a288 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a28c : bv 32 := 0x0007059b.
Lemma F_1a28c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3d8 : word) = Some W_1a28c.
Proof. vm_refl. Qed.
Lemma D_1a28c : decode_any W_1a28c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a290 : bv 32 := 0x02c58263.
Lemma F_1a290 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3dc : word) = Some W_1a290.
Proof. vm_refl. Qed.
Lemma D_1a290 : decode_any W_1a290 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a294 : bv 32 := 0x02058263.
Lemma F_1a294 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3e0 : word) = Some W_1a294.
Proof. vm_refl. Qed.
Lemma D_1a294 : decode_any W_1a294 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a298 : bv 32 := 0x04900893.
Lemma F_1a298 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3e4 : word) = Some W_1a298.
Proof. vm_refl. Qed.
Lemma D_1a298 : decode_any W_1a298 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a29c : bv 32 := 0x00000593.
Lemma F_1a29c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3e8 : word) = Some W_1a29c.
Proof. vm_refl. Qed.
Lemma D_1a29c : decode_any W_1a29c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2a0 : bv 32 := 0x00000613.
Lemma F_1a2a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3ec : word) = Some W_1a2a0.
Proof. vm_refl. Qed.
Lemma D_1a2a0 : decode_any W_1a2a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2a4 : bv 32 := 0x00000693.
Lemma F_1a2a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3f0 : word) = Some W_1a2a4.
Proof. vm_refl. Qed.
Lemma D_1a2a4 : decode_any W_1a2a4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2a8 : bv 32 := 0x00000513.
Lemma F_1a2a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3f4 : word) = Some W_1a2a8.
Proof. vm_refl. Qed.
Lemma D_1a2a8 : decode_any W_1a2a8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2ac : bv 32 := 0x00000073.
Lemma F_1a2ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3f8 : word) = Some W_1a2ac.
Proof. vm_refl. Qed.
Lemma D_1a2ac : decode_any W_1a2ac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1a2ac : is_ecall W_1a2ac = true.
Proof. reflexivity. Qed.

Definition W_1a2b0 : bv 32 := 0xff9ff06f.
Lemma F_1a2b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a3fc : word) = Some W_1a2b0.
Proof. vm_refl. Qed.
Lemma D_1a2b0 : decode_any W_1a2b0 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2b4 : bv 32 := 0x00000023.
Lemma F_1a2b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a400 : word) = Some W_1a2b4.
Proof. vm_refl. Qed.
Lemma D_1a2b4 : decode_any W_1a2b4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2b8 : bv 32 := 0x00050413.
Lemma F_1a2b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a404 : word) = Some W_1a2b8.
Proof. vm_refl. Qed.
Lemma D_1a2b8 : decode_any W_1a2b8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2bc : bv 32 := 0xdbdff0ef.
Lemma F_1a2bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a408 : word) = Some W_1a2bc.
Proof. vm_refl. Qed.
Lemma D_1a2bc : decode_any W_1a2bc = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2c0 : bv 32 := 0xf51ff0ef.
Lemma F_1a2c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a40c : word) = Some W_1a2c0.
Proof. vm_refl. Qed.
Lemma D_1a2c0 : decode_any W_1a2c0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2c4 : bv 32 := 0x258020ef.
Lemma F_1a2c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a410 : word) = Some W_1a2c4.
Proof. vm_refl. Qed.
Lemma D_1a2c4 : decode_any W_1a2c4 = Some (Jal 1 8792, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2c8 : bv 32 := 0x00040513.
Lemma F_1a2c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a414 : word) = Some W_1a2c8.
Proof. vm_refl. Qed.
Lemma D_1a2c8 : decode_any W_1a2c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2cc : bv 32 := 0x004000ef.
Lemma F_1a2cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a418 : word) = Some W_1a2cc.
Proof. vm_refl. Qed.
Lemma D_1a2cc : decode_any W_1a2cc = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2d0 : bv 32 := 0x00050593.
Lemma F_1a2d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a41c : word) = Some W_1a2d0.
Proof. vm_refl. Qed.
Lemma D_1a2d0 : decode_any W_1a2d0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2d4 : bv 32 := 0x05e00893.
Lemma F_1a2d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a420 : word) = Some W_1a2d4.
Proof. vm_refl. Qed.
Lemma D_1a2d4 : decode_any W_1a2d4 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a2d8 : bv 32 := 0x00000073.
Lemma F_1a2d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a424 : word) = Some W_1a2d8.
Proof. vm_refl. Qed.
Lemma D_1a2d8 : decode_any W_1a2d8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1a2d8 : is_ecall W_1a2d8 = true.
Proof. reflexivity. Qed.

Definition W_1a3d0 : bv 32 := 0xff010113.
Lemma F_1a3d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a51c : word) = Some W_1a3d0.
Proof. vm_refl. Qed.
Lemma D_1a3d0 : decode_any W_1a3d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3d4 : bv 32 := 0x00113423.
Lemma F_1a3d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a520 : word) = Some W_1a3d4.
Proof. vm_refl. Qed.
Lemma D_1a3d4 : decode_any W_1a3d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3d8 : bv 32 := 0x00050e63.
Lemma F_1a3d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a524 : word) = Some W_1a3d8.
Proof. vm_refl. Qed.
Lemma D_1a3d8 : decode_any W_1a3d8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3dc : bv 32 := 0x00050593.
Lemma F_1a3dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a528 : word) = Some W_1a3dc.
Proof. vm_refl. Qed.
Lemma D_1a3dc : decode_any W_1a3dc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3e0 : bv 32 := 0x00009517.
Lemma F_1a3e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a52c : word) = Some W_1a3e0.
Proof. vm_refl. Qed.
Lemma D_1a3e0 : decode_any W_1a3e0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3e4 : bv 32 := 0x9c453503.
Lemma F_1a3e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a530 : word) = Some W_1a3e4.
Proof. vm_refl. Qed.
Lemma D_1a3e4 : decode_any W_1a3e4 = Some (Load SZ8 true 10 10 2500, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3e8 : bv 32 := 0x00800613.
Lemma F_1a3e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a534 : word) = Some W_1a3e8.
Proof. vm_refl. Qed.
Lemma D_1a3e8 : decode_any W_1a3e8 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3ec : bv 32 := 0x739060ef.
Lemma F_1a3ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a538 : word) = Some W_1a3ec.
Proof. vm_refl. Qed.
Lemma D_1a3ec : decode_any W_1a3ec = Some (Jal 1 28472, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3f0 : bv 32 := 0x01c0006f.
Lemma F_1a3f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a53c : word) = Some W_1a3f0.
Proof. vm_refl. Qed.
Lemma D_1a3f0 : decode_any W_1a3f0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3f4 : bv 32 := 0x00009517.
Lemma F_1a3f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a540 : word) = Some W_1a3f4.
Proof. vm_refl. Qed.
Lemma D_1a3f4 : decode_any W_1a3f4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3f8 : bv 32 := 0x9b053503.
Lemma F_1a3f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a544 : word) = Some W_1a3f8.
Proof. vm_refl. Qed.
Lemma D_1a3f8 : decode_any W_1a3f8 = Some (Load SZ8 true 10 10 2480, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3fc : bv 32 := 0x41c655b7.
Lemma F_1a3fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a548 : word) = Some W_1a3fc.
Proof. vm_refl. Qed.
Lemma D_1a3fc : decode_any W_1a3fc = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a400 : bv 32 := 0xe6d5859b.
Lemma F_1a400 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a54c : word) = Some W_1a400.
Proof. vm_refl. Qed.
Lemma D_1a400 : decode_any W_1a400 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a404 : bv 32 := 0x02b505b3.
Lemma F_1a404 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a550 : word) = Some W_1a404.
Proof. vm_refl. Qed.
Lemma D_1a404 : decode_any W_1a404 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a408 : bv 32 := 0x00b53023.
Lemma F_1a408 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a554 : word) = Some W_1a408.
Proof. vm_refl. Qed.
Lemma D_1a408 : decode_any W_1a408 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a40c : bv 32 := 0x00009517.
Lemma F_1a40c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a558 : word) = Some W_1a40c.
Proof. vm_refl. Qed.
Lemma D_1a40c : decode_any W_1a40c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a410 : bv 32 := 0x99853503.
Lemma F_1a410 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a55c : word) = Some W_1a410.
Proof. vm_refl. Qed.
Lemma D_1a410 : decode_any W_1a410 = Some (Load SZ8 true 10 10 2456, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a414 : bv 32 := 0x000500a3.
Lemma F_1a414 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a560 : word) = Some W_1a414.
Proof. vm_refl. Qed.
Lemma D_1a414 : decode_any W_1a414 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a418 : bv 32 := 0x00053503.
Lemma F_1a418 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a564 : word) = Some W_1a418.
Proof. vm_refl. Qed.
Lemma D_1a418 : decode_any W_1a418 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a41c : bv 32 := 0x00020593.
Lemma F_1a41c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a568 : word) = Some W_1a41c.
Proof. vm_refl. Qed.
Lemma D_1a41c : decode_any W_1a41c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a420 : bv 32 := 0xfea5b823.
Lemma F_1a420 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a56c : word) = Some W_1a420.
Proof. vm_refl. Qed.
Lemma D_1a420 : decode_any W_1a420 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a424 : bv 32 := 0x00813083.
Lemma F_1a424 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a570 : word) = Some W_1a424.
Proof. vm_refl. Qed.
Lemma D_1a424 : decode_any W_1a424 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a428 : bv 32 := 0x01010113.
Lemma F_1a428 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a574 : word) = Some W_1a428.
Proof. vm_refl. Qed.
Lemma D_1a428 : decode_any W_1a428 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a42c : bv 32 := 0x00008067.
Lemma F_1a42c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a578 : word) = Some W_1a42c.
Proof. vm_refl. Qed.
Lemma D_1a42c : decode_any W_1a42c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a438 : bv 32 := 0xfffff5b7.
Lemma F_1a438 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a584 : word) = Some W_1a438.
Proof. vm_refl. Qed.
Lemma D_1a438 : decode_any W_1a438 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a43c : bv 32 := 0x0015859b.
Lemma F_1a43c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a588 : word) = Some W_1a43c.
Proof. vm_refl. Qed.
Lemma D_1a43c : decode_any W_1a43c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a440 : bv 32 := 0x02b56663.
Lemma F_1a440 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a58c : word) = Some W_1a440.
Proof. vm_refl. Qed.
Lemma D_1a440 : decode_any W_1a440 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a46c : bv 32 := 0x00008067.
Lemma F_1a46c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a5b8 : word) = Some W_1a46c.
Proof. vm_refl. Qed.
Lemma D_1a46c : decode_any W_1a46c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5c0 : bv 32 := 0x1c050463.
Lemma F_1a5c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a70c : word) = Some W_1a5c0.
Proof. vm_refl. Qed.
Lemma D_1a5c0 : decode_any W_1a5c0 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5c4 : bv 32 := 0xfd010113.
Lemma F_1a5c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a710 : word) = Some W_1a5c4.
Proof. vm_refl. Qed.
Lemma D_1a5c4 : decode_any W_1a5c4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5c8 : bv 32 := 0x02113423.
Lemma F_1a5c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a714 : word) = Some W_1a5c8.
Proof. vm_refl. Qed.
Lemma D_1a5c8 : decode_any W_1a5c8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5cc : bv 32 := 0x02813023.
Lemma F_1a5cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a718 : word) = Some W_1a5cc.
Proof. vm_refl. Qed.
Lemma D_1a5cc : decode_any W_1a5cc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5d0 : bv 32 := 0x00913c23.
Lemma F_1a5d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a71c : word) = Some W_1a5d0.
Proof. vm_refl. Qed.
Lemma D_1a5d0 : decode_any W_1a5d0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5d4 : bv 32 := 0x01213823.
Lemma F_1a5d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a720 : word) = Some W_1a5d4.
Proof. vm_refl. Qed.
Lemma D_1a5d4 : decode_any W_1a5d4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5d8 : bv 32 := 0x01313423.
Lemma F_1a5d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a724 : word) = Some W_1a5d8.
Proof. vm_refl. Qed.
Lemma D_1a5d8 : decode_any W_1a5d8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5dc : bv 32 := 0x00050493.
Lemma F_1a5dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a728 : word) = Some W_1a5dc.
Proof. vm_refl. Qed.
Lemma D_1a5dc : decode_any W_1a5dc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5e0 : bv 32 := 0x1ac000ef.
Lemma F_1a5e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a72c : word) = Some W_1a5e0.
Proof. vm_refl. Qed.
Lemma D_1a5e0 : decode_any W_1a5e0 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5e4 : bv 32 := 0x02053583.
Lemma F_1a5e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a730 : word) = Some W_1a5e4.
Proof. vm_refl. Qed.
Lemma D_1a5e4 : decode_any W_1a5e4 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5e8 : bv 32 := 0xffd4c683.
Lemma F_1a5e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a734 : word) = Some W_1a5e8.
Proof. vm_refl. Qed.
Lemma D_1a5e8 : decode_any W_1a5e8 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5ec : bv 32 := 0x00c5d613.
Lemma F_1a5ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a738 : word) = Some W_1a5ec.
Proof. vm_refl. Qed.
Lemma D_1a5ec : decode_any W_1a5ec = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5f0 : bv 32 := 0x01f6f413.
Lemma F_1a5f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a73c : word) = Some W_1a5f0.
Proof. vm_refl. Qed.
Lemma D_1a5f0 : decode_any W_1a5f0 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5f4 : bv 32 := 0x00060e63.
Lemma F_1a5f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a740 : word) = Some W_1a5f4.
Proof. vm_refl. Qed.
Lemma D_1a5f4 : decode_any W_1a5f4 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5f8 : bv 32 := 0x01f5f613.
Lemma F_1a5f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a744 : word) = Some W_1a5f8.
Proof. vm_refl. Qed.
Lemma D_1a5f8 : decode_any W_1a5f8 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a5fc : bv 32 := 0x00061a63.
Lemma F_1a5fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a748 : word) = Some W_1a5fc.
Proof. vm_refl. Qed.
Lemma D_1a5fc : decode_any W_1a5fc = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a600 : bv 32 := 0xfffff637.
Lemma F_1a600 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a74c : word) = Some W_1a600.
Proof. vm_refl. Qed.
Lemma D_1a600 : decode_any W_1a600 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a604 : bv 32 := 0x00c5f633.
Lemma F_1a604 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a750 : word) = Some W_1a604.
Proof. vm_refl. Qed.
Lemma D_1a604 : decode_any W_1a604 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a608 : bv 32 := 0xff060613.
Lemma F_1a608 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a754 : word) = Some W_1a608.
Proof. vm_refl. Qed.
Lemma D_1a608 : decode_any W_1a608 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a60c : bv 32 := 0x0200006f.
Lemma F_1a60c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a758 : word) = Some W_1a60c.
Proof. vm_refl. Qed.
Lemma D_1a60c : decode_any W_1a60c = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a610 : bv 32 := 0x0055d613.
Lemma F_1a610 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a75c : word) = Some W_1a610.
Proof. vm_refl. Qed.
Lemma D_1a610 : decode_any W_1a610 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a614 : bv 32 := 0xffff8717.
Lemma F_1a614 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a760 : word) = Some W_1a614.
Proof. vm_refl. Qed.
Lemma D_1a614 : decode_any W_1a614 = Some (Auipc 14 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a618 : bv 32 := 0x07e67613.
Lemma F_1a618 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a764 : word) = Some W_1a618.
Proof. vm_refl. Qed.
Lemma D_1a618 : decode_any W_1a618 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a61c : bv 32 := 0xcfc70713.
Lemma F_1a61c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a768 : word) = Some W_1a61c.
Proof. vm_refl. Qed.
Lemma D_1a61c : decode_any W_1a61c = Some (OpImm ALU_ADD 14 14 3324, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a620 : bv 32 := 0x00c70633.
Lemma F_1a620 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a76c : word) = Some W_1a620.
Proof. vm_refl. Qed.
Lemma D_1a620 : decode_any W_1a620 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a624 : bv 32 := 0x00065603.
Lemma F_1a624 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a770 : word) = Some W_1a624.
Proof. vm_refl. Qed.
Lemma D_1a624 : decode_any W_1a624 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a628 : bv 32 := 0x00461613.
Lemma F_1a628 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a774 : word) = Some W_1a628.
Proof. vm_refl. Qed.
Lemma D_1a628 : decode_any W_1a628 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a62c : bv 32 := 0x01053703.
Lemma F_1a62c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a778 : word) = Some W_1a62c.
Proof. vm_refl. Qed.
Lemma D_1a62c : decode_any W_1a62c = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a630 : bv 32 := 0x028607b3.
Lemma F_1a630 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a77c : word) = Some W_1a630.
Proof. vm_refl. Qed.
Lemma D_1a630 : decode_any W_1a630 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a634 : bv 32 := 0x0a000813.
Lemma F_1a634 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a780 : word) = Some W_1a634.
Proof. vm_refl. Qed.
Lemma D_1a634 : decode_any W_1a634 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a638 : bv 32 := 0x00c70633.
Lemma F_1a638 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a784 : word) = Some W_1a638.
Proof. vm_refl. Qed.
Lemma D_1a638 : decode_any W_1a638 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a63c : bv 32 := 0x00f607b3.
Lemma F_1a63c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a788 : word) = Some W_1a63c.
Proof. vm_refl. Qed.
Lemma D_1a63c : decode_any W_1a63c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a640 : bv 32 := 0x00c78613.
Lemma F_1a640 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a78c : word) = Some W_1a640.
Proof. vm_refl. Qed.
Lemma D_1a640 : decode_any W_1a640 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a644 : bv 32 := 0x0056d713.
Lemma F_1a644 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a790 : word) = Some W_1a644.
Proof. vm_refl. Qed.
Lemma D_1a644 : decode_any W_1a644 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a648 : bv 32 := 0x0306e663.
Lemma F_1a648 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a794 : word) = Some W_1a648.
Proof. vm_refl. Qed.
Lemma D_1a648 : decode_any W_1a648 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a64c : bv 32 := 0x00500693.
Lemma F_1a64c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a798 : word) = Some W_1a64c.
Proof. vm_refl. Qed.
Lemma D_1a64c : decode_any W_1a64c = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a650 : bv 32 := 0x00d70463.
Lemma F_1a650 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a79c : word) = Some W_1a650.
Proof. vm_refl. Qed.
Lemma D_1a650 : decode_any W_1a650 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a658 : bv 32 := 0x0087e703.
Lemma F_1a658 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7a4 : word) = Some W_1a658.
Proof. vm_refl. Qed.
Lemma D_1a658 : decode_any W_1a658 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a65c : bv 32 := 0x00400693.
Lemma F_1a65c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7a8 : word) = Some W_1a65c.
Proof. vm_refl. Qed.
Lemma D_1a65c : decode_any W_1a65c = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a660 : bv 32 := 0x00e6e463.
Lemma F_1a660 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7ac : word) = Some W_1a660.
Proof. vm_refl. Qed.
Lemma D_1a660 : decode_any W_1a660 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a668 : bv 32 := 0x0077c683.
Lemma F_1a668 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7b4 : word) = Some W_1a668.
Proof. vm_refl. Qed.
Lemma D_1a668 : decode_any W_1a668 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a66c : bv 32 := 0x00068463.
Lemma F_1a66c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7b8 : word) = Some W_1a66c.
Proof. vm_refl. Qed.
Lemma D_1a66c : decode_any W_1a66c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a674 : bv 32 := 0x409606b3.
Lemma F_1a674 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7c0 : word) = Some W_1a674.
Proof. vm_refl. Qed.
Lemma D_1a674 : decode_any W_1a674 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a678 : bv 32 := 0x00e6f463.
Lemma F_1a678 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7c4 : word) = Some W_1a678.
Proof. vm_refl. Qed.
Lemma D_1a678 : decode_any W_1a678 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a680 : bv 32 := 0x40e606b3.
Lemma F_1a680 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7cc : word) = Some W_1a680.
Proof. vm_refl. Qed.
Lemma D_1a680 : decode_any W_1a680 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a684 : bv 32 := 0x0006c683.
Lemma F_1a684 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7d0 : word) = Some W_1a684.
Proof. vm_refl. Qed.
Lemma D_1a684 : decode_any W_1a684 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a688 : bv 32 := 0x00068463.
Lemma F_1a688 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7d4 : word) = Some W_1a688.
Proof. vm_refl. Qed.
Lemma D_1a688 : decode_any W_1a688 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a690 : bv 32 := 0x00064603.
Lemma F_1a690 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7dc : word) = Some W_1a690.
Proof. vm_refl. Qed.
Lemma D_1a690 : decode_any W_1a690 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a694 : bv 32 := 0x00060463.
Lemma F_1a694 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a7e0 : word) = Some W_1a694.
Proof. vm_refl. Qed.
Lemma D_1a694 : decode_any W_1a694 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a78c : bv 32 := 0x00f57593.
Lemma F_1a78c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a8d8 : word) = Some W_1a78c.
Proof. vm_refl. Qed.
Lemma D_1a78c : decode_any W_1a78c = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a790 : bv 32 := 0x00058463.
Lemma F_1a790 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a8dc : word) = Some W_1a790.
Proof. vm_refl. Qed.
Lemma D_1a790 : decode_any W_1a790 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a798 : bv 32 := 0xffc54603.
Lemma F_1a798 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a8e4 : word) = Some W_1a798.
Proof. vm_refl. Qed.
Lemma D_1a798 : decode_any W_1a798 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a79c : bv 32 := 0xffd54683.
Lemma F_1a79c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a8e8 : word) = Some W_1a79c.
Proof. vm_refl. Qed.
Lemma D_1a79c : decode_any W_1a79c = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7a0 : bv 32 := 0xffe55583.
Lemma F_1a7a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a8ec : word) = Some W_1a7a0.
Proof. vm_refl. Qed.
Lemma D_1a7a0 : decode_any W_1a7a0 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7a4 : bv 32 := 0x00060e63.
Lemma F_1a7a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a8f0 : word) = Some W_1a7a4.
Proof. vm_refl. Qed.
Lemma D_1a7a4 : decode_any W_1a7a4 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7c0 : bv 32 := 0x00459613.
Lemma F_1a7c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a90c : word) = Some W_1a7c0.
Proof. vm_refl. Qed.
Lemma D_1a7c0 : decode_any W_1a7c0 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7c4 : bv 32 := 0x40c50633.
Lemma F_1a7c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a910 : word) = Some W_1a7c4.
Proof. vm_refl. Qed.
Lemma D_1a7c4 : decode_any W_1a7c4 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7c8 : bv 32 := 0xff063503.
Lemma F_1a7c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a914 : word) = Some W_1a7c8.
Proof. vm_refl. Qed.
Lemma D_1a7c8 : decode_any W_1a7c8 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7cc : bv 32 := 0x01053703.
Lemma F_1a7cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a918 : word) = Some W_1a7cc.
Proof. vm_refl. Qed.
Lemma D_1a7cc : decode_any W_1a7cc = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7d0 : bv 32 := 0xff060613.
Lemma F_1a7d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a91c : word) = Some W_1a7d0.
Proof. vm_refl. Qed.
Lemma D_1a7d0 : decode_any W_1a7d0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7d4 : bv 32 := 0x01f6f693.
Lemma F_1a7d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a920 : word) = Some W_1a7d4.
Proof. vm_refl. Qed.
Lemma D_1a7d4 : decode_any W_1a7d4 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7d8 : bv 32 := 0x00c70463.
Lemma F_1a7d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a924 : word) = Some W_1a7d8.
Proof. vm_refl. Qed.
Lemma D_1a7d8 : decode_any W_1a7d8 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7e0 : bv 32 := 0x02053603.
Lemma F_1a7e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a92c : word) = Some W_1a7e0.
Proof. vm_refl. Qed.
Lemma D_1a7e0 : decode_any W_1a7e0 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7e4 : bv 32 := 0x01f67713.
Lemma F_1a7e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a930 : word) = Some W_1a7e4.
Proof. vm_refl. Qed.
Lemma D_1a7e4 : decode_any W_1a7e4 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7e8 : bv 32 := 0x00d77463.
Lemma F_1a7e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a934 : word) = Some W_1a7e8.
Proof. vm_refl. Qed.
Lemma D_1a7e8 : decode_any W_1a7e8 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7f0 : bv 32 := 0x01852783.
Lemma F_1a7f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a93c : word) = Some W_1a7f0.
Proof. vm_refl. Qed.
Lemma D_1a7f0 : decode_any W_1a7f0 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7f4 : bv 32 := 0x00100713.
Lemma F_1a7f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a940 : word) = Some W_1a7f4.
Proof. vm_refl. Qed.
Lemma D_1a7f4 : decode_any W_1a7f4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7f8 : bv 32 := 0x00d7173b.
Lemma F_1a7f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a944 : word) = Some W_1a7f8.
Proof. vm_refl. Qed.
Lemma D_1a7f8 : decode_any W_1a7f8 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a7fc : bv 32 := 0x00e7f7b3.
Lemma F_1a7fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a948 : word) = Some W_1a7fc.
Proof. vm_refl. Qed.
Lemma D_1a7fc : decode_any W_1a7fc = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a800 : bv 32 := 0x00078463.
Lemma F_1a800 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a94c : word) = Some W_1a800.
Proof. vm_refl. Qed.
Lemma D_1a800 : decode_any W_1a800 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a808 : bv 32 := 0x01c52783.
Lemma F_1a808 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a954 : word) = Some W_1a808.
Proof. vm_refl. Qed.
Lemma D_1a808 : decode_any W_1a808 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a80c : bv 32 := 0x00e7f733.
Lemma F_1a80c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a958 : word) = Some W_1a80c.
Proof. vm_refl. Qed.
Lemma D_1a80c : decode_any W_1a80c = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a810 : bv 32 := 0x00070463.
Lemma F_1a810 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a95c : word) = Some W_1a810.
Proof. vm_refl. Qed.
Lemma D_1a810 : decode_any W_1a810 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a818 : bv 32 := 0xfffff737.
Lemma F_1a818 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a964 : word) = Some W_1a818.
Proof. vm_refl. Qed.
Lemma D_1a818 : decode_any W_1a818 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a81c : bv 32 := 0x0007a797.
Lemma F_1a81c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a968 : word) = Some W_1a81c.
Proof. vm_refl. Qed.
Lemma D_1a81c : decode_any W_1a81c = Some (Auipc 15 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a820 : bv 32 := 0x00e57733.
Lemma F_1a820 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a96c : word) = Some W_1a820.
Proof. vm_refl. Qed.
Lemma D_1a820 : decode_any W_1a820 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a824 : bv 32 := 0x00073703.
Lemma F_1a824 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a970 : word) = Some W_1a824.
Proof. vm_refl. Qed.
Lemma D_1a824 : decode_any W_1a824 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a828 : bv 32 := 0xc087b783.
Lemma F_1a828 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a974 : word) = Some W_1a828.
Proof. vm_refl. Qed.
Lemma D_1a828 : decode_any W_1a828 = Some (Load SZ8 true 15 15 3080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a82c : bv 32 := 0x00f70463.
Lemma F_1a82c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a978 : word) = Some W_1a82c.
Proof. vm_refl. Qed.
Lemma D_1a82c : decode_any W_1a82c = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a834 : bv 32 := 0x03461713.
Lemma F_1a834 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a980 : word) = Some W_1a834.
Proof. vm_refl. Qed.
Lemma D_1a834 : decode_any W_1a834 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a838 : bv 32 := 0x03a75713.
Lemma F_1a838 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a984 : word) = Some W_1a838.
Proof. vm_refl. Qed.
Lemma D_1a838 : decode_any W_1a838 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a83c : bv 32 := 0x02f00793.
Lemma F_1a83c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a988 : word) = Some W_1a83c.
Proof. vm_refl. Qed.
Lemma D_1a83c : decode_any W_1a83c = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a840 : bv 32 := 0x02e7ea63.
Lemma F_1a840 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a98c : word) = Some W_1a840.
Proof. vm_refl. Qed.
Lemma D_1a840 : decode_any W_1a840 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a844 : bv 32 := 0x00171713.
Lemma F_1a844 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a990 : word) = Some W_1a844.
Proof. vm_refl. Qed.
Lemma D_1a844 : decode_any W_1a844 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a848 : bv 32 := 0xffff8797.
Lemma F_1a848 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a994 : word) = Some W_1a848.
Proof. vm_refl. Qed.
Lemma D_1a848 : decode_any W_1a848 = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a84c : bv 32 := 0xac878793.
Lemma F_1a84c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a998 : word) = Some W_1a84c.
Proof. vm_refl. Qed.
Lemma D_1a84c : decode_any W_1a84c = Some (OpImm ALU_ADD 15 15 2760, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a850 : bv 32 := 0x00e78733.
Lemma F_1a850 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a99c : word) = Some W_1a850.
Proof. vm_refl. Qed.
Lemma D_1a850 : decode_any W_1a850 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a854 : bv 32 := 0x00075703.
Lemma F_1a854 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9a0 : word) = Some W_1a854.
Proof. vm_refl. Qed.
Lemma D_1a854 : decode_any W_1a854 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a858 : bv 32 := 0x02d707b3.
Lemma F_1a858 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9a4 : word) = Some W_1a858.
Proof. vm_refl. Qed.
Lemma D_1a858 : decode_any W_1a858 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a85c : bv 32 := 0x00f5f463.
Lemma F_1a85c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9a8 : word) = Some W_1a85c.
Proof. vm_refl. Qed.
Lemma D_1a85c : decode_any W_1a85c = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a864 : bv 32 := 0x00168693.
Lemma F_1a864 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9b0 : word) = Some W_1a864.
Proof. vm_refl. Qed.
Lemma D_1a864 : decode_any W_1a864 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a868 : bv 32 := 0x02e686b3.
Lemma F_1a868 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9b4 : word) = Some W_1a868.
Proof. vm_refl. Qed.
Lemma D_1a868 : decode_any W_1a868 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a86c : bv 32 := 0x00d5f863.
Lemma F_1a86c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9b8 : word) = Some W_1a86c.
Proof. vm_refl. Qed.
Lemma D_1a86c : decode_any W_1a86c = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a870 : bv 32 := 0x0100006f.
Lemma F_1a870 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9bc : word) = Some W_1a870.
Proof. vm_refl. Qed.
Lemma D_1a870 : decode_any W_1a870 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a874 : bv 32 := 0x03f00693.
Lemma F_1a874 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9c0 : word) = Some W_1a874.
Proof. vm_refl. Qed.
Lemma D_1a874 : decode_any W_1a874 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a878 : bv 32 := 0x00d70463.
Lemma F_1a878 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9c4 : word) = Some W_1a878.
Proof. vm_refl. Qed.
Lemma D_1a878 : decode_any W_1a878 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a880 : bv 32 := 0x00c65613.
Lemma F_1a880 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9cc : word) = Some W_1a880.
Proof. vm_refl. Qed.
Lemma D_1a880 : decode_any W_1a880 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a884 : bv 32 := 0x00060a63.
Lemma F_1a884 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9d0 : word) = Some W_1a884.
Proof. vm_refl. Qed.
Lemma D_1a884 : decode_any W_1a884 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a888 : bv 32 := 0x00861613.
Lemma F_1a888 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9d4 : word) = Some W_1a888.
Proof. vm_refl. Qed.
Lemma D_1a888 : decode_any W_1a888 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a88c : bv 32 := 0xfff60613.
Lemma F_1a88c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9d8 : word) = Some W_1a88c.
Proof. vm_refl. Qed.
Lemma D_1a88c : decode_any W_1a88c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a890 : bv 32 := 0x00b67463.
Lemma F_1a890 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9dc : word) = Some W_1a890.
Proof. vm_refl. Qed.
Lemma D_1a890 : decode_any W_1a890 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a898 : bv 32 := 0x00008067.
Lemma F_1a898 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1a9e4 : word) = Some W_1a898.
Proof. vm_refl. Qed.
Lemma D_1a898 : decode_any W_1a898 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac1c : bv 32 := 0x00072503.
Lemma F_1ac1c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad68 : word) = Some W_1ac1c.
Proof. vm_refl. Qed.
Lemma D_1ac1c : decode_any W_1ac1c = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac20 : bv 32 := 0x00b56633.
Lemma F_1ac20 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad6c : word) = Some W_1ac20.
Proof. vm_refl. Qed.
Lemma D_1ac20 : decode_any W_1ac20 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac24 : bv 32 := 0x160726af.
Lemma F_1ac24 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad70 : word) = Some W_1ac24.
Proof. vm_refl. Qed.
Lemma D_1ac24 : decode_any W_1ac24 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac28 : bv 32 := 0x00a69663.
Lemma F_1ac28 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad74 : word) = Some W_1ac28.
Proof. vm_refl. Qed.
Lemma D_1ac28 : decode_any W_1ac28 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac2c : bv 32 := 0x1ec727af.
Lemma F_1ac2c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad78 : word) = Some W_1ac2c.
Proof. vm_refl. Qed.
Lemma D_1ac2c : decode_any W_1ac2c = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac30 : bv 32 := 0xfe079ae3.
Lemma F_1ac30 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad7c : word) = Some W_1ac30.
Proof. vm_refl. Qed.
Lemma D_1ac30 : decode_any W_1ac30 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac34 : bv 32 := 0x0006869b.
Lemma F_1ac34 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad80 : word) = Some W_1ac34.
Proof. vm_refl. Qed.
Lemma D_1ac34 : decode_any W_1ac34 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac38 : bv 32 := 0xfea692e3.
Lemma F_1ac38 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1ad84 : word) = Some W_1ac38.
Proof. vm_refl. Qed.
Lemma D_1ac38 : decode_any W_1ac38 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.
