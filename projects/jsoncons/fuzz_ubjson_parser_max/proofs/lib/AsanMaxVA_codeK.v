(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_8c16c : bv 32 := 0x00155593.
Lemma F_8c16c : fetch_word Asan.M.loaded_segments (0x8c16c : word) = Some W_8c16c.
Proof. vm_refl. Qed.
Lemma D_8c16c : decode_any W_8c16c = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c170 : bv 32 := 0x55555637.
Lemma F_8c170 : fetch_word Asan.M.loaded_segments (0x8c170 : word) = Some W_8c170.
Proof. vm_refl. Qed.
Lemma D_8c170 : decode_any W_8c170 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c174 : bv 32 := 0x333336b7.
Lemma F_8c174 : fetch_word Asan.M.loaded_segments (0x8c174 : word) = Some W_8c174.
Proof. vm_refl. Qed.
Lemma D_8c174 : decode_any W_8c174 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c178 : bv 32 := 0x0f0f1737.
Lemma F_8c178 : fetch_word Asan.M.loaded_segments (0x8c178 : word) = Some W_8c178.
Proof. vm_refl. Qed.
Lemma D_8c178 : decode_any W_8c178 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c17c : bv 32 := 0x010107b7.
Lemma F_8c17c : fetch_word Asan.M.loaded_segments (0x8c17c : word) = Some W_8c17c.
Proof. vm_refl. Qed.
Lemma D_8c17c : decode_any W_8c17c = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c180 : bv 32 := 0x00b56533.
Lemma F_8c180 : fetch_word Asan.M.loaded_segments (0x8c180 : word) = Some W_8c180.
Proof. vm_refl. Qed.
Lemma D_8c180 : decode_any W_8c180 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c184 : bv 32 := 0x5556059b.
Lemma F_8c184 : fetch_word Asan.M.loaded_segments (0x8c184 : word) = Some W_8c184.
Proof. vm_refl. Qed.
Lemma D_8c184 : decode_any W_8c184 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c188 : bv 32 := 0x3336861b.
Lemma F_8c188 : fetch_word Asan.M.loaded_segments (0x8c188 : word) = Some W_8c188.
Proof. vm_refl. Qed.
Lemma D_8c188 : decode_any W_8c188 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c18c : bv 32 := 0xf0f7069b.
Lemma F_8c18c : fetch_word Asan.M.loaded_segments (0x8c18c : word) = Some W_8c18c.
Proof. vm_refl. Qed.
Lemma D_8c18c : decode_any W_8c18c = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c190 : bv 32 := 0x1017871b.
Lemma F_8c190 : fetch_word Asan.M.loaded_segments (0x8c190 : word) = Some W_8c190.
Proof. vm_refl. Qed.
Lemma D_8c190 : decode_any W_8c190 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c194 : bv 32 := 0x00255793.
Lemma F_8c194 : fetch_word Asan.M.loaded_segments (0x8c194 : word) = Some W_8c194.
Proof. vm_refl. Qed.
Lemma D_8c194 : decode_any W_8c194 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c198 : bv 32 := 0x00f56533.
Lemma F_8c198 : fetch_word Asan.M.loaded_segments (0x8c198 : word) = Some W_8c198.
Proof. vm_refl. Qed.
Lemma D_8c198 : decode_any W_8c198 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c19c : bv 32 := 0x02059793.
Lemma F_8c19c : fetch_word Asan.M.loaded_segments (0x8c19c : word) = Some W_8c19c.
Proof. vm_refl. Qed.
Lemma D_8c19c : decode_any W_8c19c = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1a0 : bv 32 := 0x00f585b3.
Lemma F_8c1a0 : fetch_word Asan.M.loaded_segments (0x8c1a0 : word) = Some W_8c1a0.
Proof. vm_refl. Qed.
Lemma D_8c1a0 : decode_any W_8c1a0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1a4 : bv 32 := 0x02061793.
Lemma F_8c1a4 : fetch_word Asan.M.loaded_segments (0x8c1a4 : word) = Some W_8c1a4.
Proof. vm_refl. Qed.
Lemma D_8c1a4 : decode_any W_8c1a4 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1a8 : bv 32 := 0x00f60633.
Lemma F_8c1a8 : fetch_word Asan.M.loaded_segments (0x8c1a8 : word) = Some W_8c1a8.
Proof. vm_refl. Qed.
Lemma D_8c1a8 : decode_any W_8c1a8 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1ac : bv 32 := 0x02069793.
Lemma F_8c1ac : fetch_word Asan.M.loaded_segments (0x8c1ac : word) = Some W_8c1ac.
Proof. vm_refl. Qed.
Lemma D_8c1ac : decode_any W_8c1ac = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1b0 : bv 32 := 0x00f686b3.
Lemma F_8c1b0 : fetch_word Asan.M.loaded_segments (0x8c1b0 : word) = Some W_8c1b0.
Proof. vm_refl. Qed.
Lemma D_8c1b0 : decode_any W_8c1b0 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1b4 : bv 32 := 0x02071793.
Lemma F_8c1b4 : fetch_word Asan.M.loaded_segments (0x8c1b4 : word) = Some W_8c1b4.
Proof. vm_refl. Qed.
Lemma D_8c1b4 : decode_any W_8c1b4 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1b8 : bv 32 := 0x00f70733.
Lemma F_8c1b8 : fetch_word Asan.M.loaded_segments (0x8c1b8 : word) = Some W_8c1b8.
Proof. vm_refl. Qed.
Lemma D_8c1b8 : decode_any W_8c1b8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1bc : bv 32 := 0x00455793.
Lemma F_8c1bc : fetch_word Asan.M.loaded_segments (0x8c1bc : word) = Some W_8c1bc.
Proof. vm_refl. Qed.
Lemma D_8c1bc : decode_any W_8c1bc = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1c0 : bv 32 := 0x00f56533.
Lemma F_8c1c0 : fetch_word Asan.M.loaded_segments (0x8c1c0 : word) = Some W_8c1c0.
Proof. vm_refl. Qed.
Lemma D_8c1c0 : decode_any W_8c1c0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1c4 : bv 32 := 0x00855793.
Lemma F_8c1c4 : fetch_word Asan.M.loaded_segments (0x8c1c4 : word) = Some W_8c1c4.
Proof. vm_refl. Qed.
Lemma D_8c1c4 : decode_any W_8c1c4 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1c8 : bv 32 := 0x00f56533.
Lemma F_8c1c8 : fetch_word Asan.M.loaded_segments (0x8c1c8 : word) = Some W_8c1c8.
Proof. vm_refl. Qed.
Lemma D_8c1c8 : decode_any W_8c1c8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1cc : bv 32 := 0x01055793.
Lemma F_8c1cc : fetch_word Asan.M.loaded_segments (0x8c1cc : word) = Some W_8c1cc.
Proof. vm_refl. Qed.
Lemma D_8c1cc : decode_any W_8c1cc = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1d0 : bv 32 := 0x00f56533.
Lemma F_8c1d0 : fetch_word Asan.M.loaded_segments (0x8c1d0 : word) = Some W_8c1d0.
Proof. vm_refl. Qed.
Lemma D_8c1d0 : decode_any W_8c1d0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1d4 : bv 32 := 0x02055793.
Lemma F_8c1d4 : fetch_word Asan.M.loaded_segments (0x8c1d4 : word) = Some W_8c1d4.
Proof. vm_refl. Qed.
Lemma D_8c1d4 : decode_any W_8c1d4 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1d8 : bv 32 := 0x00f56533.
Lemma F_8c1d8 : fetch_word Asan.M.loaded_segments (0x8c1d8 : word) = Some W_8c1d8.
Proof. vm_refl. Qed.
Lemma D_8c1d8 : decode_any W_8c1d8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1dc : bv 32 := 0xfff54513.
Lemma F_8c1dc : fetch_word Asan.M.loaded_segments (0x8c1dc : word) = Some W_8c1dc.
Proof. vm_refl. Qed.
Lemma D_8c1dc : decode_any W_8c1dc = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1e0 : bv 32 := 0x00155793.
Lemma F_8c1e0 : fetch_word Asan.M.loaded_segments (0x8c1e0 : word) = Some W_8c1e0.
Proof. vm_refl. Qed.
Lemma D_8c1e0 : decode_any W_8c1e0 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1e4 : bv 32 := 0x00b7f5b3.
Lemma F_8c1e4 : fetch_word Asan.M.loaded_segments (0x8c1e4 : word) = Some W_8c1e4.
Proof. vm_refl. Qed.
Lemma D_8c1e4 : decode_any W_8c1e4 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1e8 : bv 32 := 0x40b50533.
Lemma F_8c1e8 : fetch_word Asan.M.loaded_segments (0x8c1e8 : word) = Some W_8c1e8.
Proof. vm_refl. Qed.
Lemma D_8c1e8 : decode_any W_8c1e8 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1ec : bv 32 := 0x00c575b3.
Lemma F_8c1ec : fetch_word Asan.M.loaded_segments (0x8c1ec : word) = Some W_8c1ec.
Proof. vm_refl. Qed.
Lemma D_8c1ec : decode_any W_8c1ec = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1f0 : bv 32 := 0x00255513.
Lemma F_8c1f0 : fetch_word Asan.M.loaded_segments (0x8c1f0 : word) = Some W_8c1f0.
Proof. vm_refl. Qed.
Lemma D_8c1f0 : decode_any W_8c1f0 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1f4 : bv 32 := 0x00c57533.
Lemma F_8c1f4 : fetch_word Asan.M.loaded_segments (0x8c1f4 : word) = Some W_8c1f4.
Proof. vm_refl. Qed.
Lemma D_8c1f4 : decode_any W_8c1f4 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1f8 : bv 32 := 0x00a58533.
Lemma F_8c1f8 : fetch_word Asan.M.loaded_segments (0x8c1f8 : word) = Some W_8c1f8.
Proof. vm_refl. Qed.
Lemma D_8c1f8 : decode_any W_8c1f8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c1fc : bv 32 := 0x00455593.
Lemma F_8c1fc : fetch_word Asan.M.loaded_segments (0x8c1fc : word) = Some W_8c1fc.
Proof. vm_refl. Qed.
Lemma D_8c1fc : decode_any W_8c1fc = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c200 : bv 32 := 0x00b50533.
Lemma F_8c200 : fetch_word Asan.M.loaded_segments (0x8c200 : word) = Some W_8c200.
Proof. vm_refl. Qed.
Lemma D_8c200 : decode_any W_8c200 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c204 : bv 32 := 0x00d57533.
Lemma F_8c204 : fetch_word Asan.M.loaded_segments (0x8c204 : word) = Some W_8c204.
Proof. vm_refl. Qed.
Lemma D_8c204 : decode_any W_8c204 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c208 : bv 32 := 0x02e50533.
Lemma F_8c208 : fetch_word Asan.M.loaded_segments (0x8c208 : word) = Some W_8c208.
Proof. vm_refl. Qed.
Lemma D_8c208 : decode_any W_8c208 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c20c : bv 32 := 0x03855513.
Lemma F_8c20c : fetch_word Asan.M.loaded_segments (0x8c20c : word) = Some W_8c20c.
Proof. vm_refl. Qed.
Lemma D_8c20c : decode_any W_8c20c = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c210 : bv 32 := 0x40a0053b.
Lemma F_8c210 : fetch_word Asan.M.loaded_segments (0x8c210 : word) = Some W_8c210.
Proof. vm_refl. Qed.
Lemma D_8c210 : decode_any W_8c210 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c214 : bv 32 := 0xfff00593.
Lemma F_8c214 : fetch_word Asan.M.loaded_segments (0x8c214 : word) = Some W_8c214.
Proof. vm_refl. Qed.
Lemma D_8c214 : decode_any W_8c214 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c218 : bv 32 := 0x00a59533.
Lemma F_8c218 : fetch_word Asan.M.loaded_segments (0x8c218 : word) = Some W_8c218.
Proof. vm_refl. Qed.
Lemma D_8c218 : decode_any W_8c218 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c21c : bv 32 := 0xfff54513.
Lemma F_8c21c : fetch_word Asan.M.loaded_segments (0x8c21c : word) = Some W_8c21c.
Proof. vm_refl. Qed.
Lemma D_8c21c : decode_any W_8c21c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
