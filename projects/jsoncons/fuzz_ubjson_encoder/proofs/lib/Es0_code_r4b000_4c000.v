(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9b98c : bv 32 := 0x01293023.
Lemma F_9b98c : fetch_word Plain.M.loaded_segments (0x9b9d8 : word) = Some W_9b98c.
Proof. vm_refl. Qed.
Lemma D_9b98c : decode_any W_9b98c = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b990 : bv 32 := 0x00040513.
Lemma F_9b990 : fetch_word Plain.M.loaded_segments (0x9b9dc : word) = Some W_9b990.
Proof. vm_refl. Qed.
Lemma D_9b990 : decode_any W_9b990 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b994 : bv 32 := 0x16c130ef.
Lemma F_9b994 : fetch_word Plain.M.loaded_segments (0x9b9e0 : word) = Some W_9b994.
Proof. vm_refl. Qed.
Lemma D_9b994 : decode_any W_9b994 = Some (Jal 1 78188, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b998 : bv 32 := 0x04054a63.
Lemma F_9b998 : fetch_word Plain.M.loaded_segments (0x9b9e4 : word) = Some W_9b998.
Proof. vm_refl. Qed.
Lemma D_9b998 : decode_any W_9b998 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b99c : bv 32 := 0x00051663.
Lemma F_9b99c : fetch_word Plain.M.loaded_segments (0x9b9e8 : word) = Some W_9b99c.
Proof. vm_refl. Qed.
Lemma D_9b99c : decode_any W_9b99c = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9a0 : bv 32 := 0x00100513.
Lemma F_9b9a0 : fetch_word Plain.M.loaded_segments (0x9b9ec : word) = Some W_9b9a0.
Proof. vm_refl. Qed.
Lemma D_9b9a0 : decode_any W_9b9a0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9a4 : bv 32 := 0x00a48023.
Lemma F_9b9a4 : fetch_word Plain.M.loaded_segments (0x9b9f0 : word) = Some W_9b9a4.
Proof. vm_refl. Qed.
Lemma D_9b9a4 : decode_any W_9b9a4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9a8 : bv 32 := 0x00200513.
Lemma F_9b9a8 : fetch_word Plain.M.loaded_segments (0x9b9f4 : word) = Some W_9b9a8.
Proof. vm_refl. Qed.
Lemma D_9b9a8 : decode_any W_9b9a8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9ac : bv 32 := 0x0004f597.
Lemma F_9b9ac : fetch_word Plain.M.loaded_segments (0x9b9f8 : word) = Some W_9b9ac.
Proof. vm_refl. Qed.
Lemma D_9b9ac : decode_any W_9b9ac = Some (Auipc 11 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9b0 : bv 32 := 0x02a92423.
Lemma F_9b9b0 : fetch_word Plain.M.loaded_segments (0x9b9fc : word) = Some W_9b9b0.
Proof. vm_refl. Qed.
Lemma D_9b9b0 : decode_any W_9b9b0 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9b4 : bv 32 := 0x06000893.
Lemma F_9b9b4 : fetch_word Plain.M.loaded_segments (0x9ba00 : word) = Some W_9b9b4.
Proof. vm_refl. Qed.
Lemma D_9b9b4 : decode_any W_9b9b4 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9b8 : bv 32 := 0x65058513.
Lemma F_9b9b8 : fetch_word Plain.M.loaded_segments (0x9ba04 : word) = Some W_9b9b8.
Proof. vm_refl. Qed.
Lemma D_9b9b8 : decode_any W_9b9b8 = Some (OpImm ALU_ADD 10 11 1616, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9bc : bv 32 := 0x03848593.
Lemma F_9b9bc : fetch_word Plain.M.loaded_segments (0x9ba08 : word) = Some W_9b9bc.
Proof. vm_refl. Qed.
Lemma D_9b9bc : decode_any W_9b9bc = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9c0 : bv 32 := 0x00000073.
Lemma F_9b9c0 : fetch_word Plain.M.loaded_segments (0x9ba0c : word) = Some W_9b9c0.
Proof. vm_refl. Qed.
Lemma D_9b9c0 : decode_any W_9b9c0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9b9c0 : is_ecall W_9b9c0 = true.
Proof. reflexivity. Qed.

Definition W_9b9c4 : bv 32 := 0x07890613.
Lemma F_9b9c4 : fetch_word Plain.M.loaded_segments (0x9ba10 : word) = Some W_9b9c4.
Proof. vm_refl. Qed.
Lemma D_9b9c4 : decode_any W_9b9c4 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9c8 : bv 32 := 0x02a92023.
Lemma F_9b9c8 : fetch_word Plain.M.loaded_segments (0x9ba14 : word) = Some W_9b9c8.
Proof. vm_refl. Qed.
Lemma D_9b9c8 : decode_any W_9b9c8 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9cc : bv 32 := 0x08b93c23.
Lemma F_9b9cc : fetch_word Plain.M.loaded_segments (0x9ba18 : word) = Some W_9b9cc.
Proof. vm_refl. Qed.
Lemma D_9b9cc : decode_any W_9b9cc = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9d0 : bv 32 := 0x06c93c23.
Lemma F_9b9d0 : fetch_word Plain.M.loaded_segments (0x9ba1c : word) = Some W_9b9d0.
Proof. vm_refl. Qed.
Lemma D_9b9d0 : decode_any W_9b9d0 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9d4 : bv 32 := 0x00050517.
Lemma F_9b9d4 : fetch_word Plain.M.loaded_segments (0x9ba20 : word) = Some W_9b9d4.
Proof. vm_refl. Qed.
Lemma D_9b9d4 : decode_any W_9b9d4 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9d8 : bv 32 := 0x89853503.
Lemma F_9b9d8 : fetch_word Plain.M.loaded_segments (0x9ba24 : word) = Some W_9b9d8.
Proof. vm_refl. Qed.
Lemma D_9b9d8 : decode_any W_9b9d8 = Some (Load SZ8 true 10 10 2200, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9dc : bv 32 := 0x01293423.
Lemma F_9b9dc : fetch_word Plain.M.loaded_segments (0x9ba28 : word) = Some W_9b9dc.
Proof. vm_refl. Qed.
Lemma D_9b9dc : decode_any W_9b9dc = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9e0 : bv 32 := 0x01293823.
Lemma F_9b9e0 : fetch_word Plain.M.loaded_segments (0x9ba2c : word) = Some W_9b9e0.
Proof. vm_refl. Qed.
Lemma D_9b9e0 : decode_any W_9b9e0 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9e4 : bv 32 := 0x00a93c23.
Lemma F_9b9e4 : fetch_word Plain.M.loaded_segments (0x9ba30 : word) = Some W_9b9e4.
Proof. vm_refl. Qed.
Lemma D_9b9e4 : decode_any W_9b9e4 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9e8 : bv 32 := 0x0080006f.
Lemma F_9b9e8 : fetch_word Plain.M.loaded_segments (0x9ba34 : word) = Some W_9b9e8.
Proof. vm_refl. Qed.
Lemma D_9b9e8 : decode_any W_9b9e8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9f0 : bv 32 := 0x03813083.
Lemma F_9b9f0 : fetch_word Plain.M.loaded_segments (0x9ba3c : word) = Some W_9b9f0.
Proof. vm_refl. Qed.
Lemma D_9b9f0 : decode_any W_9b9f0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9f4 : bv 32 := 0x03013403.
Lemma F_9b9f4 : fetch_word Plain.M.loaded_segments (0x9ba40 : word) = Some W_9b9f4.
Proof. vm_refl. Qed.
Lemma D_9b9f4 : decode_any W_9b9f4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9f8 : bv 32 := 0x02813483.
Lemma F_9b9f8 : fetch_word Plain.M.loaded_segments (0x9ba44 : word) = Some W_9b9f8.
Proof. vm_refl. Qed.
Lemma D_9b9f8 : decode_any W_9b9f8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9fc : bv 32 := 0x02013903.
Lemma F_9b9fc : fetch_word Plain.M.loaded_segments (0x9ba48 : word) = Some W_9b9fc.
Proof. vm_refl. Qed.
Lemma D_9b9fc : decode_any W_9b9fc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ba00 : bv 32 := 0x01813983.
Lemma F_9ba00 : fetch_word Plain.M.loaded_segments (0x9ba4c : word) = Some W_9ba00.
Proof. vm_refl. Qed.
Lemma D_9ba00 : decode_any W_9ba00 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ba04 : bv 32 := 0x01013a03.
Lemma F_9ba04 : fetch_word Plain.M.loaded_segments (0x9ba50 : word) = Some W_9ba04.
Proof. vm_refl. Qed.
Lemma D_9ba04 : decode_any W_9ba04 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ba08 : bv 32 := 0x00813a83.
Lemma F_9ba08 : fetch_word Plain.M.loaded_segments (0x9ba54 : word) = Some W_9ba08.
Proof. vm_refl. Qed.
Lemma D_9ba08 : decode_any W_9ba08 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ba0c : bv 32 := 0x04010113.
Lemma F_9ba0c : fetch_word Plain.M.loaded_segments (0x9ba58 : word) = Some W_9ba0c.
Proof. vm_refl. Qed.
Lemma D_9ba0c : decode_any W_9ba0c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ba10 : bv 32 := 0x00008067.
Lemma F_9ba10 : fetch_word Plain.M.loaded_segments (0x9ba5c : word) = Some W_9ba10.
Proof. vm_refl. Qed.
Lemma D_9ba10 : decode_any W_9ba10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bab4 : bv 32 := 0x00050593.
Lemma F_9bab4 : fetch_word Plain.M.loaded_segments (0x9bb00 : word) = Some W_9bab4.
Proof. vm_refl. Qed.
Lemma D_9bab4 : decode_any W_9bab4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bab8 : bv 32 := 0x05e00893.
Lemma F_9bab8 : fetch_word Plain.M.loaded_segments (0x9bb04 : word) = Some W_9bab8.
Proof. vm_refl. Qed.
Lemma D_9bab8 : decode_any W_9bab8 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_9babc : bv 32 := 0x00000073.
Lemma F_9babc : fetch_word Plain.M.loaded_segments (0x9bb08 : word) = Some W_9babc.
Proof. vm_refl. Qed.
Lemma D_9babc : decode_any W_9babc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9babc : is_ecall W_9babc = true.
Proof. reflexivity. Qed.

Definition W_9bd60 : bv 32 := 0xfe010113.
Lemma F_9bd60 : fetch_word Plain.M.loaded_segments (0x9bdac : word) = Some W_9bd60.
Proof. vm_refl. Qed.
Lemma D_9bd60 : decode_any W_9bd60 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd64 : bv 32 := 0x00113c23.
Lemma F_9bd64 : fetch_word Plain.M.loaded_segments (0x9bdb0 : word) = Some W_9bd64.
Proof. vm_refl. Qed.
Lemma D_9bd64 : decode_any W_9bd64 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd68 : bv 32 := 0x00813823.
Lemma F_9bd68 : fetch_word Plain.M.loaded_segments (0x9bdb4 : word) = Some W_9bd68.
Proof. vm_refl. Qed.
Lemma D_9bd68 : decode_any W_9bd68 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd6c : bv 32 := 0x00913423.
Lemma F_9bd6c : fetch_word Plain.M.loaded_segments (0x9bdb8 : word) = Some W_9bd6c.
Proof. vm_refl. Qed.
Lemma D_9bd6c : decode_any W_9bd6c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd70 : bv 32 := 0x0001c517.
Lemma F_9bd70 : fetch_word Plain.M.loaded_segments (0x9bdbc : word) = Some W_9bd70.
Proof. vm_refl. Qed.
Lemma D_9bd70 : decode_any W_9bd70 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd74 : bv 32 := 0x0001c597.
Lemma F_9bd74 : fetch_word Plain.M.loaded_segments (0x9bdc0 : word) = Some W_9bd74.
Proof. vm_refl. Qed.
Lemma D_9bd74 : decode_any W_9bd74 = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd78 : bv 32 := 0x4ec53503.
Lemma F_9bd78 : fetch_word Plain.M.loaded_segments (0x9bdc4 : word) = Some W_9bd78.
Proof. vm_refl. Qed.
Lemma D_9bd78 : decode_any W_9bd78 = Some (Load SZ8 true 10 10 1260, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd7c : bv 32 := 0x4f05b403.
Lemma F_9bd7c : fetch_word Plain.M.loaded_segments (0x9bdc8 : word) = Some W_9bd7c.
Proof. vm_refl. Qed.
Lemma D_9bd7c : decode_any W_9bd7c = Some (Load SZ8 true 8 11 1264, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd80 : bv 32 := 0x00a47c63.
Lemma F_9bd80 : fetch_word Plain.M.loaded_segments (0x9bdcc : word) = Some W_9bd80.
Proof. vm_refl. Qed.
Lemma D_9bd80 : decode_any W_9bd80 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd84 : bv 32 := 0xff853583.
Lemma F_9bd84 : fetch_word Plain.M.loaded_segments (0x9bdd0 : word) = Some W_9bd84.
Proof. vm_refl. Qed.
Lemma D_9bd84 : decode_any W_9bd84 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd88 : bv 32 := 0xff850493.
Lemma F_9bd88 : fetch_word Plain.M.loaded_segments (0x9bdd4 : word) = Some W_9bd88.
Proof. vm_refl. Qed.
Lemma D_9bd88 : decode_any W_9bd88 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd8c : bv 32 := 0x000580e7.
Lemma F_9bd8c : fetch_word Plain.M.loaded_segments (0x9bdd8 : word) = Some W_9bd8c.
Proof. vm_refl. Qed.
Lemma D_9bd8c : decode_any W_9bd8c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd90 : bv 32 := 0x00048513.
Lemma F_9bd90 : fetch_word Plain.M.loaded_segments (0x9bddc : word) = Some W_9bd90.
Proof. vm_refl. Qed.
Lemma D_9bd90 : decode_any W_9bd90 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd94 : bv 32 := 0xfe9468e3.
Lemma F_9bd94 : fetch_word Plain.M.loaded_segments (0x9bde0 : word) = Some W_9bd94.
Proof. vm_refl. Qed.
Lemma D_9bd94 : decode_any W_9bd94 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd98 : bv 32 := 0x01813083.
Lemma F_9bd98 : fetch_word Plain.M.loaded_segments (0x9bde4 : word) = Some W_9bd98.
Proof. vm_refl. Qed.
Lemma D_9bd98 : decode_any W_9bd98 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bd9c : bv 32 := 0x01013403.
Lemma F_9bd9c : fetch_word Plain.M.loaded_segments (0x9bde8 : word) = Some W_9bd9c.
Proof. vm_refl. Qed.
Lemma D_9bd9c : decode_any W_9bd9c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bda0 : bv 32 := 0x00813483.
Lemma F_9bda0 : fetch_word Plain.M.loaded_segments (0x9bdec : word) = Some W_9bda0.
Proof. vm_refl. Qed.
Lemma D_9bda0 : decode_any W_9bda0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bda4 : bv 32 := 0x02010113.
Lemma F_9bda4 : fetch_word Plain.M.loaded_segments (0x9bdf0 : word) = Some W_9bda4.
Proof. vm_refl. Qed.
Lemma D_9bda4 : decode_any W_9bda4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bda8 : bv 32 := 0xfb5ff06f.
Lemma F_9bda8 : fetch_word Plain.M.loaded_segments (0x9bdf4 : word) = Some W_9bda8.
Proof. vm_refl. Qed.
Lemma D_9bda8 : decode_any W_9bda8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdac : bv 32 := 0xff010113.
Lemma F_9bdac : fetch_word Plain.M.loaded_segments (0x9bdf8 : word) = Some W_9bdac.
Proof. vm_refl. Qed.
Lemma D_9bdac : decode_any W_9bdac = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdb0 : bv 32 := 0x00113423.
Lemma F_9bdb0 : fetch_word Plain.M.loaded_segments (0x9bdfc : word) = Some W_9bdb0.
Proof. vm_refl. Qed.
Lemma D_9bdb0 : decode_any W_9bdb0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdb4 : bv 32 := 0x00813023.
Lemma F_9bdb4 : fetch_word Plain.M.loaded_segments (0x9be00 : word) = Some W_9bdb4.
Proof. vm_refl. Qed.
Lemma D_9bdb4 : decode_any W_9bdb4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdb8 : bv 32 := 0x00000593.
Lemma F_9bdb8 : fetch_word Plain.M.loaded_segments (0x9be04 : word) = Some W_9bdb8.
Proof. vm_refl. Qed.
Lemma D_9bdb8 : decode_any W_9bdb8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdbc : bv 32 := 0x00020613.
Lemma F_9bdbc : fetch_word Plain.M.loaded_segments (0x9be08 : word) = Some W_9bdbc.
Proof. vm_refl. Qed.
Lemma D_9bdbc : decode_any W_9bdbc = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdc0 : bv 32 := 0xf5862603.
Lemma F_9bdc0 : fetch_word Plain.M.loaded_segments (0x9be0c : word) = Some W_9bdc0.
Proof. vm_refl. Qed.
Lemma D_9bdc0 : decode_any W_9bdc0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdc4 : bv 32 := 0x0004f697.
Lemma F_9bdc4 : fetch_word Plain.M.loaded_segments (0x9be10 : word) = Some W_9bdc4.
Proof. vm_refl. Qed.
Lemma D_9bdc4 : decode_any W_9bdc4 = Some (Auipc 13 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdc8 : bv 32 := 0x49868693.
Lemma F_9bdc8 : fetch_word Plain.M.loaded_segments (0x9be14 : word) = Some W_9bdc8.
Proof. vm_refl. Qed.
Lemma D_9bdc8 : decode_any W_9bdc8 = Some (OpImm ALU_ADD 13 13 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdcc : bv 32 := 0x1606a72f.
Lemma F_9bdcc : fetch_word Plain.M.loaded_segments (0x9be18 : word) = Some W_9bdcc.
Proof. vm_refl. Qed.
Lemma D_9bdcc : decode_any W_9bdcc = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdd0 : bv 32 := 0x00b71663.
Lemma F_9bdd0 : fetch_word Plain.M.loaded_segments (0x9be1c : word) = Some W_9bdd0.
Proof. vm_refl. Qed.
Lemma D_9bdd0 : decode_any W_9bdd0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdd4 : bv 32 := 0x1ec6a7af.
Lemma F_9bdd4 : fetch_word Plain.M.loaded_segments (0x9be20 : word) = Some W_9bdd4.
Proof. vm_refl. Qed.
Lemma D_9bdd4 : decode_any W_9bdd4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bdd8 : bv 32 := 0xfe079ae3.
Lemma F_9bdd8 : fetch_word Plain.M.loaded_segments (0x9be24 : word) = Some W_9bdd8.
Proof. vm_refl. Qed.
Lemma D_9bdd8 : decode_any W_9bdd8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bddc : bv 32 := 0x0007059b.
Lemma F_9bddc : fetch_word Plain.M.loaded_segments (0x9be28 : word) = Some W_9bddc.
Proof. vm_refl. Qed.
Lemma D_9bddc : decode_any W_9bddc = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bde0 : bv 32 := 0x02c58263.
Lemma F_9bde0 : fetch_word Plain.M.loaded_segments (0x9be2c : word) = Some W_9bde0.
Proof. vm_refl. Qed.
Lemma D_9bde0 : decode_any W_9bde0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bde4 : bv 32 := 0x02058263.
Lemma F_9bde4 : fetch_word Plain.M.loaded_segments (0x9be30 : word) = Some W_9bde4.
Proof. vm_refl. Qed.
Lemma D_9bde4 : decode_any W_9bde4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9be08 : bv 32 := 0x00050413.
Lemma F_9be08 : fetch_word Plain.M.loaded_segments (0x9be54 : word) = Some W_9be08.
Proof. vm_refl. Qed.
Lemma D_9be08 : decode_any W_9be08 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9be0c : bv 32 := 0xcf5ff0ef.
Lemma F_9be0c : fetch_word Plain.M.loaded_segments (0x9be58 : word) = Some W_9be0c.
Proof. vm_refl. Qed.
Lemma D_9be0c : decode_any W_9be0c = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

Definition W_9be10 : bv 32 := 0xf51ff0ef.
Lemma F_9be10 : fetch_word Plain.M.loaded_segments (0x9be5c : word) = Some W_9be10.
Proof. vm_refl. Qed.
Lemma D_9be10 : decode_any W_9be10 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_9be14 : bv 32 := 0x63c050ef.
Lemma F_9be14 : fetch_word Plain.M.loaded_segments (0x9be60 : word) = Some W_9be14.
Proof. vm_refl. Qed.
Lemma D_9be14 : decode_any W_9be14 = Some (Jal 1 22076, 4%Z).
Proof. vm_refl. Qed.

Definition W_9be18 : bv 32 := 0x00040513.
Lemma F_9be18 : fetch_word Plain.M.loaded_segments (0x9be64 : word) = Some W_9be18.
Proof. vm_refl. Qed.
Lemma D_9be18 : decode_any W_9be18 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9be1c : bv 32 := 0xc99ff0ef.
Lemma F_9be1c : fetch_word Plain.M.loaded_segments (0x9be68 : word) = Some W_9be1c.
Proof. vm_refl. Qed.
Lemma D_9be1c : decode_any W_9be1c = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf04 : bv 32 := 0xff010113.
Lemma F_9bf04 : fetch_word Plain.M.loaded_segments (0x9bf50 : word) = Some W_9bf04.
Proof. vm_refl. Qed.
Lemma D_9bf04 : decode_any W_9bf04 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf08 : bv 32 := 0x00113423.
Lemma F_9bf08 : fetch_word Plain.M.loaded_segments (0x9bf54 : word) = Some W_9bf08.
Proof. vm_refl. Qed.
Lemma D_9bf08 : decode_any W_9bf08 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf0c : bv 32 := 0x00050e63.
Lemma F_9bf0c : fetch_word Plain.M.loaded_segments (0x9bf58 : word) = Some W_9bf0c.
Proof. vm_refl. Qed.
Lemma D_9bf0c : decode_any W_9bf0c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf10 : bv 32 := 0x00050593.
Lemma F_9bf10 : fetch_word Plain.M.loaded_segments (0x9bf5c : word) = Some W_9bf10.
Proof. vm_refl. Qed.
Lemma D_9bf10 : decode_any W_9bf10 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf14 : bv 32 := 0x0001c517.
Lemma F_9bf14 : fetch_word Plain.M.loaded_segments (0x9bf60 : word) = Some W_9bf14.
Proof. vm_refl. Qed.
Lemma D_9bf14 : decode_any W_9bf14 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf18 : bv 32 := 0x34053503.
Lemma F_9bf18 : fetch_word Plain.M.loaded_segments (0x9bf64 : word) = Some W_9bf18.
Proof. vm_refl. Qed.
Lemma D_9bf18 : decode_any W_9bf18 = Some (Load SZ8 true 10 10 832, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf1c : bv 32 := 0x00800613.
Lemma F_9bf1c : fetch_word Plain.M.loaded_segments (0x9bf68 : word) = Some W_9bf1c.
Proof. vm_refl. Qed.
Lemma D_9bf1c : decode_any W_9bf1c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf20 : bv 32 := 0x520100ef.
Lemma F_9bf20 : fetch_word Plain.M.loaded_segments (0x9bf6c : word) = Some W_9bf20.
Proof. vm_refl. Qed.
Lemma D_9bf20 : decode_any W_9bf20 = Some (Jal 1 66848, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf24 : bv 32 := 0x01c0006f.
Lemma F_9bf24 : fetch_word Plain.M.loaded_segments (0x9bf70 : word) = Some W_9bf24.
Proof. vm_refl. Qed.
Lemma D_9bf24 : decode_any W_9bf24 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf40 : bv 32 := 0x0001c517.
Lemma F_9bf40 : fetch_word Plain.M.loaded_segments (0x9bf8c : word) = Some W_9bf40.
Proof. vm_refl. Qed.
Lemma D_9bf40 : decode_any W_9bf40 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf44 : bv 32 := 0x31453503.
Lemma F_9bf44 : fetch_word Plain.M.loaded_segments (0x9bf90 : word) = Some W_9bf44.
Proof. vm_refl. Qed.
Lemma D_9bf44 : decode_any W_9bf44 = Some (Load SZ8 true 10 10 788, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf48 : bv 32 := 0x000500a3.
Lemma F_9bf48 : fetch_word Plain.M.loaded_segments (0x9bf94 : word) = Some W_9bf48.
Proof. vm_refl. Qed.
Lemma D_9bf48 : decode_any W_9bf48 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf4c : bv 32 := 0x00053503.
Lemma F_9bf4c : fetch_word Plain.M.loaded_segments (0x9bf98 : word) = Some W_9bf4c.
Proof. vm_refl. Qed.
Lemma D_9bf4c : decode_any W_9bf4c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf50 : bv 32 := 0x00020593.
Lemma F_9bf50 : fetch_word Plain.M.loaded_segments (0x9bf9c : word) = Some W_9bf50.
Proof. vm_refl. Qed.
Lemma D_9bf50 : decode_any W_9bf50 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf54 : bv 32 := 0xfea5b823.
Lemma F_9bf54 : fetch_word Plain.M.loaded_segments (0x9bfa0 : word) = Some W_9bf54.
Proof. vm_refl. Qed.
Lemma D_9bf54 : decode_any W_9bf54 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf58 : bv 32 := 0x00813083.
Lemma F_9bf58 : fetch_word Plain.M.loaded_segments (0x9bfa4 : word) = Some W_9bf58.
Proof. vm_refl. Qed.
Lemma D_9bf58 : decode_any W_9bf58 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf5c : bv 32 := 0x01010113.
Lemma F_9bf5c : fetch_word Plain.M.loaded_segments (0x9bfa8 : word) = Some W_9bf5c.
Proof. vm_refl. Qed.
Lemma D_9bf5c : decode_any W_9bf5c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf60 : bv 32 := 0x00008067.
Lemma F_9bf60 : fetch_word Plain.M.loaded_segments (0x9bfac : word) = Some W_9bf60.
Proof. vm_refl. Qed.
Lemma D_9bf60 : decode_any W_9bf60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf6c : bv 32 := 0xfffff5b7.
Lemma F_9bf6c : fetch_word Plain.M.loaded_segments (0x9bfb8 : word) = Some W_9bf6c.
Proof. vm_refl. Qed.
Lemma D_9bf6c : decode_any W_9bf6c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf70 : bv 32 := 0x0015859b.
Lemma F_9bf70 : fetch_word Plain.M.loaded_segments (0x9bfbc : word) = Some W_9bf70.
Proof. vm_refl. Qed.
Lemma D_9bf70 : decode_any W_9bf70 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf74 : bv 32 := 0x02b56663.
Lemma F_9bf74 : fetch_word Plain.M.loaded_segments (0x9bfc0 : word) = Some W_9bf74.
Proof. vm_refl. Qed.
Lemma D_9bf74 : decode_any W_9bf74 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfa0 : bv 32 := 0x00008067.
Lemma F_9bfa0 : fetch_word Plain.M.loaded_segments (0x9bfec : word) = Some W_9bfa0.
Proof. vm_refl. Qed.
Lemma D_9bfa0 : decode_any W_9bfa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
