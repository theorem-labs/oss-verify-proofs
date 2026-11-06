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

Definition W_4b104 : bv 32 := 0x01293023.
Lemma F_4b104 : fetch_word Plain.M.loaded_segments (0x4b104 : word) = Some W_4b104.
Proof. vm_refl. Qed.
Lemma D_4b104 : decode_any W_4b104 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b108 : bv 32 := 0x00040513.
Lemma F_4b108 : fetch_word Plain.M.loaded_segments (0x4b108 : word) = Some W_4b108.
Proof. vm_refl. Qed.
Lemma D_4b108 : decode_any W_4b108 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b10c : bv 32 := 0x23d0e0ef.
Lemma F_4b10c : fetch_word Plain.M.loaded_segments (0x4b10c : word) = Some W_4b10c.
Proof. vm_refl. Qed.
Lemma D_4b10c : decode_any W_4b10c = Some (Jal 1 59964, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b110 : bv 32 := 0x04054a63.
Lemma F_4b110 : fetch_word Plain.M.loaded_segments (0x4b110 : word) = Some W_4b110.
Proof. vm_refl. Qed.
Lemma D_4b110 : decode_any W_4b110 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b114 : bv 32 := 0x00051663.
Lemma F_4b114 : fetch_word Plain.M.loaded_segments (0x4b114 : word) = Some W_4b114.
Proof. vm_refl. Qed.
Lemma D_4b114 : decode_any W_4b114 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b118 : bv 32 := 0x00100513.
Lemma F_4b118 : fetch_word Plain.M.loaded_segments (0x4b118 : word) = Some W_4b118.
Proof. vm_refl. Qed.
Lemma D_4b118 : decode_any W_4b118 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b11c : bv 32 := 0x00a48023.
Lemma F_4b11c : fetch_word Plain.M.loaded_segments (0x4b11c : word) = Some W_4b11c.
Proof. vm_refl. Qed.
Lemma D_4b11c : decode_any W_4b11c = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b120 : bv 32 := 0x00200513.
Lemma F_4b120 : fetch_word Plain.M.loaded_segments (0x4b120 : word) = Some W_4b120.
Proof. vm_refl. Qed.
Lemma D_4b120 : decode_any W_4b120 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b124 : bv 32 := 0x00045597.
Lemma F_4b124 : fetch_word Plain.M.loaded_segments (0x4b124 : word) = Some W_4b124.
Proof. vm_refl. Qed.
Lemma D_4b124 : decode_any W_4b124 = Some (Auipc 11 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b128 : bv 32 := 0x02a92423.
Lemma F_4b128 : fetch_word Plain.M.loaded_segments (0x4b128 : word) = Some W_4b128.
Proof. vm_refl. Qed.
Lemma D_4b128 : decode_any W_4b128 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b12c : bv 32 := 0x06000893.
Lemma F_4b12c : fetch_word Plain.M.loaded_segments (0x4b12c : word) = Some W_4b12c.
Proof. vm_refl. Qed.
Lemma D_4b12c : decode_any W_4b12c = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b130 : bv 32 := 0x31c58513.
Lemma F_4b130 : fetch_word Plain.M.loaded_segments (0x4b130 : word) = Some W_4b130.
Proof. vm_refl. Qed.
Lemma D_4b130 : decode_any W_4b130 = Some (OpImm ALU_ADD 10 11 796, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b134 : bv 32 := 0x03848593.
Lemma F_4b134 : fetch_word Plain.M.loaded_segments (0x4b134 : word) = Some W_4b134.
Proof. vm_refl. Qed.
Lemma D_4b134 : decode_any W_4b134 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b138 : bv 32 := 0x00000073.
Lemma F_4b138 : fetch_word Plain.M.loaded_segments (0x4b138 : word) = Some W_4b138.
Proof. vm_refl. Qed.
Lemma D_4b138 : decode_any W_4b138 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4b138 : is_ecall W_4b138 = true.
Proof. reflexivity. Qed.

Definition W_4b13c : bv 32 := 0x07890613.
Lemma F_4b13c : fetch_word Plain.M.loaded_segments (0x4b13c : word) = Some W_4b13c.
Proof. vm_refl. Qed.
Lemma D_4b13c : decode_any W_4b13c = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b140 : bv 32 := 0x02a92023.
Lemma F_4b140 : fetch_word Plain.M.loaded_segments (0x4b140 : word) = Some W_4b140.
Proof. vm_refl. Qed.
Lemma D_4b140 : decode_any W_4b140 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b144 : bv 32 := 0x08b93c23.
Lemma F_4b144 : fetch_word Plain.M.loaded_segments (0x4b144 : word) = Some W_4b144.
Proof. vm_refl. Qed.
Lemma D_4b144 : decode_any W_4b144 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b148 : bv 32 := 0x06c93c23.
Lemma F_4b148 : fetch_word Plain.M.loaded_segments (0x4b148 : word) = Some W_4b148.
Proof. vm_refl. Qed.
Lemma D_4b148 : decode_any W_4b148 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b14c : bv 32 := 0x00045517.
Lemma F_4b14c : fetch_word Plain.M.loaded_segments (0x4b14c : word) = Some W_4b14c.
Proof. vm_refl. Qed.
Lemma D_4b14c : decode_any W_4b14c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b150 : bv 32 := 0x56453503.
Lemma F_4b150 : fetch_word Plain.M.loaded_segments (0x4b150 : word) = Some W_4b150.
Proof. vm_refl. Qed.
Lemma D_4b150 : decode_any W_4b150 = Some (Load SZ8 true 10 10 1380, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b154 : bv 32 := 0x01293423.
Lemma F_4b154 : fetch_word Plain.M.loaded_segments (0x4b154 : word) = Some W_4b154.
Proof. vm_refl. Qed.
Lemma D_4b154 : decode_any W_4b154 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b158 : bv 32 := 0x01293823.
Lemma F_4b158 : fetch_word Plain.M.loaded_segments (0x4b158 : word) = Some W_4b158.
Proof. vm_refl. Qed.
Lemma D_4b158 : decode_any W_4b158 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b15c : bv 32 := 0x00a93c23.
Lemma F_4b15c : fetch_word Plain.M.loaded_segments (0x4b15c : word) = Some W_4b15c.
Proof. vm_refl. Qed.
Lemma D_4b15c : decode_any W_4b15c = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b160 : bv 32 := 0x0080006f.
Lemma F_4b160 : fetch_word Plain.M.loaded_segments (0x4b160 : word) = Some W_4b160.
Proof. vm_refl. Qed.
Lemma D_4b160 : decode_any W_4b160 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b168 : bv 32 := 0x03813083.
Lemma F_4b168 : fetch_word Plain.M.loaded_segments (0x4b168 : word) = Some W_4b168.
Proof. vm_refl. Qed.
Lemma D_4b168 : decode_any W_4b168 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b16c : bv 32 := 0x03013403.
Lemma F_4b16c : fetch_word Plain.M.loaded_segments (0x4b16c : word) = Some W_4b16c.
Proof. vm_refl. Qed.
Lemma D_4b16c : decode_any W_4b16c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b170 : bv 32 := 0x02813483.
Lemma F_4b170 : fetch_word Plain.M.loaded_segments (0x4b170 : word) = Some W_4b170.
Proof. vm_refl. Qed.
Lemma D_4b170 : decode_any W_4b170 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b174 : bv 32 := 0x02013903.
Lemma F_4b174 : fetch_word Plain.M.loaded_segments (0x4b174 : word) = Some W_4b174.
Proof. vm_refl. Qed.
Lemma D_4b174 : decode_any W_4b174 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b178 : bv 32 := 0x01813983.
Lemma F_4b178 : fetch_word Plain.M.loaded_segments (0x4b178 : word) = Some W_4b178.
Proof. vm_refl. Qed.
Lemma D_4b178 : decode_any W_4b178 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b17c : bv 32 := 0x01013a03.
Lemma F_4b17c : fetch_word Plain.M.loaded_segments (0x4b17c : word) = Some W_4b17c.
Proof. vm_refl. Qed.
Lemma D_4b17c : decode_any W_4b17c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b180 : bv 32 := 0x00813a83.
Lemma F_4b180 : fetch_word Plain.M.loaded_segments (0x4b180 : word) = Some W_4b180.
Proof. vm_refl. Qed.
Lemma D_4b180 : decode_any W_4b180 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b184 : bv 32 := 0x04010113.
Lemma F_4b184 : fetch_word Plain.M.loaded_segments (0x4b184 : word) = Some W_4b184.
Proof. vm_refl. Qed.
Lemma D_4b184 : decode_any W_4b184 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b188 : bv 32 := 0x00008067.
Lemma F_4b188 : fetch_word Plain.M.loaded_segments (0x4b188 : word) = Some W_4b188.
Proof. vm_refl. Qed.
Lemma D_4b188 : decode_any W_4b188 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b22c : bv 32 := 0x00050593.
Lemma F_4b22c : fetch_word Plain.M.loaded_segments (0x4b22c : word) = Some W_4b22c.
Proof. vm_refl. Qed.
Lemma D_4b22c : decode_any W_4b22c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b230 : bv 32 := 0x05e00893.
Lemma F_4b230 : fetch_word Plain.M.loaded_segments (0x4b230 : word) = Some W_4b230.
Proof. vm_refl. Qed.
Lemma D_4b230 : decode_any W_4b230 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b234 : bv 32 := 0x00000073.
Lemma F_4b234 : fetch_word Plain.M.loaded_segments (0x4b234 : word) = Some W_4b234.
Proof. vm_refl. Qed.
Lemma D_4b234 : decode_any W_4b234 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4b234 : is_ecall W_4b234 = true.
Proof. reflexivity. Qed.

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

Definition W_4b4c8 : bv 32 := 0x00040513.
Lemma F_4b4c8 : fetch_word Plain.M.loaded_segments (0x4b4c8 : word) = Some W_4b4c8.
Proof. vm_refl. Qed.
Lemma D_4b4c8 : decode_any W_4b4c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b4cc : bv 32 := 0xd61ff0ef.
Lemma F_4b4cc : fetch_word Plain.M.loaded_segments (0x4b4cc : word) = Some W_4b4cc.
Proof. vm_refl. Qed.
Lemma D_4b4cc : decode_any W_4b4cc = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5b4 : bv 32 := 0xff010113.
Lemma F_4b5b4 : fetch_word Plain.M.loaded_segments (0x4b5b4 : word) = Some W_4b5b4.
Proof. vm_refl. Qed.
Lemma D_4b5b4 : decode_any W_4b5b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5b8 : bv 32 := 0x00113423.
Lemma F_4b5b8 : fetch_word Plain.M.loaded_segments (0x4b5b8 : word) = Some W_4b5b8.
Proof. vm_refl. Qed.
Lemma D_4b5b8 : decode_any W_4b5b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5bc : bv 32 := 0x00050e63.
Lemma F_4b5bc : fetch_word Plain.M.loaded_segments (0x4b5bc : word) = Some W_4b5bc.
Proof. vm_refl. Qed.
Lemma D_4b5bc : decode_any W_4b5bc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5c0 : bv 32 := 0x00050593.
Lemma F_4b5c0 : fetch_word Plain.M.loaded_segments (0x4b5c0 : word) = Some W_4b5c0.
Proof. vm_refl. Qed.
Lemma D_4b5c0 : decode_any W_4b5c0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5c4 : bv 32 := 0x00013517.
Lemma F_4b5c4 : fetch_word Plain.M.loaded_segments (0x4b5c4 : word) = Some W_4b5c4.
Proof. vm_refl. Qed.
Lemma D_4b5c4 : decode_any W_4b5c4 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5c8 : bv 32 := 0x02c53503.
Lemma F_4b5c8 : fetch_word Plain.M.loaded_segments (0x4b5c8 : word) = Some W_4b5c8.
Proof. vm_refl. Qed.
Lemma D_4b5c8 : decode_any W_4b5c8 = Some (Load SZ8 true 10 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5cc : bv 32 := 0x00800613.
Lemma F_4b5cc : fetch_word Plain.M.loaded_segments (0x4b5cc : word) = Some W_4b5cc.
Proof. vm_refl. Qed.
Lemma D_4b5cc : decode_any W_4b5cc = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5d0 : bv 32 := 0x3540d0ef.
Lemma F_4b5d0 : fetch_word Plain.M.loaded_segments (0x4b5d0 : word) = Some W_4b5d0.
Proof. vm_refl. Qed.
Lemma D_4b5d0 : decode_any W_4b5d0 = Some (Jal 1 54100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5d4 : bv 32 := 0x01c0006f.
Lemma F_4b5d4 : fetch_word Plain.M.loaded_segments (0x4b5d4 : word) = Some W_4b5d4.
Proof. vm_refl. Qed.
Lemma D_4b5d4 : decode_any W_4b5d4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5f0 : bv 32 := 0x00013517.
Lemma F_4b5f0 : fetch_word Plain.M.loaded_segments (0x4b5f0 : word) = Some W_4b5f0.
Proof. vm_refl. Qed.
Lemma D_4b5f0 : decode_any W_4b5f0 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5f4 : bv 32 := 0x00053503.
Lemma F_4b5f4 : fetch_word Plain.M.loaded_segments (0x4b5f4 : word) = Some W_4b5f4.
Proof. vm_refl. Qed.
Lemma D_4b5f4 : decode_any W_4b5f4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5f8 : bv 32 := 0x000500a3.
Lemma F_4b5f8 : fetch_word Plain.M.loaded_segments (0x4b5f8 : word) = Some W_4b5f8.
Proof. vm_refl. Qed.
Lemma D_4b5f8 : decode_any W_4b5f8 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b5fc : bv 32 := 0x00053503.
Lemma F_4b5fc : fetch_word Plain.M.loaded_segments (0x4b5fc : word) = Some W_4b5fc.
Proof. vm_refl. Qed.
Lemma D_4b5fc : decode_any W_4b5fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b600 : bv 32 := 0x00020593.
Lemma F_4b600 : fetch_word Plain.M.loaded_segments (0x4b600 : word) = Some W_4b600.
Proof. vm_refl. Qed.
Lemma D_4b600 : decode_any W_4b600 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b604 : bv 32 := 0xfea5b823.
Lemma F_4b604 : fetch_word Plain.M.loaded_segments (0x4b604 : word) = Some W_4b604.
Proof. vm_refl. Qed.
Lemma D_4b604 : decode_any W_4b604 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b608 : bv 32 := 0x00813083.
Lemma F_4b608 : fetch_word Plain.M.loaded_segments (0x4b608 : word) = Some W_4b608.
Proof. vm_refl. Qed.
Lemma D_4b608 : decode_any W_4b608 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b60c : bv 32 := 0x01010113.
Lemma F_4b60c : fetch_word Plain.M.loaded_segments (0x4b60c : word) = Some W_4b60c.
Proof. vm_refl. Qed.
Lemma D_4b60c : decode_any W_4b60c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b610 : bv 32 := 0x00008067.
Lemma F_4b610 : fetch_word Plain.M.loaded_segments (0x4b610 : word) = Some W_4b610.
Proof. vm_refl. Qed.
Lemma D_4b610 : decode_any W_4b610 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b61c : bv 32 := 0xfffff5b7.
Lemma F_4b61c : fetch_word Plain.M.loaded_segments (0x4b61c : word) = Some W_4b61c.
Proof. vm_refl. Qed.
Lemma D_4b61c : decode_any W_4b61c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b620 : bv 32 := 0x0015859b.
Lemma F_4b620 : fetch_word Plain.M.loaded_segments (0x4b620 : word) = Some W_4b620.
Proof. vm_refl. Qed.
Lemma D_4b620 : decode_any W_4b620 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b624 : bv 32 := 0x02b56663.
Lemma F_4b624 : fetch_word Plain.M.loaded_segments (0x4b624 : word) = Some W_4b624.
Proof. vm_refl. Qed.
Lemma D_4b624 : decode_any W_4b624 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b650 : bv 32 := 0x00008067.
Lemma F_4b650 : fetch_word Plain.M.loaded_segments (0x4b650 : word) = Some W_4b650.
Proof. vm_refl. Qed.
Lemma D_4b650 : decode_any W_4b650 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
