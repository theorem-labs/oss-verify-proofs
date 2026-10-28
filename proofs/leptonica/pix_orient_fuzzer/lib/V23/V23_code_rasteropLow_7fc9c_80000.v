(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7fc9c : bv 32 := 0xf1010113.
Lemma F_7fc9c : fetch_word Ubsan.M.loaded_segments (0x7fc9c : word) = Some W_7fc9c.
Proof. vm_refl. Qed.
Lemma D_7fc9c : decode_any W_7fc9c = Some (OpImm ALU_ADD 2 2 3856, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fca0 : bv 32 := 0x0e113423.
Lemma F_7fca0 : fetch_word Ubsan.M.loaded_segments (0x7fca0 : word) = Some W_7fca0.
Proof. vm_refl. Qed.
Lemma D_7fca0 : decode_any W_7fca0 = Some (Store SZ8 2 1 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fca4 : bv 32 := 0x0e813023.
Lemma F_7fca4 : fetch_word Ubsan.M.loaded_segments (0x7fca4 : word) = Some W_7fca4.
Proof. vm_refl. Qed.
Lemma D_7fca4 : decode_any W_7fca4 = Some (Store SZ8 2 8 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fca8 : bv 32 := 0x0c913c23.
Lemma F_7fca8 : fetch_word Ubsan.M.loaded_segments (0x7fca8 : word) = Some W_7fca8.
Proof. vm_refl. Qed.
Lemma D_7fca8 : decode_any W_7fca8 = Some (Store SZ8 2 9 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcac : bv 32 := 0x0d213823.
Lemma F_7fcac : fetch_word Ubsan.M.loaded_segments (0x7fcac : word) = Some W_7fcac.
Proof. vm_refl. Qed.
Lemma D_7fcac : decode_any W_7fcac = Some (Store SZ8 2 18 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcb0 : bv 32 := 0x0d313423.
Lemma F_7fcb0 : fetch_word Ubsan.M.loaded_segments (0x7fcb0 : word) = Some W_7fcb0.
Proof. vm_refl. Qed.
Lemma D_7fcb0 : decode_any W_7fcb0 = Some (Store SZ8 2 19 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcb4 : bv 32 := 0x0d413023.
Lemma F_7fcb4 : fetch_word Ubsan.M.loaded_segments (0x7fcb4 : word) = Some W_7fcb4.
Proof. vm_refl. Qed.
Lemma D_7fcb4 : decode_any W_7fcb4 = Some (Store SZ8 2 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcb8 : bv 32 := 0x0b513c23.
Lemma F_7fcb8 : fetch_word Ubsan.M.loaded_segments (0x7fcb8 : word) = Some W_7fcb8.
Proof. vm_refl. Qed.
Lemma D_7fcb8 : decode_any W_7fcb8 = Some (Store SZ8 2 21 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcbc : bv 32 := 0x0b613823.
Lemma F_7fcbc : fetch_word Ubsan.M.loaded_segments (0x7fcbc : word) = Some W_7fcbc.
Proof. vm_refl. Qed.
Lemma D_7fcbc : decode_any W_7fcbc = Some (Store SZ8 2 22 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcc0 : bv 32 := 0x0b713423.
Lemma F_7fcc0 : fetch_word Ubsan.M.loaded_segments (0x7fcc0 : word) = Some W_7fcc0.
Proof. vm_refl. Qed.
Lemma D_7fcc0 : decode_any W_7fcc0 = Some (Store SZ8 2 23 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcc4 : bv 32 := 0x0b813023.
Lemma F_7fcc4 : fetch_word Ubsan.M.loaded_segments (0x7fcc4 : word) = Some W_7fcc4.
Proof. vm_refl. Qed.
Lemma D_7fcc4 : decode_any W_7fcc4 = Some (Store SZ8 2 24 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcc8 : bv 32 := 0x09913c23.
Lemma F_7fcc8 : fetch_word Ubsan.M.loaded_segments (0x7fcc8 : word) = Some W_7fcc8.
Proof. vm_refl. Qed.
Lemma D_7fcc8 : decode_any W_7fcc8 = Some (Store SZ8 2 25 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fccc : bv 32 := 0x09a13823.
Lemma F_7fccc : fetch_word Ubsan.M.loaded_segments (0x7fccc : word) = Some W_7fccc.
Proof. vm_refl. Qed.
Lemma D_7fccc : decode_any W_7fccc = Some (Store SZ8 2 26 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcd0 : bv 32 := 0x09b13423.
Lemma F_7fcd0 : fetch_word Ubsan.M.loaded_segments (0x7fcd0 : word) = Some W_7fcd0.
Proof. vm_refl. Qed.
Lemma D_7fcd0 : decode_any W_7fcd0 = Some (Store SZ8 2 27 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcd4 : bv 32 := 0x00060b93.
Lemma F_7fcd4 : fetch_word Ubsan.M.loaded_segments (0x7fcd4 : word) = Some W_7fcd4.
Proof. vm_refl. Qed.
Lemma D_7fcd4 : decode_any W_7fcd4 = Some (OpImm ALU_ADD 23 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcd8 : bv 32 := 0x00058293.
Lemma F_7fcd8 : fetch_word Ubsan.M.loaded_segments (0x7fcd8 : word) = Some W_7fcd8.
Proof. vm_refl. Qed.
Lemma D_7fcd8 : decode_any W_7fcd8 = Some (OpImm ALU_ADD 5 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcdc : bv 32 := 0x12813d03.
Lemma F_7fcdc : fetch_word Ubsan.M.loaded_segments (0x7fcdc : word) = Some W_7fcdc.
Proof. vm_refl. Qed.
Lemma D_7fcdc : decode_any W_7fcdc = Some (Load SZ8 true 26 2 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fce0 : bv 32 := 0x12013a03.
Lemma F_7fce0 : fetch_word Ubsan.M.loaded_segments (0x7fce0 : word) = Some W_7fce0.
Proof. vm_refl. Qed.
Lemma D_7fce0 : decode_any W_7fce0 = Some (Load SZ8 true 20 2 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fce4 : bv 32 := 0x11813303.
Lemma F_7fce4 : fetch_word Ubsan.M.loaded_segments (0x7fce4 : word) = Some W_7fce4.
Proof. vm_refl. Qed.
Lemma D_7fce4 : decode_any W_7fce4 = Some (Load SZ8 true 6 2 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fce8 : bv 32 := 0x11013e03.
Lemma F_7fce8 : fetch_word Ubsan.M.loaded_segments (0x7fce8 : word) = Some W_7fce8.
Proof. vm_refl. Qed.
Lemma D_7fce8 : decode_any W_7fce8 = Some (Load SZ8 true 28 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcec : bv 32 := 0x10813e83.
Lemma F_7fcec : fetch_word Ubsan.M.loaded_segments (0x7fcec : word) = Some W_7fcec.
Proof. vm_refl. Qed.
Lemma D_7fcec : decode_any W_7fcec = Some (Load SZ8 true 29 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcf0 : bv 32 := 0x10013983.
Lemma F_7fcf0 : fetch_word Ubsan.M.loaded_segments (0x7fcf0 : word) = Some W_7fcf0.
Proof. vm_refl. Qed.
Lemma D_7fcf0 : decode_any W_7fcf0 = Some (Load SZ8 true 19 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcf4 : bv 32 := 0x0f813583.
Lemma F_7fcf4 : fetch_word Ubsan.M.loaded_segments (0x7fcf4 : word) = Some W_7fcf4.
Proof. vm_refl. Qed.
Lemma D_7fcf4 : decode_any W_7fcf4 = Some (Load SZ8 true 11 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcf8 : bv 32 := 0x0f013b03.
Lemma F_7fcf8 : fetch_word Ubsan.M.loaded_segments (0x7fcf8 : word) = Some W_7fcf8.
Proof. vm_refl. Qed.
Lemma D_7fcf8 : decode_any W_7fcf8 = Some (Load SZ8 true 22 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fcfc : bv 32 := 0x00100613.
Lemma F_7fcfc : fetch_word Ubsan.M.loaded_segments (0x7fcfc : word) = Some W_7fcfc.
Proof. vm_refl. Qed.
Lemma D_7fcfc : decode_any W_7fcfc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd00 : bv 32 := 0x02c69663.
Lemma F_7fd00 : fetch_word Ubsan.M.loaded_segments (0x7fd00 : word) = Some W_7fd00.
Proof. vm_refl. Qed.
Lemma D_7fd00 : decode_any W_7fd00 = Some (Branch BC_NE 13 12 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd04 : bv 32 := 0x00088413.
Lemma F_7fd04 : fetch_word Ubsan.M.loaded_segments (0x7fd04 : word) = Some W_7fd04.
Proof. vm_refl. Qed.
Lemma D_7fd04 : decode_any W_7fd04 = Some (OpImm ALU_ADD 8 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd08 : bv 32 := 0x00078f13.
Lemma F_7fd08 : fetch_word Ubsan.M.loaded_segments (0x7fd08 : word) = Some W_7fd08.
Proof. vm_refl. Qed.
Lemma D_7fd08 : decode_any W_7fd08 = Some (OpImm ALU_ADD 30 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd0c : bv 32 := 0x00028a93.
Lemma F_7fd0c : fetch_word Ubsan.M.loaded_segments (0x7fd0c : word) = Some W_7fd0c.
Proof. vm_refl. Qed.
Lemma D_7fd0c : decode_any W_7fd0c = Some (OpImm ALU_ADD 21 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd10 : bv 32 := 0x0007861b.
Lemma F_7fd10 : fetch_word Ubsan.M.loaded_segments (0x7fd10 : word) = Some W_7fd10.
Proof. vm_refl. Qed.
Lemma D_7fd10 : decode_any W_7fd10 = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd14 : bv 32 := 0x06064c63.
Lemma F_7fd14 : fetch_word Ubsan.M.loaded_segments (0x7fd14 : word) = Some W_7fd14.
Proof. vm_refl. Qed.
Lemma D_7fd14 : decode_any W_7fd14 = Some (Branch BC_LT 12 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd18 : bv 32 := 0x000a0d93.
Lemma F_7fd18 : fetch_word Ubsan.M.loaded_segments (0x7fd18 : word) = Some W_7fd18.
Proof. vm_refl. Qed.
Lemma D_7fd18 : decode_any W_7fd18 = Some (OpImm ALU_ADD 27 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd1c : bv 32 := 0x000f0c93.
Lemma F_7fd1c : fetch_word Ubsan.M.loaded_segments (0x7fd1c : word) = Some W_7fd1c.
Proof. vm_refl. Qed.
Lemma D_7fd1c : decode_any W_7fd1c = Some (OpImm ALU_ADD 25 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd20 : bv 32 := 0x000a061b.
Lemma F_7fd20 : fetch_word Ubsan.M.loaded_segments (0x7fd20 : word) = Some W_7fd20.
Proof. vm_refl. Qed.
Lemma D_7fd20 : decode_any W_7fd20 = Some (OpImm32 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd24 : bv 32 := 0x0c065463.
Lemma F_7fd24 : fetch_word Ubsan.M.loaded_segments (0x7fd24 : word) = Some W_7fd24.
Proof. vm_refl. Qed.
Lemma D_7fd24 : decode_any W_7fd24 = Some (Branch BC_GE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd28 : bv 32 := 0x0980006f.
Lemma F_7fd28 : fetch_word Ubsan.M.loaded_segments (0x7fd28 : word) = Some W_7fd28.
Proof. vm_refl. Qed.
Lemma D_7fd28 : decode_any W_7fd28 = Some (Jal 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd2c : bv 32 := 0x02d28ab3.
Lemma F_7fd2c : fetch_word Ubsan.M.loaded_segments (0x7fd2c : word) = Some W_7fd2c.
Proof. vm_refl. Qed.
Lemma D_7fd2c : decode_any W_7fd2c = Some (Mul M_MUL 21 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd30 : bv 32 := 0x02d2863b.
Lemma F_7fd30 : fetch_word Ubsan.M.loaded_segments (0x7fd30 : word) = Some W_7fd30.
Proof. vm_refl. Qed.
Lemma D_7fd30 : decode_any W_7fd30 = Some (Mul32 M_MUL 12 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd34 : bv 32 := 0x01560463.
Lemma F_7fd34 : fetch_word Ubsan.M.loaded_segments (0x7fd34 : word) = Some W_7fd34.
Proof. vm_refl. Qed.
Lemma D_7fd34 : decode_any W_7fd34 = Some (Branch BC_EQ 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd38 : bv 32 := 0x7bc0206f.
Lemma F_7fd38 : fetch_word Ubsan.M.loaded_segments (0x7fd38 : word) = Some W_7fd38.
Proof. vm_refl. Qed.
Lemma D_7fd38 : decode_any W_7fd38 = Some (Jal 0 10172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd3c : bv 32 := 0x02d78f33.
Lemma F_7fd3c : fetch_word Ubsan.M.loaded_segments (0x7fd3c : word) = Some W_7fd3c.
Proof. vm_refl. Qed.
Lemma D_7fd3c : decode_any W_7fd3c = Some (Mul M_MUL 30 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd40 : bv 32 := 0x02d7863b.
Lemma F_7fd40 : fetch_word Ubsan.M.loaded_segments (0x7fd40 : word) = Some W_7fd40.
Proof. vm_refl. Qed.
Lemma D_7fd40 : decode_any W_7fd40 = Some (Mul32 M_MUL 12 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd44 : bv 32 := 0x01e60463.
Lemma F_7fd44 : fetch_word Ubsan.M.loaded_segments (0x7fd44 : word) = Some W_7fd44.
Proof. vm_refl. Qed.
Lemma D_7fd44 : decode_any W_7fd44 = Some (Branch BC_EQ 12 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd48 : bv 32 := 0x7ac0206f.
Lemma F_7fd48 : fetch_word Ubsan.M.loaded_segments (0x7fd48 : word) = Some W_7fd48.
Proof. vm_refl. Qed.
Lemma D_7fd48 : decode_any W_7fd48 = Some (Jal 0 10156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd4c : bv 32 := 0x02d88433.
Lemma F_7fd4c : fetch_word Ubsan.M.loaded_segments (0x7fd4c : word) = Some W_7fd4c.
Proof. vm_refl. Qed.
Lemma D_7fd4c : decode_any W_7fd4c = Some (Mul M_MUL 8 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd50 : bv 32 := 0x02d8863b.
Lemma F_7fd50 : fetch_word Ubsan.M.loaded_segments (0x7fd50 : word) = Some W_7fd50.
Proof. vm_refl. Qed.
Lemma D_7fd50 : decode_any W_7fd50 = Some (Mul32 M_MUL 12 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd54 : bv 32 := 0x00860463.
Lemma F_7fd54 : fetch_word Ubsan.M.loaded_segments (0x7fd54 : word) = Some W_7fd54.
Proof. vm_refl. Qed.
Lemma D_7fd54 : decode_any W_7fd54 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd58 : bv 32 := 0x79c0206f.
Lemma F_7fd58 : fetch_word Ubsan.M.loaded_segments (0x7fd58 : word) = Some W_7fd58.
Proof. vm_refl. Qed.
Lemma D_7fd58 : decode_any W_7fd58 = Some (Jal 0 10140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd5c : bv 32 := 0x02de8633.
Lemma F_7fd5c : fetch_word Ubsan.M.loaded_segments (0x7fd5c : word) = Some W_7fd5c.
Proof. vm_refl. Qed.
Lemma D_7fd5c : decode_any W_7fd5c = Some (Mul M_MUL 12 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd60 : bv 32 := 0x02de87bb.
Lemma F_7fd60 : fetch_word Ubsan.M.loaded_segments (0x7fd60 : word) = Some W_7fd60.
Proof. vm_refl. Qed.
Lemma D_7fd60 : decode_any W_7fd60 = Some (Mul32 M_MUL 15 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd64 : bv 32 := 0x00c78463.
Lemma F_7fd64 : fetch_word Ubsan.M.loaded_segments (0x7fd64 : word) = Some W_7fd64.
Proof. vm_refl. Qed.
Lemma D_7fd64 : decode_any W_7fd64 = Some (Branch BC_EQ 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd68 : bv 32 := 0x78c0206f.
Lemma F_7fd68 : fetch_word Ubsan.M.loaded_segments (0x7fd68 : word) = Some W_7fd68.
Proof. vm_refl. Qed.
Lemma D_7fd68 : decode_any W_7fd68 = Some (Jal 0 10124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd6c : bv 32 := 0x02da07b3.
Lemma F_7fd6c : fetch_word Ubsan.M.loaded_segments (0x7fd6c : word) = Some W_7fd6c.
Proof. vm_refl. Qed.
Lemma D_7fd6c : decode_any W_7fd6c = Some (Mul M_MUL 15 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd70 : bv 32 := 0x02da06bb.
Lemma F_7fd70 : fetch_word Ubsan.M.loaded_segments (0x7fd70 : word) = Some W_7fd70.
Proof. vm_refl. Qed.
Lemma D_7fd70 : decode_any W_7fd70 = Some (Mul32 M_MUL 13 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd74 : bv 32 := 0x00f68463.
Lemma F_7fd74 : fetch_word Ubsan.M.loaded_segments (0x7fd74 : word) = Some W_7fd74.
Proof. vm_refl. Qed.
Lemma D_7fd74 : decode_any W_7fd74 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd78 : bv 32 := 0x77c0206f.
Lemma F_7fd78 : fetch_word Ubsan.M.loaded_segments (0x7fd78 : word) = Some W_7fd78.
Proof. vm_refl. Qed.
Lemma D_7fd78 : decode_any W_7fd78 = Some (Jal 0 10108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd7c : bv 32 := 0x00060e93.
Lemma F_7fd7c : fetch_word Ubsan.M.loaded_segments (0x7fd7c : word) = Some W_7fd7c.
Proof. vm_refl. Qed.
Lemma D_7fd7c : decode_any W_7fd7c = Some (OpImm ALU_ADD 29 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd80 : bv 32 := 0x00078a13.
Lemma F_7fd80 : fetch_word Ubsan.M.loaded_segments (0x7fd80 : word) = Some W_7fd80.
Proof. vm_refl. Qed.
Lemma D_7fd80 : decode_any W_7fd80 = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd84 : bv 32 := 0x000f061b.
Lemma F_7fd84 : fetch_word Ubsan.M.loaded_segments (0x7fd84 : word) = Some W_7fd84.
Proof. vm_refl. Qed.
Lemma D_7fd84 : decode_any W_7fd84 = Some (OpImm32 12 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd88 : bv 32 := 0xf80658e3.
Lemma F_7fd88 : fetch_word Ubsan.M.loaded_segments (0x7fd88 : word) = Some W_7fd88.
Proof. vm_refl. Qed.
Lemma D_7fd88 : decode_any W_7fd88 = Some (Branch BC_GE 12 0 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd8c : bv 32 := 0x000a069b.
Lemma F_7fd8c : fetch_word Ubsan.M.loaded_segments (0x7fd8c : word) = Some W_7fd8c.
Proof. vm_refl. Qed.
Lemma D_7fd8c : decode_any W_7fd8c = Some (OpImm32 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd90 : bv 32 := 0x40c68db3.
Lemma F_7fd90 : fetch_word Ubsan.M.loaded_segments (0x7fd90 : word) = Some W_7fd90.
Proof. vm_refl. Qed.
Lemma D_7fd90 : decode_any W_7fd90 = Some (Op ALU_SUB 27 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd94 : bv 32 := 0x40c686bb.
Lemma F_7fd94 : fetch_word Ubsan.M.loaded_segments (0x7fd94 : word) = Some W_7fd94.
Proof. vm_refl. Qed.
Lemma D_7fd94 : decode_any W_7fd94 = Some (Op32 ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd98 : bv 32 := 0x01b68463.
Lemma F_7fd98 : fetch_word Ubsan.M.loaded_segments (0x7fd98 : word) = Some W_7fd98.
Proof. vm_refl. Qed.
Lemma D_7fd98 : decode_any W_7fd98 = Some (Branch BC_EQ 13 27 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd9c : bv 32 := 0x7580206f.
Lemma F_7fd9c : fetch_word Ubsan.M.loaded_segments (0x7fd9c : word) = Some W_7fd9c.
Proof. vm_refl. Qed.
Lemma D_7fd9c : decode_any W_7fd9c = Some (Jal 0 10072, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda0 : bv 32 := 0x0004069b.
Lemma F_7fda0 : fetch_word Ubsan.M.loaded_segments (0x7fda0 : word) = Some W_7fda0.
Proof. vm_refl. Qed.
Lemma D_7fda0 : decode_any W_7fda0 = Some (OpImm32 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda4 : bv 32 := 0x00c68433.
Lemma F_7fda4 : fetch_word Ubsan.M.loaded_segments (0x7fda4 : word) = Some W_7fda4.
Proof. vm_refl. Qed.
Lemma D_7fda4 : decode_any W_7fda4 = Some (Op ALU_ADD 8 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda8 : bv 32 := 0x00c6863b.
Lemma F_7fda8 : fetch_word Ubsan.M.loaded_segments (0x7fda8 : word) = Some W_7fda8.
Proof. vm_refl. Qed.
Lemma D_7fda8 : decode_any W_7fda8 = Some (Op32 ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdac : bv 32 := 0x00860463.
Lemma F_7fdac : fetch_word Ubsan.M.loaded_segments (0x7fdac : word) = Some W_7fdac.
Proof. vm_refl. Qed.
Lemma D_7fdac : decode_any W_7fdac = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb0 : bv 32 := 0x7440206f.
Lemma F_7fdb0 : fetch_word Ubsan.M.loaded_segments (0x7fdb0 : word) = Some W_7fdb0.
Proof. vm_refl. Qed.
Lemma D_7fdb0 : decode_any W_7fdb0 = Some (Jal 0 10052, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb4 : bv 32 := 0x00000c93.
Lemma F_7fdb4 : fetch_word Ubsan.M.loaded_segments (0x7fdb4 : word) = Some W_7fdb4.
Proof. vm_refl. Qed.
Lemma D_7fdb4 : decode_any W_7fdb4 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb8 : bv 32 := 0x000d861b.
Lemma F_7fdb8 : fetch_word Ubsan.M.loaded_segments (0x7fdb8 : word) = Some W_7fdb8.
Proof. vm_refl. Qed.
Lemma D_7fdb8 : decode_any W_7fdb8 = Some (OpImm32 12 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdbc : bv 32 := 0x02065863.
Lemma F_7fdbc : fetch_word Ubsan.M.loaded_segments (0x7fdbc : word) = Some W_7fdbc.
Proof. vm_refl. Qed.
Lemma D_7fdbc : decode_any W_7fdbc = Some (Branch BC_GE 12 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc0 : bv 32 := 0x000c869b.
Lemma F_7fdc0 : fetch_word Ubsan.M.loaded_segments (0x7fdc0 : word) = Some W_7fdc0.
Proof. vm_refl. Qed.
Lemma D_7fdc0 : decode_any W_7fdc0 = Some (OpImm32 13 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc4 : bv 32 := 0x40c68cb3.
Lemma F_7fdc4 : fetch_word Ubsan.M.loaded_segments (0x7fdc4 : word) = Some W_7fdc4.
Proof. vm_refl. Qed.
Lemma D_7fdc4 : decode_any W_7fdc4 = Some (Op ALU_SUB 25 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc8 : bv 32 := 0x40c686bb.
Lemma F_7fdc8 : fetch_word Ubsan.M.loaded_segments (0x7fdc8 : word) = Some W_7fdc8.
Proof. vm_refl. Qed.
Lemma D_7fdc8 : decode_any W_7fdc8 = Some (Op32 ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdcc : bv 32 := 0x01968463.
Lemma F_7fdcc : fetch_word Ubsan.M.loaded_segments (0x7fdcc : word) = Some W_7fdcc.
Proof. vm_refl. Qed.
Lemma D_7fdcc : decode_any W_7fdcc = Some (Branch BC_EQ 13 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd0 : bv 32 := 0x7240206f.
Lemma F_7fdd0 : fetch_word Ubsan.M.loaded_segments (0x7fdd0 : word) = Some W_7fdd0.
Proof. vm_refl. Qed.
Lemma D_7fdd0 : decode_any W_7fdd0 = Some (Jal 0 10020, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd4 : bv 32 := 0x0004069b.
Lemma F_7fdd4 : fetch_word Ubsan.M.loaded_segments (0x7fdd4 : word) = Some W_7fdd4.
Proof. vm_refl. Qed.
Lemma D_7fdd4 : decode_any W_7fdd4 = Some (OpImm32 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd8 : bv 32 := 0x00c68433.
Lemma F_7fdd8 : fetch_word Ubsan.M.loaded_segments (0x7fdd8 : word) = Some W_7fdd8.
Proof. vm_refl. Qed.
Lemma D_7fdd8 : decode_any W_7fdd8 = Some (Op ALU_ADD 8 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fddc : bv 32 := 0x00c6863b.
Lemma F_7fddc : fetch_word Ubsan.M.loaded_segments (0x7fddc : word) = Some W_7fddc.
Proof. vm_refl. Qed.
Lemma D_7fddc : decode_any W_7fddc = Some (Op32 ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde0 : bv 32 := 0x00860463.
Lemma F_7fde0 : fetch_word Ubsan.M.loaded_segments (0x7fde0 : word) = Some W_7fde0.
Proof. vm_refl. Qed.
Lemma D_7fde0 : decode_any W_7fde0 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde4 : bv 32 := 0x7100206f.
Lemma F_7fde4 : fetch_word Ubsan.M.loaded_segments (0x7fde4 : word) = Some W_7fde4.
Proof. vm_refl. Qed.
Lemma D_7fde4 : decode_any W_7fde4 = Some (Jal 0 10000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde8 : bv 32 := 0x00000d93.
Lemma F_7fde8 : fetch_word Ubsan.M.loaded_segments (0x7fde8 : word) = Some W_7fde8.
Proof. vm_refl. Qed.
Lemma D_7fde8 : decode_any W_7fde8 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdec : bv 32 := 0x0004061b.
Lemma F_7fdec : fetch_word Ubsan.M.loaded_segments (0x7fdec : word) = Some W_7fdec.
Proof. vm_refl. Qed.
Lemma D_7fdec : decode_any W_7fdec = Some (OpImm32 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf0 : bv 32 := 0x000c869b.
Lemma F_7fdf0 : fetch_word Ubsan.M.loaded_segments (0x7fdf0 : word) = Some W_7fdf0.
Proof. vm_refl. Qed.
Lemma D_7fdf0 : decode_any W_7fdf0 = Some (OpImm32 13 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf4 : bv 32 := 0x00c687b3.
Lemma F_7fdf4 : fetch_word Ubsan.M.loaded_segments (0x7fdf4 : word) = Some W_7fdf4.
Proof. vm_refl. Qed.
Lemma D_7fdf4 : decode_any W_7fdf4 = Some (Op ALU_ADD 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf8 : bv 32 := 0x00c688bb.
Lemma F_7fdf8 : fetch_word Ubsan.M.loaded_segments (0x7fdf8 : word) = Some W_7fdf8.
Proof. vm_refl. Qed.
Lemma D_7fdf8 : decode_any W_7fdf8 = Some (Op32 ALU_ADD 17 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdfc : bv 32 := 0x00f88463.
Lemma F_7fdfc : fetch_word Ubsan.M.loaded_segments (0x7fdfc : word) = Some W_7fdfc.
Proof. vm_refl. Qed.
Lemma D_7fdfc : decode_any W_7fdfc = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe00 : bv 32 := 0x6f40206f.
Lemma F_7fe00 : fetch_word Ubsan.M.loaded_segments (0x7fe00 : word) = Some W_7fe00.
Proof. vm_refl. Qed.
Lemma D_7fe00 : decode_any W_7fe00 = Some (Jal 0 9972, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe04 : bv 32 := 0x0007879b.
Lemma F_7fe04 : fetch_word Ubsan.M.loaded_segments (0x7fe04 : word) = Some W_7fe04.
Proof. vm_refl. Qed.
Lemma D_7fe04 : decode_any W_7fe04 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe08 : bv 32 := 0x000a889b.
Lemma F_7fe08 : fetch_word Ubsan.M.loaded_segments (0x7fe08 : word) = Some W_7fe08.
Proof. vm_refl. Qed.
Lemma D_7fe08 : decode_any W_7fe08 = Some (OpImm32 17 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe0c : bv 32 := 0x41178fbb.
Lemma F_7fe0c : fetch_word Ubsan.M.loaded_segments (0x7fe0c : word) = Some W_7fe0c.
Proof. vm_refl. Qed.
Lemma D_7fe0c : decode_any W_7fe0c = Some (Op32 ALU_SUB 31 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe10 : bv 32 := 0x411787b3.
Lemma F_7fe10 : fetch_word Ubsan.M.loaded_segments (0x7fe10 : word) = Some W_7fe10.
Proof. vm_refl. Qed.
Lemma D_7fe10 : decode_any W_7fe10 = Some (Op ALU_SUB 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe14 : bv 32 := 0x00ff8463.
Lemma F_7fe14 : fetch_word Ubsan.M.loaded_segments (0x7fe14 : word) = Some W_7fe14.
Proof. vm_refl. Qed.
Lemma D_7fe14 : decode_any W_7fe14 = Some (Branch BC_EQ 31 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe18 : bv 32 := 0x6dc0206f.
Lemma F_7fe18 : fetch_word Ubsan.M.loaded_segments (0x7fe18 : word) = Some W_7fe18.
Proof. vm_refl. Qed.
Lemma D_7fe18 : decode_any W_7fe18 = Some (Jal 0 9948, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe1c : bv 32 := 0x01f05a63.
Lemma F_7fe1c : fetch_word Ubsan.M.loaded_segments (0x7fe1c : word) = Some W_7fe1c.
Proof. vm_refl. Qed.
Lemma D_7fe1c : decode_any W_7fe1c = Some (Branch BC_GE 0 31 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe20 : bv 32 := 0x41f60433.
Lemma F_7fe20 : fetch_word Ubsan.M.loaded_segments (0x7fe20 : word) = Some W_7fe20.
Proof. vm_refl. Qed.
Lemma D_7fe20 : decode_any W_7fe20 = Some (Op ALU_SUB 8 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe24 : bv 32 := 0x41f6063b.
Lemma F_7fe24 : fetch_word Ubsan.M.loaded_segments (0x7fe24 : word) = Some W_7fe24.
Proof. vm_refl. Qed.
Lemma D_7fe24 : decode_any W_7fe24 = Some (Op32 ALU_SUB 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe28 : bv 32 := 0x00860463.
Lemma F_7fe28 : fetch_word Ubsan.M.loaded_segments (0x7fe28 : word) = Some W_7fe28.
Proof. vm_refl. Qed.
Lemma D_7fe28 : decode_any W_7fe28 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe2c : bv 32 := 0x6c80206f.
Lemma F_7fe2c : fetch_word Ubsan.M.loaded_segments (0x7fe2c : word) = Some W_7fe2c.
Proof. vm_refl. Qed.
Lemma D_7fe2c : decode_any W_7fe2c = Some (Jal 0 9928, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe30 : bv 32 := 0x0004061b.
Lemma F_7fe30 : fetch_word Ubsan.M.loaded_segments (0x7fe30 : word) = Some W_7fe30.
Proof. vm_refl. Qed.
Lemma D_7fe30 : decode_any W_7fe30 = Some (OpImm32 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe34 : bv 32 := 0x000d8c1b.
Lemma F_7fe34 : fetch_word Ubsan.M.loaded_segments (0x7fe34 : word) = Some W_7fe34.
Proof. vm_refl. Qed.
Lemma D_7fe34 : decode_any W_7fe34 = Some (OpImm32 24 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe38 : bv 32 := 0x00cc07b3.
Lemma F_7fe38 : fetch_word Ubsan.M.loaded_segments (0x7fe38 : word) = Some W_7fe38.
Proof. vm_refl. Qed.
Lemma D_7fe38 : decode_any W_7fe38 = Some (Op ALU_ADD 15 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe3c : bv 32 := 0x00cc08bb.
Lemma F_7fe3c : fetch_word Ubsan.M.loaded_segments (0x7fe3c : word) = Some W_7fe3c.
Proof. vm_refl. Qed.
Lemma D_7fe3c : decode_any W_7fe3c = Some (Op32 ALU_ADD 17 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe40 : bv 32 := 0x00f88463.
Lemma F_7fe40 : fetch_word Ubsan.M.loaded_segments (0x7fe40 : word) = Some W_7fe40.
Proof. vm_refl. Qed.
Lemma D_7fe40 : decode_any W_7fe40 = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe44 : bv 32 := 0x6b00206f.
Lemma F_7fe44 : fetch_word Ubsan.M.loaded_segments (0x7fe44 : word) = Some W_7fe44.
Proof. vm_refl. Qed.
Lemma D_7fe44 : decode_any W_7fe44 = Some (Jal 0 9904, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe48 : bv 32 := 0x0007829b.
Lemma F_7fe48 : fetch_word Ubsan.M.loaded_segments (0x7fe48 : word) = Some W_7fe48.
Proof. vm_refl. Qed.
Lemma D_7fe48 : decode_any W_7fe48 = Some (OpImm32 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe4c : bv 32 := 0x000e889b.
Lemma F_7fe4c : fetch_word Ubsan.M.loaded_segments (0x7fe4c : word) = Some W_7fe4c.
Proof. vm_refl. Qed.
Lemma D_7fe4c : decode_any W_7fe4c = Some (OpImm32 17 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe50 : bv 32 := 0x411287bb.
Lemma F_7fe50 : fetch_word Ubsan.M.loaded_segments (0x7fe50 : word) = Some W_7fe50.
Proof. vm_refl. Qed.
Lemma D_7fe50 : decode_any W_7fe50 = Some (Op32 ALU_SUB 15 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe54 : bv 32 := 0x411288b3.
Lemma F_7fe54 : fetch_word Ubsan.M.loaded_segments (0x7fe54 : word) = Some W_7fe54.
Proof. vm_refl. Qed.
Lemma D_7fe54 : decode_any W_7fe54 = Some (Op ALU_SUB 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe58 : bv 32 := 0x01178463.
Lemma F_7fe58 : fetch_word Ubsan.M.loaded_segments (0x7fe58 : word) = Some W_7fe58.
Proof. vm_refl. Qed.
Lemma D_7fe58 : decode_any W_7fe58 = Some (Branch BC_EQ 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe5c : bv 32 := 0x6980206f.
Lemma F_7fe5c : fetch_word Ubsan.M.loaded_segments (0x7fe5c : word) = Some W_7fe5c.
Proof. vm_refl. Qed.
Lemma D_7fe5c : decode_any W_7fe5c = Some (Jal 0 9880, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe60 : bv 32 := 0x00f05a63.
Lemma F_7fe60 : fetch_word Ubsan.M.loaded_segments (0x7fe60 : word) = Some W_7fe60.
Proof. vm_refl. Qed.
Lemma D_7fe60 : decode_any W_7fe60 = Some (Branch BC_GE 0 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe64 : bv 32 := 0x40f60433.
Lemma F_7fe64 : fetch_word Ubsan.M.loaded_segments (0x7fe64 : word) = Some W_7fe64.
Proof. vm_refl. Qed.
Lemma D_7fe64 : decode_any W_7fe64 = Some (Op ALU_SUB 8 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe68 : bv 32 := 0x40f6063b.
Lemma F_7fe68 : fetch_word Ubsan.M.loaded_segments (0x7fe68 : word) = Some W_7fe68.
Proof. vm_refl. Qed.
Lemma D_7fe68 : decode_any W_7fe68 = Some (Op32 ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe6c : bv 32 := 0x00860463.
Lemma F_7fe6c : fetch_word Ubsan.M.loaded_segments (0x7fe6c : word) = Some W_7fe6c.
Proof. vm_refl. Qed.
Lemma D_7fe6c : decode_any W_7fe6c = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe70 : bv 32 := 0x6840206f.
Lemma F_7fe70 : fetch_word Ubsan.M.loaded_segments (0x7fe70 : word) = Some W_7fe70.
Proof. vm_refl. Qed.
Lemma D_7fe70 : decode_any W_7fe70 = Some (Jal 0 9860, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe74 : bv 32 := 0x00084e63.
Lemma F_7fe74 : fetch_word Ubsan.M.loaded_segments (0x7fe74 : word) = Some W_7fe74.
Proof. vm_refl. Qed.
Lemma D_7fe74 : decode_any W_7fe74 = Some (Branch BC_LT 16 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe78 : bv 32 := 0x000d0093.
Lemma F_7fe78 : fetch_word Ubsan.M.loaded_segments (0x7fe78 : word) = Some W_7fe78.
Proof. vm_refl. Qed.
Lemma D_7fe78 : decode_any W_7fe78 = Some (OpImm ALU_ADD 1 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe7c : bv 32 := 0x00080613.
Lemma F_7fe7c : fetch_word Ubsan.M.loaded_segments (0x7fe7c : word) = Some W_7fe7c.
Proof. vm_refl. Qed.
Lemma D_7fe7c : decode_any W_7fe7c = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe80 : bv 32 := 0x000d079b.
Lemma F_7fe80 : fetch_word Ubsan.M.loaded_segments (0x7fe80 : word) = Some W_7fe80.
Proof. vm_refl. Qed.
Lemma D_7fe80 : decode_any W_7fe80 = Some (OpImm32 15 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe84 : bv 32 := 0x0207ce63.
Lemma F_7fe84 : fetch_word Ubsan.M.loaded_segments (0x7fe84 : word) = Some W_7fe84.
Proof. vm_refl. Qed.
Lemma D_7fe84 : decode_any W_7fe84 = Some (Branch BC_LT 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe88 : bv 32 := 0x00060393.
Lemma F_7fe88 : fetch_word Ubsan.M.loaded_segments (0x7fe88 : word) = Some W_7fe88.
Proof. vm_refl. Qed.
Lemma D_7fe88 : decode_any W_7fe88 = Some (OpImm ALU_ADD 7 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe8c : bv 32 := 0x05c0006f.
Lemma F_7fe8c : fetch_word Ubsan.M.loaded_segments (0x7fe8c : word) = Some W_7fe8c.
Proof. vm_refl. Qed.
Lemma D_7fe8c : decode_any W_7fe8c = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe90 : bv 32 := 0x410d00b3.
Lemma F_7fe90 : fetch_word Ubsan.M.loaded_segments (0x7fe90 : word) = Some W_7fe90.
Proof. vm_refl. Qed.
Lemma D_7fe90 : decode_any W_7fe90 = Some (Op ALU_SUB 1 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe94 : bv 32 := 0x410d063b.
Lemma F_7fe94 : fetch_word Ubsan.M.loaded_segments (0x7fe94 : word) = Some W_7fe94.
Proof. vm_refl. Qed.
Lemma D_7fe94 : decode_any W_7fe94 = Some (Op32 ALU_SUB 12 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe98 : bv 32 := 0x00160463.
Lemma F_7fe98 : fetch_word Ubsan.M.loaded_segments (0x7fe98 : word) = Some W_7fe98.
Proof. vm_refl. Qed.
Lemma D_7fe98 : decode_any W_7fe98 = Some (Branch BC_EQ 12 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe9c : bv 32 := 0x6580206f.
Lemma F_7fe9c : fetch_word Ubsan.M.loaded_segments (0x7fe9c : word) = Some W_7fe9c.
Proof. vm_refl. Qed.
Lemma D_7fe9c : decode_any W_7fe9c = Some (Jal 0 9816, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fea0 : bv 32 := 0x010b07b3.
Lemma F_7fea0 : fetch_word Ubsan.M.loaded_segments (0x7fea0 : word) = Some W_7fea0.
Proof. vm_refl. Qed.
Lemma D_7fea0 : decode_any W_7fea0 = Some (Op ALU_ADD 15 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fea4 : bv 32 := 0x010b063b.
Lemma F_7fea4 : fetch_word Ubsan.M.loaded_segments (0x7fea4 : word) = Some W_7fea4.
Proof. vm_refl. Qed.
Lemma D_7fea4 : decode_any W_7fea4 = Some (Op32 ALU_ADD 12 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fea8 : bv 32 := 0x00f60463.
Lemma F_7fea8 : fetch_word Ubsan.M.loaded_segments (0x7fea8 : word) = Some W_7fea8.
Proof. vm_refl. Qed.
Lemma D_7fea8 : decode_any W_7fea8 = Some (Branch BC_EQ 12 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feac : bv 32 := 0x6480206f.
Lemma F_7feac : fetch_word Ubsan.M.loaded_segments (0x7feac : word) = Some W_7feac.
Proof. vm_refl. Qed.
Lemma D_7feac : decode_any W_7feac = Some (Jal 0 9800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb0 : bv 32 := 0x00000613.
Lemma F_7feb0 : fetch_word Ubsan.M.loaded_segments (0x7feb0 : word) = Some W_7feb0.
Proof. vm_refl. Qed.
Lemma D_7feb0 : decode_any W_7feb0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb4 : bv 32 := 0x00078b13.
Lemma F_7feb4 : fetch_word Ubsan.M.loaded_segments (0x7feb4 : word) = Some W_7feb4.
Proof. vm_refl. Qed.
Lemma D_7feb4 : decode_any W_7feb4 = Some (OpImm ALU_ADD 22 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb8 : bv 32 := 0x0000879b.
Lemma F_7feb8 : fetch_word Ubsan.M.loaded_segments (0x7feb8 : word) = Some W_7feb8.
Proof. vm_refl. Qed.
Lemma D_7feb8 : decode_any W_7feb8 = Some (OpImm32 15 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7febc : bv 32 := 0xfc07d6e3.
Lemma F_7febc : fetch_word Ubsan.M.loaded_segments (0x7febc : word) = Some W_7febc.
Proof. vm_refl. Qed.
Lemma D_7febc : decode_any W_7febc = Some (Branch BC_GE 15 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec0 : bv 32 := 0x40f603b3.
Lemma F_7fec0 : fetch_word Ubsan.M.loaded_segments (0x7fec0 : word) = Some W_7fec0.
Proof. vm_refl. Qed.
Lemma D_7fec0 : decode_any W_7fec0 = Some (Op ALU_SUB 7 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec4 : bv 32 := 0x40f6063b.
Lemma F_7fec4 : fetch_word Ubsan.M.loaded_segments (0x7fec4 : word) = Some W_7fec4.
Proof. vm_refl. Qed.
Lemma D_7fec4 : decode_any W_7fec4 = Some (Op32 ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec8 : bv 32 := 0x00760463.
Lemma F_7fec8 : fetch_word Ubsan.M.loaded_segments (0x7fec8 : word) = Some W_7fec8.
Proof. vm_refl. Qed.
Lemma D_7fec8 : decode_any W_7fec8 = Some (Branch BC_EQ 12 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fecc : bv 32 := 0x6280206f.
Lemma F_7fecc : fetch_word Ubsan.M.loaded_segments (0x7fecc : word) = Some W_7fecc.
Proof. vm_refl. Qed.
Lemma D_7fecc : decode_any W_7fecc = Some (Jal 0 9768, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed0 : bv 32 := 0x000b061b.
Lemma F_7fed0 : fetch_word Ubsan.M.loaded_segments (0x7fed0 : word) = Some W_7fed0.
Proof. vm_refl. Qed.
Lemma D_7fed0 : decode_any W_7fed0 = Some (OpImm32 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed4 : bv 32 := 0x00f60b33.
Lemma F_7fed4 : fetch_word Ubsan.M.loaded_segments (0x7fed4 : word) = Some W_7fed4.
Proof. vm_refl. Qed.
Lemma D_7fed4 : decode_any W_7fed4 = Some (Op ALU_ADD 22 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed8 : bv 32 := 0x00f6063b.
Lemma F_7fed8 : fetch_word Ubsan.M.loaded_segments (0x7fed8 : word) = Some W_7fed8.
Proof. vm_refl. Qed.
Lemma D_7fed8 : decode_any W_7fed8 = Some (Op32 ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fedc : bv 32 := 0x01660463.
Lemma F_7fedc : fetch_word Ubsan.M.loaded_segments (0x7fedc : word) = Some W_7fedc.
Proof. vm_refl. Qed.
Lemma D_7fedc : decode_any W_7fedc = Some (Branch BC_EQ 12 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee0 : bv 32 := 0x6140206f.
Lemma F_7fee0 : fetch_word Ubsan.M.loaded_segments (0x7fee0 : word) = Some W_7fee0.
Proof. vm_refl. Qed.
Lemma D_7fee0 : decode_any W_7fee0 = Some (Jal 0 9748, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee4 : bv 32 := 0x00000093.
Lemma F_7fee4 : fetch_word Ubsan.M.loaded_segments (0x7fee4 : word) = Some W_7fee4.
Proof. vm_refl. Qed.
Lemma D_7fee4 : decode_any W_7fee4 = Some (OpImm ALU_ADD 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee8 : bv 32 := 0x000b061b.
Lemma F_7fee8 : fetch_word Ubsan.M.loaded_segments (0x7fee8 : word) = Some W_7fee8.
Proof. vm_refl. Qed.
Lemma D_7fee8 : decode_any W_7fee8 = Some (OpImm32 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feec : bv 32 := 0x0003839b.
Lemma F_7feec : fetch_word Ubsan.M.loaded_segments (0x7feec : word) = Some W_7feec.
Proof. vm_refl. Qed.
Lemma D_7feec : decode_any W_7feec = Some (OpImm32 7 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fef0 : bv 32 := 0x00c387b3.
Lemma F_7fef0 : fetch_word Ubsan.M.loaded_segments (0x7fef0 : word) = Some W_7fef0.
Proof. vm_refl. Qed.
Lemma D_7fef0 : decode_any W_7fef0 = Some (Op ALU_ADD 15 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fef4 : bv 32 := 0x00c388bb.
Lemma F_7fef4 : fetch_word Ubsan.M.loaded_segments (0x7fef4 : word) = Some W_7fef4.
Proof. vm_refl. Qed.
Lemma D_7fef4 : decode_any W_7fef4 = Some (Op32 ALU_ADD 17 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fef8 : bv 32 := 0x00f88463.
Lemma F_7fef8 : fetch_word Ubsan.M.loaded_segments (0x7fef8 : word) = Some W_7fef8.
Proof. vm_refl. Qed.
Lemma D_7fef8 : decode_any W_7fef8 = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fefc : bv 32 := 0x5f80206f.
Lemma F_7fefc : fetch_word Ubsan.M.loaded_segments (0x7fefc : word) = Some W_7fefc.
Proof. vm_refl. Qed.
Lemma D_7fefc : decode_any W_7fefc = Some (Jal 0 9720, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff00 : bv 32 := 0x0007879b.
Lemma F_7ff00 : fetch_word Ubsan.M.loaded_segments (0x7ff00 : word) = Some W_7ff00.
Proof. vm_refl. Qed.
Lemma D_7ff00 : decode_any W_7ff00 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff04 : bv 32 := 0x4177893b.
Lemma F_7ff04 : fetch_word Ubsan.M.loaded_segments (0x7ff04 : word) = Some W_7ff04.
Proof. vm_refl. Qed.
Lemma D_7ff04 : decode_any W_7ff04 = Some (Op32 ALU_SUB 18 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff08 : bv 32 := 0x417787b3.
Lemma F_7ff08 : fetch_word Ubsan.M.loaded_segments (0x7ff08 : word) = Some W_7ff08.
Proof. vm_refl. Qed.
Lemma D_7ff08 : decode_any W_7ff08 = Some (Op ALU_SUB 15 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff0c : bv 32 := 0x00f90463.
Lemma F_7ff0c : fetch_word Ubsan.M.loaded_segments (0x7ff0c : word) = Some W_7ff0c.
Proof. vm_refl. Qed.
Lemma D_7ff0c : decode_any W_7ff0c = Some (Branch BC_EQ 18 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff10 : bv 32 := 0x5e40206f.
Lemma F_7ff10 : fetch_word Ubsan.M.loaded_segments (0x7ff10 : word) = Some W_7ff10.
Proof. vm_refl. Qed.
Lemma D_7ff10 : decode_any W_7ff10 = Some (Jal 0 9700, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff14 : bv 32 := 0x01205a63.
Lemma F_7ff14 : fetch_word Ubsan.M.loaded_segments (0x7ff14 : word) = Some W_7ff14.
Proof. vm_refl. Qed.
Lemma D_7ff14 : decode_any W_7ff14 = Some (Branch BC_GE 0 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff18 : bv 32 := 0x41260b33.
Lemma F_7ff18 : fetch_word Ubsan.M.loaded_segments (0x7ff18 : word) = Some W_7ff18.
Proof. vm_refl. Qed.
Lemma D_7ff18 : decode_any W_7ff18 = Some (Op ALU_SUB 22 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff1c : bv 32 := 0x4126063b.
Lemma F_7ff1c : fetch_word Ubsan.M.loaded_segments (0x7ff1c : word) = Some W_7ff1c.
Proof. vm_refl. Qed.
Lemma D_7ff1c : decode_any W_7ff1c = Some (Op32 ALU_SUB 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff20 : bv 32 := 0x01660463.
Lemma F_7ff20 : fetch_word Ubsan.M.loaded_segments (0x7ff20 : word) = Some W_7ff20.
Proof. vm_refl. Qed.
Lemma D_7ff20 : decode_any W_7ff20 = Some (Branch BC_EQ 12 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff24 : bv 32 := 0x5d00206f.
Lemma F_7ff24 : fetch_word Ubsan.M.loaded_segments (0x7ff24 : word) = Some W_7ff24.
Proof. vm_refl. Qed.
Lemma D_7ff24 : decode_any W_7ff24 = Some (Jal 0 9680, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff28 : bv 32 := 0x000b061b.
Lemma F_7ff28 : fetch_word Ubsan.M.loaded_segments (0x7ff28 : word) = Some W_7ff28.
Proof. vm_refl. Qed.
Lemma D_7ff28 : decode_any W_7ff28 = Some (OpImm32 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff2c : bv 32 := 0x0000829b.
Lemma F_7ff2c : fetch_word Ubsan.M.loaded_segments (0x7ff2c : word) = Some W_7ff2c.
Proof. vm_refl. Qed.
Lemma D_7ff2c : decode_any W_7ff2c = Some (OpImm32 5 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff30 : bv 32 := 0x00c287b3.
Lemma F_7ff30 : fetch_word Ubsan.M.loaded_segments (0x7ff30 : word) = Some W_7ff30.
Proof. vm_refl. Qed.
Lemma D_7ff30 : decode_any W_7ff30 = Some (Op ALU_ADD 15 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff34 : bv 32 := 0x00c288bb.
Lemma F_7ff34 : fetch_word Ubsan.M.loaded_segments (0x7ff34 : word) = Some W_7ff34.
Proof. vm_refl. Qed.
Lemma D_7ff34 : decode_any W_7ff34 = Some (Op32 ALU_ADD 17 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff38 : bv 32 := 0x00f88463.
Lemma F_7ff38 : fetch_word Ubsan.M.loaded_segments (0x7ff38 : word) = Some W_7ff38.
Proof. vm_refl. Qed.
Lemma D_7ff38 : decode_any W_7ff38 = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff3c : bv 32 := 0x5b80206f.
Lemma F_7ff3c : fetch_word Ubsan.M.loaded_segments (0x7ff3c : word) = Some W_7ff3c.
Proof. vm_refl. Qed.
Lemma D_7ff3c : decode_any W_7ff3c = Some (Jal 0 9656, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff40 : bv 32 := 0x0007889b.
Lemma F_7ff40 : fetch_word Ubsan.M.loaded_segments (0x7ff40 : word) = Some W_7ff40.
Proof. vm_refl. Qed.
Lemma D_7ff40 : decode_any W_7ff40 = Some (OpImm32 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff44 : bv 32 := 0x41c887bb.
Lemma F_7ff44 : fetch_word Ubsan.M.loaded_segments (0x7ff44 : word) = Some W_7ff44.
Proof. vm_refl. Qed.
Lemma D_7ff44 : decode_any W_7ff44 = Some (Op32 ALU_SUB 15 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff48 : bv 32 := 0x41c888b3.
Lemma F_7ff48 : fetch_word Ubsan.M.loaded_segments (0x7ff48 : word) = Some W_7ff48.
Proof. vm_refl. Qed.
Lemma D_7ff48 : decode_any W_7ff48 = Some (Op ALU_SUB 17 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff4c : bv 32 := 0x01178463.
Lemma F_7ff4c : fetch_word Ubsan.M.loaded_segments (0x7ff4c : word) = Some W_7ff4c.
Proof. vm_refl. Qed.
Lemma D_7ff4c : decode_any W_7ff4c = Some (Branch BC_EQ 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff50 : bv 32 := 0x5a40206f.
Lemma F_7ff50 : fetch_word Ubsan.M.loaded_segments (0x7ff50 : word) = Some W_7ff50.
Proof. vm_refl. Qed.
Lemma D_7ff50 : decode_any W_7ff50 = Some (Jal 0 9636, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff54 : bv 32 := 0x00f05a63.
Lemma F_7ff54 : fetch_word Ubsan.M.loaded_segments (0x7ff54 : word) = Some W_7ff54.
Proof. vm_refl. Qed.
Lemma D_7ff54 : decode_any W_7ff54 = Some (Branch BC_GE 0 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff58 : bv 32 := 0x40f60b33.
Lemma F_7ff58 : fetch_word Ubsan.M.loaded_segments (0x7ff58 : word) = Some W_7ff58.
Proof. vm_refl. Qed.
Lemma D_7ff58 : decode_any W_7ff58 = Some (Op ALU_SUB 22 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff5c : bv 32 := 0x40f6063b.
Lemma F_7ff5c : fetch_word Ubsan.M.loaded_segments (0x7ff5c : word) = Some W_7ff5c.
Proof. vm_refl. Qed.
Lemma D_7ff5c : decode_any W_7ff5c = Some (Op32 ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff60 : bv 32 := 0x01660463.
Lemma F_7ff60 : fetch_word Ubsan.M.loaded_segments (0x7ff60 : word) = Some W_7ff60.
Proof. vm_refl. Qed.
Lemma D_7ff60 : decode_any W_7ff60 = Some (Branch BC_EQ 12 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff64 : bv 32 := 0x5900206f.
Lemma F_7ff64 : fetch_word Ubsan.M.loaded_segments (0x7ff64 : word) = Some W_7ff64.
Proof. vm_refl. Qed.
Lemma D_7ff64 : decode_any W_7ff64 = Some (Jal 0 9616, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff68 : bv 32 := 0x0004049b.
Lemma F_7ff68 : fetch_word Ubsan.M.loaded_segments (0x7ff68 : word) = Some W_7ff68.
Proof. vm_refl. Qed.
Lemma D_7ff68 : decode_any W_7ff68 = Some (OpImm32 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff6c : bv 32 := 0x00904463.
Lemma F_7ff6c : fetch_word Ubsan.M.loaded_segments (0x7ff6c : word) = Some W_7ff6c.
Proof. vm_refl. Qed.
Lemma D_7ff6c : decode_any W_7ff6c = Some (Branch BC_LT 0 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff70 : bv 32 := 0x6480706f.
Lemma F_7ff70 : fetch_word Ubsan.M.loaded_segments (0x7ff70 : word) = Some W_7ff70.
Proof. vm_refl. Qed.
Lemma D_7ff70 : decode_any W_7ff70 = Some (Jal 0 30280, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff74 : bv 32 := 0x000b0b1b.
Lemma F_7ff74 : fetch_word Ubsan.M.loaded_segments (0x7ff74 : word) = Some W_7ff74.
Proof. vm_refl. Qed.
Lemma D_7ff74 : decode_any W_7ff74 = Some (OpImm32 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff78 : bv 32 := 0x09613023.
Lemma F_7ff78 : fetch_word Ubsan.M.loaded_segments (0x7ff78 : word) = Some W_7ff78.
Proof. vm_refl. Qed.
Lemma D_7ff78 : decode_any W_7ff78 = Some (Store SZ8 2 22 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff7c : bv 32 := 0x01604463.
Lemma F_7ff7c : fetch_word Ubsan.M.loaded_segments (0x7ff7c : word) = Some W_7ff7c.
Proof. vm_refl. Qed.
Lemma D_7ff7c : decode_any W_7ff7c = Some (Branch BC_LT 0 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff80 : bv 32 := 0x6380706f.
Lemma F_7ff80 : fetch_word Ubsan.M.loaded_segments (0x7ff80 : word) = Some W_7ff80.
Proof. vm_refl. Qed.
Lemma D_7ff80 : decode_any W_7ff80 = Some (Jal 0 30264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff84 : bv 32 := 0x01bce633.
Lemma F_7ff84 : fetch_word Ubsan.M.loaded_segments (0x7ff84 : word) = Some W_7ff84.
Proof. vm_refl. Qed.
Lemma D_7ff84 : decode_any W_7ff84 = Some (Op ALU_OR 12 25 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff88 : bv 32 := 0x01f67613.
Lemma F_7ff88 : fetch_word Ubsan.M.loaded_segments (0x7ff88 : word) = Some W_7ff88.
Proof. vm_refl. Qed.
Lemma D_7ff88 : decode_any W_7ff88 = Some (OpImm ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff8c : bv 32 := 0x04613c23.
Lemma F_7ff8c : fetch_word Ubsan.M.loaded_segments (0x7ff8c : word) = Some W_7ff8c.
Proof. vm_refl. Qed.
Lemma D_7ff8c : decode_any W_7ff8c = Some (Store SZ8 2 6 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff90 : bv 32 := 0x18060263.
Lemma F_7ff90 : fetch_word Ubsan.M.loaded_segments (0x7ff90 : word) = Some W_7ff90.
Proof. vm_refl. Qed.
Lemma D_7ff90 : decode_any W_7ff90 = Some (Branch BC_EQ 12 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff94 : bv 32 := 0x02113423.
Lemma F_7ff94 : fetch_word Ubsan.M.loaded_segments (0x7ff94 : word) = Some W_7ff94.
Proof. vm_refl. Qed.
Lemma D_7ff94 : decode_any W_7ff94 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff98 : bv 32 := 0x03a13823.
Lemma F_7ff98 : fetch_word Ubsan.M.loaded_segments (0x7ff98 : word) = Some W_7ff98.
Proof. vm_refl. Qed.
Lemma D_7ff98 : decode_any W_7ff98 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff9c : bv 32 := 0x01fcf093.
Lemma F_7ff9c : fetch_word Ubsan.M.loaded_segments (0x7ff9c : word) = Some W_7ff9c.
Proof. vm_refl. Qed.
Lemma D_7ff9c : decode_any W_7ff9c = Some (OpImm ALU_AND 1 25 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa0 : bv 32 := 0x01fdf613.
Lemma F_7ffa0 : fetch_word Ubsan.M.loaded_segments (0x7ffa0 : word) = Some W_7ffa0.
Proof. vm_refl. Qed.
Lemma D_7ffa0 : decode_any W_7ffa0 = Some (OpImm ALU_AND 12 27 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa4 : bv 32 := 0x05013023.
Lemma F_7ffa4 : fetch_word Ubsan.M.loaded_segments (0x7ffa4 : word) = Some W_7ffa4.
Proof. vm_refl. Qed.
Lemma D_7ffa4 : decode_any W_7ffa4 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa8 : bv 32 := 0x05c13823.
Lemma F_7ffa8 : fetch_word Ubsan.M.loaded_segments (0x7ffa8 : word) = Some W_7ffa8.
Proof. vm_refl. Qed.
Lemma D_7ffa8 : decode_any W_7ffa8 = Some (Store SZ8 2 28 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffac : bv 32 := 0x05213423.
Lemma F_7ffac : fetch_word Ubsan.M.loaded_segments (0x7ffac : word) = Some W_7ffac.
Proof. vm_refl. Qed.
Lemma D_7ffac : decode_any W_7ffac = Some (Store SZ8 2 18 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb0 : bv 32 := 0x03713c23.
Lemma F_7ffb0 : fetch_word Ubsan.M.loaded_segments (0x7ffb0 : word) = Some W_7ffb0.
Proof. vm_refl. Qed.
Lemma D_7ffb0 : decode_any W_7ffb0 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb4 : bv 32 := 0x18c09663.
Lemma F_7ffb4 : fetch_word Ubsan.M.loaded_segments (0x7ffb4 : word) = Some W_7ffb4.
Proof. vm_refl. Qed.
Lemma D_7ffb4 : decode_any W_7ffb4 = Some (Branch BC_NE 1 12 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb8 : bv 32 := 0x60008e63.
Lemma F_7ffb8 : fetch_word Ubsan.M.loaded_segments (0x7ffb8 : word) = Some W_7ffb8.
Proof. vm_refl. Qed.
Lemma D_7ffb8 : decode_any W_7ffb8 = Some (Branch BC_EQ 1 0 1564, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffbc : bv 32 := 0x02000613.
Lemma F_7ffbc : fetch_word Ubsan.M.loaded_segments (0x7ffbc : word) = Some W_7ffbc.
Proof. vm_refl. Qed.
Lemma D_7ffbc : decode_any W_7ffbc = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc0 : bv 32 := 0xfff9f797.
Lemma F_7ffc0 : fetch_word Ubsan.M.loaded_segments (0x7ffc0 : word) = Some W_7ffc0.
Proof. vm_refl. Qed.
Lemma D_7ffc0 : decode_any W_7ffc0 = Some (Auipc 15 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc4 : bv 32 := 0x40160633.
Lemma F_7ffc4 : fetch_word Ubsan.M.loaded_segments (0x7ffc4 : word) = Some W_7ffc4.
Proof. vm_refl. Qed.
Lemma D_7ffc4 : decode_any W_7ffc4 = Some (Op ALU_SUB 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc8 : bv 32 := 0x48078793.
Lemma F_7ffc8 : fetch_word Ubsan.M.loaded_segments (0x7ffc8 : word) = Some W_7ffc8.
Proof. vm_refl. Qed.
Lemma D_7ffc8 : decode_any W_7ffc8 = Some (OpImm ALU_ADD 15 15 1152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffcc : bv 32 := 0x00261813.
Lemma F_7ffcc : fetch_word Ubsan.M.loaded_segments (0x7ffcc : word) = Some W_7ffcc.
Proof. vm_refl. Qed.
Lemma D_7ffcc : decode_any W_7ffcc = Some (ShiftImm ALU_SLL 16 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd0 : bv 32 := 0xfff7c893.
Lemma F_7ffd0 : fetch_word Ubsan.M.loaded_segments (0x7ffd0 : word) = Some W_7ffd0.
Proof. vm_refl. Qed.
Lemma D_7ffd0 : decode_any W_7ffd0 = Some (OpImm ALU_XOR 17 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd4 : bv 32 := 0x0108f463.
Lemma F_7ffd4 : fetch_word Ubsan.M.loaded_segments (0x7ffd4 : word) = Some W_7ffd4.
Proof. vm_refl. Qed.
Lemma D_7ffd4 : decode_any W_7ffd4 = Some (Branch BC_GEU 17 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd8 : bv 32 := 0x51c0206f.
Lemma F_7ffd8 : fetch_word Ubsan.M.loaded_segments (0x7ffd8 : word) = Some W_7ffd8.
Proof. vm_refl. Qed.
Lemma D_7ffd8 : decode_any W_7ffd8 = Some (Jal 0 9500, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffdc : bv 32 := 0x02770e33.
Lemma F_7ffdc : fetch_word Ubsan.M.loaded_segments (0x7ffdc : word) = Some W_7ffdc.
Proof. vm_refl. Qed.
Lemma D_7ffdc : decode_any W_7ffdc = Some (Mul M_MUL 28 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe0 : bv 32 := 0x027708bb.
Lemma F_7ffe0 : fetch_word Ubsan.M.loaded_segments (0x7ffe0 : word) = Some W_7ffe0.
Proof. vm_refl. Qed.
Lemma D_7ffe0 : decode_any W_7ffe0 = Some (Mul32 M_MUL 17 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe4 : bv 32 := 0x01c88463.
Lemma F_7ffe4 : fetch_word Ubsan.M.loaded_segments (0x7ffe4 : word) = Some W_7ffe4.
Proof. vm_refl. Qed.
Lemma D_7ffe4 : decode_any W_7ffe4 = Some (Branch BC_EQ 17 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe8 : bv 32 := 0x50c0206f.
Lemma F_7ffe8 : fetch_word Ubsan.M.loaded_segments (0x7ffe8 : word) = Some W_7ffe8.
Proof. vm_refl. Qed.
Lemma D_7ffe8 : decode_any W_7ffe8 = Some (Jal 0 9484, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffec : bv 32 := 0x000e0e1b.
Lemma F_7ffec : fetch_word Ubsan.M.loaded_segments (0x7ffec : word) = Some W_7ffec.
Proof. vm_refl. Qed.
Lemma D_7ffec : decode_any W_7ffec = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff0 : bv 32 := 0x002e1893.
Lemma F_7fff0 : fetch_word Ubsan.M.loaded_segments (0x7fff0 : word) = Some W_7fff0.
Proof. vm_refl. Qed.
Lemma D_7fff0 : decode_any W_7fff0 = Some (ShiftImm ALU_SLL 17 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff4 : bv 32 := 0x00a888b3.
Lemma F_7fff4 : fetch_word Ubsan.M.loaded_segments (0x7fff4 : word) = Some W_7fff4.
Proof. vm_refl. Qed.
Lemma D_7fff4 : decode_any W_7fff4 = Some (Op ALU_ADD 17 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff8 : bv 32 := 0x00a03333.
Lemma F_7fff8 : fetch_word Ubsan.M.loaded_segments (0x7fff8 : word) = Some W_7fff8.
Proof. vm_refl. Qed.
Lemma D_7fff8 : decode_any W_7fff8 = Some (Op ALU_SLTU 6 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fffc : bv 32 := 0x0018be93.
Lemma F_7fffc : fetch_word Ubsan.M.loaded_segments (0x7fffc : word) = Some W_7fffc.
Proof. vm_refl. Qed.
Lemma D_7fffc : decode_any W_7fffc = Some (OpImm ALU_SLTU 29 17 1, 4%Z).
Proof. vm_refl. Qed.
