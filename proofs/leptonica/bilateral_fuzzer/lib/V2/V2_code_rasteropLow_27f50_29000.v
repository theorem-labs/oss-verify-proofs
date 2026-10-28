(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_27f50 : bv 32 := 0xf1010113.
Lemma F_27f50 : fetch_word Ubsan.M.loaded_segments (0x27f50 : word) = Some W_27f50.
Proof. vm_refl. Qed.
Lemma D_27f50 : decode_any W_27f50 = Some (OpImm ALU_ADD 2 2 3856, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f54 : bv 32 := 0x0e113423.
Lemma F_27f54 : fetch_word Ubsan.M.loaded_segments (0x27f54 : word) = Some W_27f54.
Proof. vm_refl. Qed.
Lemma D_27f54 : decode_any W_27f54 = Some (Store SZ8 2 1 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f58 : bv 32 := 0x0e813023.
Lemma F_27f58 : fetch_word Ubsan.M.loaded_segments (0x27f58 : word) = Some W_27f58.
Proof. vm_refl. Qed.
Lemma D_27f58 : decode_any W_27f58 = Some (Store SZ8 2 8 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f5c : bv 32 := 0x0c913c23.
Lemma F_27f5c : fetch_word Ubsan.M.loaded_segments (0x27f5c : word) = Some W_27f5c.
Proof. vm_refl. Qed.
Lemma D_27f5c : decode_any W_27f5c = Some (Store SZ8 2 9 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f60 : bv 32 := 0x0d213823.
Lemma F_27f60 : fetch_word Ubsan.M.loaded_segments (0x27f60 : word) = Some W_27f60.
Proof. vm_refl. Qed.
Lemma D_27f60 : decode_any W_27f60 = Some (Store SZ8 2 18 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f64 : bv 32 := 0x0d313423.
Lemma F_27f64 : fetch_word Ubsan.M.loaded_segments (0x27f64 : word) = Some W_27f64.
Proof. vm_refl. Qed.
Lemma D_27f64 : decode_any W_27f64 = Some (Store SZ8 2 19 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f68 : bv 32 := 0x0d413023.
Lemma F_27f68 : fetch_word Ubsan.M.loaded_segments (0x27f68 : word) = Some W_27f68.
Proof. vm_refl. Qed.
Lemma D_27f68 : decode_any W_27f68 = Some (Store SZ8 2 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f6c : bv 32 := 0x0b513c23.
Lemma F_27f6c : fetch_word Ubsan.M.loaded_segments (0x27f6c : word) = Some W_27f6c.
Proof. vm_refl. Qed.
Lemma D_27f6c : decode_any W_27f6c = Some (Store SZ8 2 21 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f70 : bv 32 := 0x0b613823.
Lemma F_27f70 : fetch_word Ubsan.M.loaded_segments (0x27f70 : word) = Some W_27f70.
Proof. vm_refl. Qed.
Lemma D_27f70 : decode_any W_27f70 = Some (Store SZ8 2 22 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f74 : bv 32 := 0x0b713423.
Lemma F_27f74 : fetch_word Ubsan.M.loaded_segments (0x27f74 : word) = Some W_27f74.
Proof. vm_refl. Qed.
Lemma D_27f74 : decode_any W_27f74 = Some (Store SZ8 2 23 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f78 : bv 32 := 0x0b813023.
Lemma F_27f78 : fetch_word Ubsan.M.loaded_segments (0x27f78 : word) = Some W_27f78.
Proof. vm_refl. Qed.
Lemma D_27f78 : decode_any W_27f78 = Some (Store SZ8 2 24 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f7c : bv 32 := 0x09913c23.
Lemma F_27f7c : fetch_word Ubsan.M.loaded_segments (0x27f7c : word) = Some W_27f7c.
Proof. vm_refl. Qed.
Lemma D_27f7c : decode_any W_27f7c = Some (Store SZ8 2 25 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f80 : bv 32 := 0x09a13823.
Lemma F_27f80 : fetch_word Ubsan.M.loaded_segments (0x27f80 : word) = Some W_27f80.
Proof. vm_refl. Qed.
Lemma D_27f80 : decode_any W_27f80 = Some (Store SZ8 2 26 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f84 : bv 32 := 0x09b13423.
Lemma F_27f84 : fetch_word Ubsan.M.loaded_segments (0x27f84 : word) = Some W_27f84.
Proof. vm_refl. Qed.
Lemma D_27f84 : decode_any W_27f84 = Some (Store SZ8 2 27 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f88 : bv 32 := 0x00060b93.
Lemma F_27f88 : fetch_word Ubsan.M.loaded_segments (0x27f88 : word) = Some W_27f88.
Proof. vm_refl. Qed.
Lemma D_27f88 : decode_any W_27f88 = Some (OpImm ALU_ADD 23 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f8c : bv 32 := 0x00058293.
Lemma F_27f8c : fetch_word Ubsan.M.loaded_segments (0x27f8c : word) = Some W_27f8c.
Proof. vm_refl. Qed.
Lemma D_27f8c : decode_any W_27f8c = Some (OpImm ALU_ADD 5 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f90 : bv 32 := 0x12813d03.
Lemma F_27f90 : fetch_word Ubsan.M.loaded_segments (0x27f90 : word) = Some W_27f90.
Proof. vm_refl. Qed.
Lemma D_27f90 : decode_any W_27f90 = Some (Load SZ8 true 26 2 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f94 : bv 32 := 0x12013a03.
Lemma F_27f94 : fetch_word Ubsan.M.loaded_segments (0x27f94 : word) = Some W_27f94.
Proof. vm_refl. Qed.
Lemma D_27f94 : decode_any W_27f94 = Some (Load SZ8 true 20 2 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f98 : bv 32 := 0x11813303.
Lemma F_27f98 : fetch_word Ubsan.M.loaded_segments (0x27f98 : word) = Some W_27f98.
Proof. vm_refl. Qed.
Lemma D_27f98 : decode_any W_27f98 = Some (Load SZ8 true 6 2 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_27f9c : bv 32 := 0x11013e03.
Lemma F_27f9c : fetch_word Ubsan.M.loaded_segments (0x27f9c : word) = Some W_27f9c.
Proof. vm_refl. Qed.
Lemma D_27f9c : decode_any W_27f9c = Some (Load SZ8 true 28 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fa0 : bv 32 := 0x10813e83.
Lemma F_27fa0 : fetch_word Ubsan.M.loaded_segments (0x27fa0 : word) = Some W_27fa0.
Proof. vm_refl. Qed.
Lemma D_27fa0 : decode_any W_27fa0 = Some (Load SZ8 true 29 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fa4 : bv 32 := 0x10013983.
Lemma F_27fa4 : fetch_word Ubsan.M.loaded_segments (0x27fa4 : word) = Some W_27fa4.
Proof. vm_refl. Qed.
Lemma D_27fa4 : decode_any W_27fa4 = Some (Load SZ8 true 19 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fa8 : bv 32 := 0x0f813583.
Lemma F_27fa8 : fetch_word Ubsan.M.loaded_segments (0x27fa8 : word) = Some W_27fa8.
Proof. vm_refl. Qed.
Lemma D_27fa8 : decode_any W_27fa8 = Some (Load SZ8 true 11 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fac : bv 32 := 0x0f013b03.
Lemma F_27fac : fetch_word Ubsan.M.loaded_segments (0x27fac : word) = Some W_27fac.
Proof. vm_refl. Qed.
Lemma D_27fac : decode_any W_27fac = Some (Load SZ8 true 22 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fb0 : bv 32 := 0x00100613.
Lemma F_27fb0 : fetch_word Ubsan.M.loaded_segments (0x27fb0 : word) = Some W_27fb0.
Proof. vm_refl. Qed.
Lemma D_27fb0 : decode_any W_27fb0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fb4 : bv 32 := 0x02c69663.
Lemma F_27fb4 : fetch_word Ubsan.M.loaded_segments (0x27fb4 : word) = Some W_27fb4.
Proof. vm_refl. Qed.
Lemma D_27fb4 : decode_any W_27fb4 = Some (Branch BC_NE 13 12 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fb8 : bv 32 := 0x00088413.
Lemma F_27fb8 : fetch_word Ubsan.M.loaded_segments (0x27fb8 : word) = Some W_27fb8.
Proof. vm_refl. Qed.
Lemma D_27fb8 : decode_any W_27fb8 = Some (OpImm ALU_ADD 8 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fbc : bv 32 := 0x00078f13.
Lemma F_27fbc : fetch_word Ubsan.M.loaded_segments (0x27fbc : word) = Some W_27fbc.
Proof. vm_refl. Qed.
Lemma D_27fbc : decode_any W_27fbc = Some (OpImm ALU_ADD 30 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fc0 : bv 32 := 0x00028a93.
Lemma F_27fc0 : fetch_word Ubsan.M.loaded_segments (0x27fc0 : word) = Some W_27fc0.
Proof. vm_refl. Qed.
Lemma D_27fc0 : decode_any W_27fc0 = Some (OpImm ALU_ADD 21 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fc4 : bv 32 := 0x0007861b.
Lemma F_27fc4 : fetch_word Ubsan.M.loaded_segments (0x27fc4 : word) = Some W_27fc4.
Proof. vm_refl. Qed.
Lemma D_27fc4 : decode_any W_27fc4 = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fc8 : bv 32 := 0x06064c63.
Lemma F_27fc8 : fetch_word Ubsan.M.loaded_segments (0x27fc8 : word) = Some W_27fc8.
Proof. vm_refl. Qed.
Lemma D_27fc8 : decode_any W_27fc8 = Some (Branch BC_LT 12 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fcc : bv 32 := 0x000a0d93.
Lemma F_27fcc : fetch_word Ubsan.M.loaded_segments (0x27fcc : word) = Some W_27fcc.
Proof. vm_refl. Qed.
Lemma D_27fcc : decode_any W_27fcc = Some (OpImm ALU_ADD 27 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fd0 : bv 32 := 0x000f0c93.
Lemma F_27fd0 : fetch_word Ubsan.M.loaded_segments (0x27fd0 : word) = Some W_27fd0.
Proof. vm_refl. Qed.
Lemma D_27fd0 : decode_any W_27fd0 = Some (OpImm ALU_ADD 25 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fd4 : bv 32 := 0x000a061b.
Lemma F_27fd4 : fetch_word Ubsan.M.loaded_segments (0x27fd4 : word) = Some W_27fd4.
Proof. vm_refl. Qed.
Lemma D_27fd4 : decode_any W_27fd4 = Some (OpImm32 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fd8 : bv 32 := 0x0c065463.
Lemma F_27fd8 : fetch_word Ubsan.M.loaded_segments (0x27fd8 : word) = Some W_27fd8.
Proof. vm_refl. Qed.
Lemma D_27fd8 : decode_any W_27fd8 = Some (Branch BC_GE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fdc : bv 32 := 0x0980006f.
Lemma F_27fdc : fetch_word Ubsan.M.loaded_segments (0x27fdc : word) = Some W_27fdc.
Proof. vm_refl. Qed.
Lemma D_27fdc : decode_any W_27fdc = Some (Jal 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fe0 : bv 32 := 0x02d28ab3.
Lemma F_27fe0 : fetch_word Ubsan.M.loaded_segments (0x27fe0 : word) = Some W_27fe0.
Proof. vm_refl. Qed.
Lemma D_27fe0 : decode_any W_27fe0 = Some (Mul M_MUL 21 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fe4 : bv 32 := 0x02d2863b.
Lemma F_27fe4 : fetch_word Ubsan.M.loaded_segments (0x27fe4 : word) = Some W_27fe4.
Proof. vm_refl. Qed.
Lemma D_27fe4 : decode_any W_27fe4 = Some (Mul32 M_MUL 12 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fe8 : bv 32 := 0x01560463.
Lemma F_27fe8 : fetch_word Ubsan.M.loaded_segments (0x27fe8 : word) = Some W_27fe8.
Proof. vm_refl. Qed.
Lemma D_27fe8 : decode_any W_27fe8 = Some (Branch BC_EQ 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27fec : bv 32 := 0x7bc0206f.
Lemma F_27fec : fetch_word Ubsan.M.loaded_segments (0x27fec : word) = Some W_27fec.
Proof. vm_refl. Qed.
Lemma D_27fec : decode_any W_27fec = Some (Jal 0 10172, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ff0 : bv 32 := 0x02d78f33.
Lemma F_27ff0 : fetch_word Ubsan.M.loaded_segments (0x27ff0 : word) = Some W_27ff0.
Proof. vm_refl. Qed.
Lemma D_27ff0 : decode_any W_27ff0 = Some (Mul M_MUL 30 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ff4 : bv 32 := 0x02d7863b.
Lemma F_27ff4 : fetch_word Ubsan.M.loaded_segments (0x27ff4 : word) = Some W_27ff4.
Proof. vm_refl. Qed.
Lemma D_27ff4 : decode_any W_27ff4 = Some (Mul32 M_MUL 12 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ff8 : bv 32 := 0x01e60463.
Lemma F_27ff8 : fetch_word Ubsan.M.loaded_segments (0x27ff8 : word) = Some W_27ff8.
Proof. vm_refl. Qed.
Lemma D_27ff8 : decode_any W_27ff8 = Some (Branch BC_EQ 12 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ffc : bv 32 := 0x7ac0206f.
Lemma F_27ffc : fetch_word Ubsan.M.loaded_segments (0x27ffc : word) = Some W_27ffc.
Proof. vm_refl. Qed.
Lemma D_27ffc : decode_any W_27ffc = Some (Jal 0 10156, 4%Z).
Proof. vm_refl. Qed.

Definition W_28000 : bv 32 := 0x02d88433.
Lemma F_28000 : fetch_word Ubsan.M.loaded_segments (0x28000 : word) = Some W_28000.
Proof. vm_refl. Qed.
Lemma D_28000 : decode_any W_28000 = Some (Mul M_MUL 8 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28004 : bv 32 := 0x02d8863b.
Lemma F_28004 : fetch_word Ubsan.M.loaded_segments (0x28004 : word) = Some W_28004.
Proof. vm_refl. Qed.
Lemma D_28004 : decode_any W_28004 = Some (Mul32 M_MUL 12 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28008 : bv 32 := 0x00860463.
Lemma F_28008 : fetch_word Ubsan.M.loaded_segments (0x28008 : word) = Some W_28008.
Proof. vm_refl. Qed.
Lemma D_28008 : decode_any W_28008 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2800c : bv 32 := 0x79c0206f.
Lemma F_2800c : fetch_word Ubsan.M.loaded_segments (0x2800c : word) = Some W_2800c.
Proof. vm_refl. Qed.
Lemma D_2800c : decode_any W_2800c = Some (Jal 0 10140, 4%Z).
Proof. vm_refl. Qed.

Definition W_28010 : bv 32 := 0x02de8633.
Lemma F_28010 : fetch_word Ubsan.M.loaded_segments (0x28010 : word) = Some W_28010.
Proof. vm_refl. Qed.
Lemma D_28010 : decode_any W_28010 = Some (Mul M_MUL 12 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28014 : bv 32 := 0x02de87bb.
Lemma F_28014 : fetch_word Ubsan.M.loaded_segments (0x28014 : word) = Some W_28014.
Proof. vm_refl. Qed.
Lemma D_28014 : decode_any W_28014 = Some (Mul32 M_MUL 15 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28018 : bv 32 := 0x00c78463.
Lemma F_28018 : fetch_word Ubsan.M.loaded_segments (0x28018 : word) = Some W_28018.
Proof. vm_refl. Qed.
Lemma D_28018 : decode_any W_28018 = Some (Branch BC_EQ 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2801c : bv 32 := 0x78c0206f.
Lemma F_2801c : fetch_word Ubsan.M.loaded_segments (0x2801c : word) = Some W_2801c.
Proof. vm_refl. Qed.
Lemma D_2801c : decode_any W_2801c = Some (Jal 0 10124, 4%Z).
Proof. vm_refl. Qed.

Definition W_28020 : bv 32 := 0x02da07b3.
Lemma F_28020 : fetch_word Ubsan.M.loaded_segments (0x28020 : word) = Some W_28020.
Proof. vm_refl. Qed.
Lemma D_28020 : decode_any W_28020 = Some (Mul M_MUL 15 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28024 : bv 32 := 0x02da06bb.
Lemma F_28024 : fetch_word Ubsan.M.loaded_segments (0x28024 : word) = Some W_28024.
Proof. vm_refl. Qed.
Lemma D_28024 : decode_any W_28024 = Some (Mul32 M_MUL 13 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28028 : bv 32 := 0x00f68463.
Lemma F_28028 : fetch_word Ubsan.M.loaded_segments (0x28028 : word) = Some W_28028.
Proof. vm_refl. Qed.
Lemma D_28028 : decode_any W_28028 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2802c : bv 32 := 0x77c0206f.
Lemma F_2802c : fetch_word Ubsan.M.loaded_segments (0x2802c : word) = Some W_2802c.
Proof. vm_refl. Qed.
Lemma D_2802c : decode_any W_2802c = Some (Jal 0 10108, 4%Z).
Proof. vm_refl. Qed.

Definition W_28030 : bv 32 := 0x00060e93.
Lemma F_28030 : fetch_word Ubsan.M.loaded_segments (0x28030 : word) = Some W_28030.
Proof. vm_refl. Qed.
Lemma D_28030 : decode_any W_28030 = Some (OpImm ALU_ADD 29 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28034 : bv 32 := 0x00078a13.
Lemma F_28034 : fetch_word Ubsan.M.loaded_segments (0x28034 : word) = Some W_28034.
Proof. vm_refl. Qed.
Lemma D_28034 : decode_any W_28034 = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28038 : bv 32 := 0x000f061b.
Lemma F_28038 : fetch_word Ubsan.M.loaded_segments (0x28038 : word) = Some W_28038.
Proof. vm_refl. Qed.
Lemma D_28038 : decode_any W_28038 = Some (OpImm32 12 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2803c : bv 32 := 0xf80658e3.
Lemma F_2803c : fetch_word Ubsan.M.loaded_segments (0x2803c : word) = Some W_2803c.
Proof. vm_refl. Qed.
Lemma D_2803c : decode_any W_2803c = Some (Branch BC_GE 12 0 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_28040 : bv 32 := 0x000a069b.
Lemma F_28040 : fetch_word Ubsan.M.loaded_segments (0x28040 : word) = Some W_28040.
Proof. vm_refl. Qed.
Lemma D_28040 : decode_any W_28040 = Some (OpImm32 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28044 : bv 32 := 0x40c68db3.
Lemma F_28044 : fetch_word Ubsan.M.loaded_segments (0x28044 : word) = Some W_28044.
Proof. vm_refl. Qed.
Lemma D_28044 : decode_any W_28044 = Some (Op ALU_SUB 27 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28048 : bv 32 := 0x40c686bb.
Lemma F_28048 : fetch_word Ubsan.M.loaded_segments (0x28048 : word) = Some W_28048.
Proof. vm_refl. Qed.
Lemma D_28048 : decode_any W_28048 = Some (Op32 ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2804c : bv 32 := 0x01b68463.
Lemma F_2804c : fetch_word Ubsan.M.loaded_segments (0x2804c : word) = Some W_2804c.
Proof. vm_refl. Qed.
Lemma D_2804c : decode_any W_2804c = Some (Branch BC_EQ 13 27 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28050 : bv 32 := 0x7580206f.
Lemma F_28050 : fetch_word Ubsan.M.loaded_segments (0x28050 : word) = Some W_28050.
Proof. vm_refl. Qed.
Lemma D_28050 : decode_any W_28050 = Some (Jal 0 10072, 4%Z).
Proof. vm_refl. Qed.

Definition W_28054 : bv 32 := 0x0004069b.
Lemma F_28054 : fetch_word Ubsan.M.loaded_segments (0x28054 : word) = Some W_28054.
Proof. vm_refl. Qed.
Lemma D_28054 : decode_any W_28054 = Some (OpImm32 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28058 : bv 32 := 0x00c68433.
Lemma F_28058 : fetch_word Ubsan.M.loaded_segments (0x28058 : word) = Some W_28058.
Proof. vm_refl. Qed.
Lemma D_28058 : decode_any W_28058 = Some (Op ALU_ADD 8 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2805c : bv 32 := 0x00c6863b.
Lemma F_2805c : fetch_word Ubsan.M.loaded_segments (0x2805c : word) = Some W_2805c.
Proof. vm_refl. Qed.
Lemma D_2805c : decode_any W_2805c = Some (Op32 ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28060 : bv 32 := 0x00860463.
Lemma F_28060 : fetch_word Ubsan.M.loaded_segments (0x28060 : word) = Some W_28060.
Proof. vm_refl. Qed.
Lemma D_28060 : decode_any W_28060 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28064 : bv 32 := 0x7440206f.
Lemma F_28064 : fetch_word Ubsan.M.loaded_segments (0x28064 : word) = Some W_28064.
Proof. vm_refl. Qed.
Lemma D_28064 : decode_any W_28064 = Some (Jal 0 10052, 4%Z).
Proof. vm_refl. Qed.

Definition W_28068 : bv 32 := 0x00000c93.
Lemma F_28068 : fetch_word Ubsan.M.loaded_segments (0x28068 : word) = Some W_28068.
Proof. vm_refl. Qed.
Lemma D_28068 : decode_any W_28068 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2806c : bv 32 := 0x000d861b.
Lemma F_2806c : fetch_word Ubsan.M.loaded_segments (0x2806c : word) = Some W_2806c.
Proof. vm_refl. Qed.
Lemma D_2806c : decode_any W_2806c = Some (OpImm32 12 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28070 : bv 32 := 0x02065863.
Lemma F_28070 : fetch_word Ubsan.M.loaded_segments (0x28070 : word) = Some W_28070.
Proof. vm_refl. Qed.
Lemma D_28070 : decode_any W_28070 = Some (Branch BC_GE 12 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_28074 : bv 32 := 0x000c869b.
Lemma F_28074 : fetch_word Ubsan.M.loaded_segments (0x28074 : word) = Some W_28074.
Proof. vm_refl. Qed.
Lemma D_28074 : decode_any W_28074 = Some (OpImm32 13 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28078 : bv 32 := 0x40c68cb3.
Lemma F_28078 : fetch_word Ubsan.M.loaded_segments (0x28078 : word) = Some W_28078.
Proof. vm_refl. Qed.
Lemma D_28078 : decode_any W_28078 = Some (Op ALU_SUB 25 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2807c : bv 32 := 0x40c686bb.
Lemma F_2807c : fetch_word Ubsan.M.loaded_segments (0x2807c : word) = Some W_2807c.
Proof. vm_refl. Qed.
Lemma D_2807c : decode_any W_2807c = Some (Op32 ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28080 : bv 32 := 0x01968463.
Lemma F_28080 : fetch_word Ubsan.M.loaded_segments (0x28080 : word) = Some W_28080.
Proof. vm_refl. Qed.
Lemma D_28080 : decode_any W_28080 = Some (Branch BC_EQ 13 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28084 : bv 32 := 0x7240206f.
Lemma F_28084 : fetch_word Ubsan.M.loaded_segments (0x28084 : word) = Some W_28084.
Proof. vm_refl. Qed.
Lemma D_28084 : decode_any W_28084 = Some (Jal 0 10020, 4%Z).
Proof. vm_refl. Qed.

Definition W_28088 : bv 32 := 0x0004069b.
Lemma F_28088 : fetch_word Ubsan.M.loaded_segments (0x28088 : word) = Some W_28088.
Proof. vm_refl. Qed.
Lemma D_28088 : decode_any W_28088 = Some (OpImm32 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2808c : bv 32 := 0x00c68433.
Lemma F_2808c : fetch_word Ubsan.M.loaded_segments (0x2808c : word) = Some W_2808c.
Proof. vm_refl. Qed.
Lemma D_2808c : decode_any W_2808c = Some (Op ALU_ADD 8 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28090 : bv 32 := 0x00c6863b.
Lemma F_28090 : fetch_word Ubsan.M.loaded_segments (0x28090 : word) = Some W_28090.
Proof. vm_refl. Qed.
Lemma D_28090 : decode_any W_28090 = Some (Op32 ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28094 : bv 32 := 0x00860463.
Lemma F_28094 : fetch_word Ubsan.M.loaded_segments (0x28094 : word) = Some W_28094.
Proof. vm_refl. Qed.
Lemma D_28094 : decode_any W_28094 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28098 : bv 32 := 0x7100206f.
Lemma F_28098 : fetch_word Ubsan.M.loaded_segments (0x28098 : word) = Some W_28098.
Proof. vm_refl. Qed.
Lemma D_28098 : decode_any W_28098 = Some (Jal 0 10000, 4%Z).
Proof. vm_refl. Qed.

Definition W_2809c : bv 32 := 0x00000d93.
Lemma F_2809c : fetch_word Ubsan.M.loaded_segments (0x2809c : word) = Some W_2809c.
Proof. vm_refl. Qed.
Lemma D_2809c : decode_any W_2809c = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280a0 : bv 32 := 0x0004061b.
Lemma F_280a0 : fetch_word Ubsan.M.loaded_segments (0x280a0 : word) = Some W_280a0.
Proof. vm_refl. Qed.
Lemma D_280a0 : decode_any W_280a0 = Some (OpImm32 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280a4 : bv 32 := 0x000c869b.
Lemma F_280a4 : fetch_word Ubsan.M.loaded_segments (0x280a4 : word) = Some W_280a4.
Proof. vm_refl. Qed.
Lemma D_280a4 : decode_any W_280a4 = Some (OpImm32 13 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280a8 : bv 32 := 0x00c687b3.
Lemma F_280a8 : fetch_word Ubsan.M.loaded_segments (0x280a8 : word) = Some W_280a8.
Proof. vm_refl. Qed.
Lemma D_280a8 : decode_any W_280a8 = Some (Op ALU_ADD 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_280ac : bv 32 := 0x00c688bb.
Lemma F_280ac : fetch_word Ubsan.M.loaded_segments (0x280ac : word) = Some W_280ac.
Proof. vm_refl. Qed.
Lemma D_280ac : decode_any W_280ac = Some (Op32 ALU_ADD 17 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_280b0 : bv 32 := 0x00f88463.
Lemma F_280b0 : fetch_word Ubsan.M.loaded_segments (0x280b0 : word) = Some W_280b0.
Proof. vm_refl. Qed.
Lemma D_280b0 : decode_any W_280b0 = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_280b4 : bv 32 := 0x6f40206f.
Lemma F_280b4 : fetch_word Ubsan.M.loaded_segments (0x280b4 : word) = Some W_280b4.
Proof. vm_refl. Qed.
Lemma D_280b4 : decode_any W_280b4 = Some (Jal 0 9972, 4%Z).
Proof. vm_refl. Qed.

Definition W_280b8 : bv 32 := 0x0007879b.
Lemma F_280b8 : fetch_word Ubsan.M.loaded_segments (0x280b8 : word) = Some W_280b8.
Proof. vm_refl. Qed.
Lemma D_280b8 : decode_any W_280b8 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280bc : bv 32 := 0x000a889b.
Lemma F_280bc : fetch_word Ubsan.M.loaded_segments (0x280bc : word) = Some W_280bc.
Proof. vm_refl. Qed.
Lemma D_280bc : decode_any W_280bc = Some (OpImm32 17 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280c0 : bv 32 := 0x41178fbb.
Lemma F_280c0 : fetch_word Ubsan.M.loaded_segments (0x280c0 : word) = Some W_280c0.
Proof. vm_refl. Qed.
Lemma D_280c0 : decode_any W_280c0 = Some (Op32 ALU_SUB 31 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_280c4 : bv 32 := 0x411787b3.
Lemma F_280c4 : fetch_word Ubsan.M.loaded_segments (0x280c4 : word) = Some W_280c4.
Proof. vm_refl. Qed.
Lemma D_280c4 : decode_any W_280c4 = Some (Op ALU_SUB 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_280c8 : bv 32 := 0x00ff8463.
Lemma F_280c8 : fetch_word Ubsan.M.loaded_segments (0x280c8 : word) = Some W_280c8.
Proof. vm_refl. Qed.
Lemma D_280c8 : decode_any W_280c8 = Some (Branch BC_EQ 31 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_280cc : bv 32 := 0x6dc0206f.
Lemma F_280cc : fetch_word Ubsan.M.loaded_segments (0x280cc : word) = Some W_280cc.
Proof. vm_refl. Qed.
Lemma D_280cc : decode_any W_280cc = Some (Jal 0 9948, 4%Z).
Proof. vm_refl. Qed.

Definition W_280d0 : bv 32 := 0x01f05a63.
Lemma F_280d0 : fetch_word Ubsan.M.loaded_segments (0x280d0 : word) = Some W_280d0.
Proof. vm_refl. Qed.
Lemma D_280d0 : decode_any W_280d0 = Some (Branch BC_GE 0 31 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_280d4 : bv 32 := 0x41f60433.
Lemma F_280d4 : fetch_word Ubsan.M.loaded_segments (0x280d4 : word) = Some W_280d4.
Proof. vm_refl. Qed.
Lemma D_280d4 : decode_any W_280d4 = Some (Op ALU_SUB 8 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_280d8 : bv 32 := 0x41f6063b.
Lemma F_280d8 : fetch_word Ubsan.M.loaded_segments (0x280d8 : word) = Some W_280d8.
Proof. vm_refl. Qed.
Lemma D_280d8 : decode_any W_280d8 = Some (Op32 ALU_SUB 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_280dc : bv 32 := 0x00860463.
Lemma F_280dc : fetch_word Ubsan.M.loaded_segments (0x280dc : word) = Some W_280dc.
Proof. vm_refl. Qed.
Lemma D_280dc : decode_any W_280dc = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_280e0 : bv 32 := 0x6c80206f.
Lemma F_280e0 : fetch_word Ubsan.M.loaded_segments (0x280e0 : word) = Some W_280e0.
Proof. vm_refl. Qed.
Lemma D_280e0 : decode_any W_280e0 = Some (Jal 0 9928, 4%Z).
Proof. vm_refl. Qed.

Definition W_280e4 : bv 32 := 0x0004061b.
Lemma F_280e4 : fetch_word Ubsan.M.loaded_segments (0x280e4 : word) = Some W_280e4.
Proof. vm_refl. Qed.
Lemma D_280e4 : decode_any W_280e4 = Some (OpImm32 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280e8 : bv 32 := 0x000d8c1b.
Lemma F_280e8 : fetch_word Ubsan.M.loaded_segments (0x280e8 : word) = Some W_280e8.
Proof. vm_refl. Qed.
Lemma D_280e8 : decode_any W_280e8 = Some (OpImm32 24 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_280ec : bv 32 := 0x00cc07b3.
Lemma F_280ec : fetch_word Ubsan.M.loaded_segments (0x280ec : word) = Some W_280ec.
Proof. vm_refl. Qed.
Lemma D_280ec : decode_any W_280ec = Some (Op ALU_ADD 15 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_280f0 : bv 32 := 0x00cc08bb.
Lemma F_280f0 : fetch_word Ubsan.M.loaded_segments (0x280f0 : word) = Some W_280f0.
Proof. vm_refl. Qed.
Lemma D_280f0 : decode_any W_280f0 = Some (Op32 ALU_ADD 17 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_280f4 : bv 32 := 0x00f88463.
Lemma F_280f4 : fetch_word Ubsan.M.loaded_segments (0x280f4 : word) = Some W_280f4.
Proof. vm_refl. Qed.
Lemma D_280f4 : decode_any W_280f4 = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_280f8 : bv 32 := 0x6b00206f.
Lemma F_280f8 : fetch_word Ubsan.M.loaded_segments (0x280f8 : word) = Some W_280f8.
Proof. vm_refl. Qed.
Lemma D_280f8 : decode_any W_280f8 = Some (Jal 0 9904, 4%Z).
Proof. vm_refl. Qed.

Definition W_280fc : bv 32 := 0x0007829b.
Lemma F_280fc : fetch_word Ubsan.M.loaded_segments (0x280fc : word) = Some W_280fc.
Proof. vm_refl. Qed.
Lemma D_280fc : decode_any W_280fc = Some (OpImm32 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28100 : bv 32 := 0x000e889b.
Lemma F_28100 : fetch_word Ubsan.M.loaded_segments (0x28100 : word) = Some W_28100.
Proof. vm_refl. Qed.
Lemma D_28100 : decode_any W_28100 = Some (OpImm32 17 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28104 : bv 32 := 0x411287bb.
Lemma F_28104 : fetch_word Ubsan.M.loaded_segments (0x28104 : word) = Some W_28104.
Proof. vm_refl. Qed.
Lemma D_28104 : decode_any W_28104 = Some (Op32 ALU_SUB 15 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28108 : bv 32 := 0x411288b3.
Lemma F_28108 : fetch_word Ubsan.M.loaded_segments (0x28108 : word) = Some W_28108.
Proof. vm_refl. Qed.
Lemma D_28108 : decode_any W_28108 = Some (Op ALU_SUB 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_2810c : bv 32 := 0x01178463.
Lemma F_2810c : fetch_word Ubsan.M.loaded_segments (0x2810c : word) = Some W_2810c.
Proof. vm_refl. Qed.
Lemma D_2810c : decode_any W_2810c = Some (Branch BC_EQ 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28110 : bv 32 := 0x6980206f.
Lemma F_28110 : fetch_word Ubsan.M.loaded_segments (0x28110 : word) = Some W_28110.
Proof. vm_refl. Qed.
Lemma D_28110 : decode_any W_28110 = Some (Jal 0 9880, 4%Z).
Proof. vm_refl. Qed.

Definition W_28114 : bv 32 := 0x00f05a63.
Lemma F_28114 : fetch_word Ubsan.M.loaded_segments (0x28114 : word) = Some W_28114.
Proof. vm_refl. Qed.
Lemma D_28114 : decode_any W_28114 = Some (Branch BC_GE 0 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_28118 : bv 32 := 0x40f60433.
Lemma F_28118 : fetch_word Ubsan.M.loaded_segments (0x28118 : word) = Some W_28118.
Proof. vm_refl. Qed.
Lemma D_28118 : decode_any W_28118 = Some (Op ALU_SUB 8 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2811c : bv 32 := 0x40f6063b.
Lemma F_2811c : fetch_word Ubsan.M.loaded_segments (0x2811c : word) = Some W_2811c.
Proof. vm_refl. Qed.
Lemma D_2811c : decode_any W_2811c = Some (Op32 ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28120 : bv 32 := 0x00860463.
Lemma F_28120 : fetch_word Ubsan.M.loaded_segments (0x28120 : word) = Some W_28120.
Proof. vm_refl. Qed.
Lemma D_28120 : decode_any W_28120 = Some (Branch BC_EQ 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28124 : bv 32 := 0x6840206f.
Lemma F_28124 : fetch_word Ubsan.M.loaded_segments (0x28124 : word) = Some W_28124.
Proof. vm_refl. Qed.
Lemma D_28124 : decode_any W_28124 = Some (Jal 0 9860, 4%Z).
Proof. vm_refl. Qed.

Definition W_28128 : bv 32 := 0x00084e63.
Lemma F_28128 : fetch_word Ubsan.M.loaded_segments (0x28128 : word) = Some W_28128.
Proof. vm_refl. Qed.
Lemma D_28128 : decode_any W_28128 = Some (Branch BC_LT 16 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_2812c : bv 32 := 0x000d0093.
Lemma F_2812c : fetch_word Ubsan.M.loaded_segments (0x2812c : word) = Some W_2812c.
Proof. vm_refl. Qed.
Lemma D_2812c : decode_any W_2812c = Some (OpImm ALU_ADD 1 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28130 : bv 32 := 0x00080613.
Lemma F_28130 : fetch_word Ubsan.M.loaded_segments (0x28130 : word) = Some W_28130.
Proof. vm_refl. Qed.
Lemma D_28130 : decode_any W_28130 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28134 : bv 32 := 0x000d079b.
Lemma F_28134 : fetch_word Ubsan.M.loaded_segments (0x28134 : word) = Some W_28134.
Proof. vm_refl. Qed.
Lemma D_28134 : decode_any W_28134 = Some (OpImm32 15 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28138 : bv 32 := 0x0207ce63.
Lemma F_28138 : fetch_word Ubsan.M.loaded_segments (0x28138 : word) = Some W_28138.
Proof. vm_refl. Qed.
Lemma D_28138 : decode_any W_28138 = Some (Branch BC_LT 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_2813c : bv 32 := 0x00060393.
Lemma F_2813c : fetch_word Ubsan.M.loaded_segments (0x2813c : word) = Some W_2813c.
Proof. vm_refl. Qed.
Lemma D_2813c : decode_any W_2813c = Some (OpImm ALU_ADD 7 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28140 : bv 32 := 0x05c0006f.
Lemma F_28140 : fetch_word Ubsan.M.loaded_segments (0x28140 : word) = Some W_28140.
Proof. vm_refl. Qed.
Lemma D_28140 : decode_any W_28140 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_28144 : bv 32 := 0x410d00b3.
Lemma F_28144 : fetch_word Ubsan.M.loaded_segments (0x28144 : word) = Some W_28144.
Proof. vm_refl. Qed.
Lemma D_28144 : decode_any W_28144 = Some (Op ALU_SUB 1 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28148 : bv 32 := 0x410d063b.
Lemma F_28148 : fetch_word Ubsan.M.loaded_segments (0x28148 : word) = Some W_28148.
Proof. vm_refl. Qed.
Lemma D_28148 : decode_any W_28148 = Some (Op32 ALU_SUB 12 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2814c : bv 32 := 0x00160463.
Lemma F_2814c : fetch_word Ubsan.M.loaded_segments (0x2814c : word) = Some W_2814c.
Proof. vm_refl. Qed.
Lemma D_2814c : decode_any W_2814c = Some (Branch BC_EQ 12 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28150 : bv 32 := 0x6580206f.
Lemma F_28150 : fetch_word Ubsan.M.loaded_segments (0x28150 : word) = Some W_28150.
Proof. vm_refl. Qed.
Lemma D_28150 : decode_any W_28150 = Some (Jal 0 9816, 4%Z).
Proof. vm_refl. Qed.

Definition W_28154 : bv 32 := 0x010b07b3.
Lemma F_28154 : fetch_word Ubsan.M.loaded_segments (0x28154 : word) = Some W_28154.
Proof. vm_refl. Qed.
Lemma D_28154 : decode_any W_28154 = Some (Op ALU_ADD 15 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28158 : bv 32 := 0x010b063b.
Lemma F_28158 : fetch_word Ubsan.M.loaded_segments (0x28158 : word) = Some W_28158.
Proof. vm_refl. Qed.
Lemma D_28158 : decode_any W_28158 = Some (Op32 ALU_ADD 12 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2815c : bv 32 := 0x00f60463.
Lemma F_2815c : fetch_word Ubsan.M.loaded_segments (0x2815c : word) = Some W_2815c.
Proof. vm_refl. Qed.
Lemma D_2815c : decode_any W_2815c = Some (Branch BC_EQ 12 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28160 : bv 32 := 0x6480206f.
Lemma F_28160 : fetch_word Ubsan.M.loaded_segments (0x28160 : word) = Some W_28160.
Proof. vm_refl. Qed.
Lemma D_28160 : decode_any W_28160 = Some (Jal 0 9800, 4%Z).
Proof. vm_refl. Qed.

Definition W_28164 : bv 32 := 0x00000613.
Lemma F_28164 : fetch_word Ubsan.M.loaded_segments (0x28164 : word) = Some W_28164.
Proof. vm_refl. Qed.
Lemma D_28164 : decode_any W_28164 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28168 : bv 32 := 0x00078b13.
Lemma F_28168 : fetch_word Ubsan.M.loaded_segments (0x28168 : word) = Some W_28168.
Proof. vm_refl. Qed.
Lemma D_28168 : decode_any W_28168 = Some (OpImm ALU_ADD 22 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2816c : bv 32 := 0x0000879b.
Lemma F_2816c : fetch_word Ubsan.M.loaded_segments (0x2816c : word) = Some W_2816c.
Proof. vm_refl. Qed.
Lemma D_2816c : decode_any W_2816c = Some (OpImm32 15 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28170 : bv 32 := 0xfc07d6e3.
Lemma F_28170 : fetch_word Ubsan.M.loaded_segments (0x28170 : word) = Some W_28170.
Proof. vm_refl. Qed.
Lemma D_28170 : decode_any W_28170 = Some (Branch BC_GE 15 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_28174 : bv 32 := 0x40f603b3.
Lemma F_28174 : fetch_word Ubsan.M.loaded_segments (0x28174 : word) = Some W_28174.
Proof. vm_refl. Qed.
Lemma D_28174 : decode_any W_28174 = Some (Op ALU_SUB 7 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28178 : bv 32 := 0x40f6063b.
Lemma F_28178 : fetch_word Ubsan.M.loaded_segments (0x28178 : word) = Some W_28178.
Proof. vm_refl. Qed.
Lemma D_28178 : decode_any W_28178 = Some (Op32 ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2817c : bv 32 := 0x00760463.
Lemma F_2817c : fetch_word Ubsan.M.loaded_segments (0x2817c : word) = Some W_2817c.
Proof. vm_refl. Qed.
Lemma D_2817c : decode_any W_2817c = Some (Branch BC_EQ 12 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28180 : bv 32 := 0x6280206f.
Lemma F_28180 : fetch_word Ubsan.M.loaded_segments (0x28180 : word) = Some W_28180.
Proof. vm_refl. Qed.
Lemma D_28180 : decode_any W_28180 = Some (Jal 0 9768, 4%Z).
Proof. vm_refl. Qed.

Definition W_28184 : bv 32 := 0x000b061b.
Lemma F_28184 : fetch_word Ubsan.M.loaded_segments (0x28184 : word) = Some W_28184.
Proof. vm_refl. Qed.
Lemma D_28184 : decode_any W_28184 = Some (OpImm32 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28188 : bv 32 := 0x00f60b33.
Lemma F_28188 : fetch_word Ubsan.M.loaded_segments (0x28188 : word) = Some W_28188.
Proof. vm_refl. Qed.
Lemma D_28188 : decode_any W_28188 = Some (Op ALU_ADD 22 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2818c : bv 32 := 0x00f6063b.
Lemma F_2818c : fetch_word Ubsan.M.loaded_segments (0x2818c : word) = Some W_2818c.
Proof. vm_refl. Qed.
Lemma D_2818c : decode_any W_2818c = Some (Op32 ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28190 : bv 32 := 0x01660463.
Lemma F_28190 : fetch_word Ubsan.M.loaded_segments (0x28190 : word) = Some W_28190.
Proof. vm_refl. Qed.
Lemma D_28190 : decode_any W_28190 = Some (Branch BC_EQ 12 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28194 : bv 32 := 0x6140206f.
Lemma F_28194 : fetch_word Ubsan.M.loaded_segments (0x28194 : word) = Some W_28194.
Proof. vm_refl. Qed.
Lemma D_28194 : decode_any W_28194 = Some (Jal 0 9748, 4%Z).
Proof. vm_refl. Qed.

Definition W_28198 : bv 32 := 0x00000093.
Lemma F_28198 : fetch_word Ubsan.M.loaded_segments (0x28198 : word) = Some W_28198.
Proof. vm_refl. Qed.
Lemma D_28198 : decode_any W_28198 = Some (OpImm ALU_ADD 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2819c : bv 32 := 0x000b061b.
Lemma F_2819c : fetch_word Ubsan.M.loaded_segments (0x2819c : word) = Some W_2819c.
Proof. vm_refl. Qed.
Lemma D_2819c : decode_any W_2819c = Some (OpImm32 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_281a0 : bv 32 := 0x0003839b.
Lemma F_281a0 : fetch_word Ubsan.M.loaded_segments (0x281a0 : word) = Some W_281a0.
Proof. vm_refl. Qed.
Lemma D_281a0 : decode_any W_281a0 = Some (OpImm32 7 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_281a4 : bv 32 := 0x00c387b3.
Lemma F_281a4 : fetch_word Ubsan.M.loaded_segments (0x281a4 : word) = Some W_281a4.
Proof. vm_refl. Qed.
Lemma D_281a4 : decode_any W_281a4 = Some (Op ALU_ADD 15 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_281a8 : bv 32 := 0x00c388bb.
Lemma F_281a8 : fetch_word Ubsan.M.loaded_segments (0x281a8 : word) = Some W_281a8.
Proof. vm_refl. Qed.
Lemma D_281a8 : decode_any W_281a8 = Some (Op32 ALU_ADD 17 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_281ac : bv 32 := 0x00f88463.
Lemma F_281ac : fetch_word Ubsan.M.loaded_segments (0x281ac : word) = Some W_281ac.
Proof. vm_refl. Qed.
Lemma D_281ac : decode_any W_281ac = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_281b0 : bv 32 := 0x5f80206f.
Lemma F_281b0 : fetch_word Ubsan.M.loaded_segments (0x281b0 : word) = Some W_281b0.
Proof. vm_refl. Qed.
Lemma D_281b0 : decode_any W_281b0 = Some (Jal 0 9720, 4%Z).
Proof. vm_refl. Qed.

Definition W_281b4 : bv 32 := 0x0007879b.
Lemma F_281b4 : fetch_word Ubsan.M.loaded_segments (0x281b4 : word) = Some W_281b4.
Proof. vm_refl. Qed.
Lemma D_281b4 : decode_any W_281b4 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_281b8 : bv 32 := 0x4177893b.
Lemma F_281b8 : fetch_word Ubsan.M.loaded_segments (0x281b8 : word) = Some W_281b8.
Proof. vm_refl. Qed.
Lemma D_281b8 : decode_any W_281b8 = Some (Op32 ALU_SUB 18 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_281bc : bv 32 := 0x417787b3.
Lemma F_281bc : fetch_word Ubsan.M.loaded_segments (0x281bc : word) = Some W_281bc.
Proof. vm_refl. Qed.
Lemma D_281bc : decode_any W_281bc = Some (Op ALU_SUB 15 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_281c0 : bv 32 := 0x00f90463.
Lemma F_281c0 : fetch_word Ubsan.M.loaded_segments (0x281c0 : word) = Some W_281c0.
Proof. vm_refl. Qed.
Lemma D_281c0 : decode_any W_281c0 = Some (Branch BC_EQ 18 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_281c4 : bv 32 := 0x5e40206f.
Lemma F_281c4 : fetch_word Ubsan.M.loaded_segments (0x281c4 : word) = Some W_281c4.
Proof. vm_refl. Qed.
Lemma D_281c4 : decode_any W_281c4 = Some (Jal 0 9700, 4%Z).
Proof. vm_refl. Qed.

Definition W_281c8 : bv 32 := 0x01205a63.
Lemma F_281c8 : fetch_word Ubsan.M.loaded_segments (0x281c8 : word) = Some W_281c8.
Proof. vm_refl. Qed.
Lemma D_281c8 : decode_any W_281c8 = Some (Branch BC_GE 0 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_281cc : bv 32 := 0x41260b33.
Lemma F_281cc : fetch_word Ubsan.M.loaded_segments (0x281cc : word) = Some W_281cc.
Proof. vm_refl. Qed.
Lemma D_281cc : decode_any W_281cc = Some (Op ALU_SUB 22 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_281d0 : bv 32 := 0x4126063b.
Lemma F_281d0 : fetch_word Ubsan.M.loaded_segments (0x281d0 : word) = Some W_281d0.
Proof. vm_refl. Qed.
Lemma D_281d0 : decode_any W_281d0 = Some (Op32 ALU_SUB 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_281d4 : bv 32 := 0x01660463.
Lemma F_281d4 : fetch_word Ubsan.M.loaded_segments (0x281d4 : word) = Some W_281d4.
Proof. vm_refl. Qed.
Lemma D_281d4 : decode_any W_281d4 = Some (Branch BC_EQ 12 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_281d8 : bv 32 := 0x5d00206f.
Lemma F_281d8 : fetch_word Ubsan.M.loaded_segments (0x281d8 : word) = Some W_281d8.
Proof. vm_refl. Qed.
Lemma D_281d8 : decode_any W_281d8 = Some (Jal 0 9680, 4%Z).
Proof. vm_refl. Qed.

Definition W_281dc : bv 32 := 0x000b061b.
Lemma F_281dc : fetch_word Ubsan.M.loaded_segments (0x281dc : word) = Some W_281dc.
Proof. vm_refl. Qed.
Lemma D_281dc : decode_any W_281dc = Some (OpImm32 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_281e0 : bv 32 := 0x0000829b.
Lemma F_281e0 : fetch_word Ubsan.M.loaded_segments (0x281e0 : word) = Some W_281e0.
Proof. vm_refl. Qed.
Lemma D_281e0 : decode_any W_281e0 = Some (OpImm32 5 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_281e4 : bv 32 := 0x00c287b3.
Lemma F_281e4 : fetch_word Ubsan.M.loaded_segments (0x281e4 : word) = Some W_281e4.
Proof. vm_refl. Qed.
Lemma D_281e4 : decode_any W_281e4 = Some (Op ALU_ADD 15 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_281e8 : bv 32 := 0x00c288bb.
Lemma F_281e8 : fetch_word Ubsan.M.loaded_segments (0x281e8 : word) = Some W_281e8.
Proof. vm_refl. Qed.
Lemma D_281e8 : decode_any W_281e8 = Some (Op32 ALU_ADD 17 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_281ec : bv 32 := 0x00f88463.
Lemma F_281ec : fetch_word Ubsan.M.loaded_segments (0x281ec : word) = Some W_281ec.
Proof. vm_refl. Qed.
Lemma D_281ec : decode_any W_281ec = Some (Branch BC_EQ 17 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_281f0 : bv 32 := 0x5b80206f.
Lemma F_281f0 : fetch_word Ubsan.M.loaded_segments (0x281f0 : word) = Some W_281f0.
Proof. vm_refl. Qed.
Lemma D_281f0 : decode_any W_281f0 = Some (Jal 0 9656, 4%Z).
Proof. vm_refl. Qed.

Definition W_281f4 : bv 32 := 0x0007889b.
Lemma F_281f4 : fetch_word Ubsan.M.loaded_segments (0x281f4 : word) = Some W_281f4.
Proof. vm_refl. Qed.
Lemma D_281f4 : decode_any W_281f4 = Some (OpImm32 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_281f8 : bv 32 := 0x41c887bb.
Lemma F_281f8 : fetch_word Ubsan.M.loaded_segments (0x281f8 : word) = Some W_281f8.
Proof. vm_refl. Qed.
Lemma D_281f8 : decode_any W_281f8 = Some (Op32 ALU_SUB 15 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_281fc : bv 32 := 0x41c888b3.
Lemma F_281fc : fetch_word Ubsan.M.loaded_segments (0x281fc : word) = Some W_281fc.
Proof. vm_refl. Qed.
Lemma D_281fc : decode_any W_281fc = Some (Op ALU_SUB 17 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_28200 : bv 32 := 0x01178463.
Lemma F_28200 : fetch_word Ubsan.M.loaded_segments (0x28200 : word) = Some W_28200.
Proof. vm_refl. Qed.
Lemma D_28200 : decode_any W_28200 = Some (Branch BC_EQ 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28204 : bv 32 := 0x5a40206f.
Lemma F_28204 : fetch_word Ubsan.M.loaded_segments (0x28204 : word) = Some W_28204.
Proof. vm_refl. Qed.
Lemma D_28204 : decode_any W_28204 = Some (Jal 0 9636, 4%Z).
Proof. vm_refl. Qed.

Definition W_28208 : bv 32 := 0x00f05a63.
Lemma F_28208 : fetch_word Ubsan.M.loaded_segments (0x28208 : word) = Some W_28208.
Proof. vm_refl. Qed.
Lemma D_28208 : decode_any W_28208 = Some (Branch BC_GE 0 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_2820c : bv 32 := 0x40f60b33.
Lemma F_2820c : fetch_word Ubsan.M.loaded_segments (0x2820c : word) = Some W_2820c.
Proof. vm_refl. Qed.
Lemma D_2820c : decode_any W_2820c = Some (Op ALU_SUB 22 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28210 : bv 32 := 0x40f6063b.
Lemma F_28210 : fetch_word Ubsan.M.loaded_segments (0x28210 : word) = Some W_28210.
Proof. vm_refl. Qed.
Lemma D_28210 : decode_any W_28210 = Some (Op32 ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28214 : bv 32 := 0x01660463.
Lemma F_28214 : fetch_word Ubsan.M.loaded_segments (0x28214 : word) = Some W_28214.
Proof. vm_refl. Qed.
Lemma D_28214 : decode_any W_28214 = Some (Branch BC_EQ 12 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28218 : bv 32 := 0x5900206f.
Lemma F_28218 : fetch_word Ubsan.M.loaded_segments (0x28218 : word) = Some W_28218.
Proof. vm_refl. Qed.
Lemma D_28218 : decode_any W_28218 = Some (Jal 0 9616, 4%Z).
Proof. vm_refl. Qed.

Definition W_2821c : bv 32 := 0x0004049b.
Lemma F_2821c : fetch_word Ubsan.M.loaded_segments (0x2821c : word) = Some W_2821c.
Proof. vm_refl. Qed.
Lemma D_2821c : decode_any W_2821c = Some (OpImm32 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28220 : bv 32 := 0x00904463.
Lemma F_28220 : fetch_word Ubsan.M.loaded_segments (0x28220 : word) = Some W_28220.
Proof. vm_refl. Qed.
Lemma D_28220 : decode_any W_28220 = Some (Branch BC_LT 0 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28224 : bv 32 := 0x6480706f.
Lemma F_28224 : fetch_word Ubsan.M.loaded_segments (0x28224 : word) = Some W_28224.
Proof. vm_refl. Qed.
Lemma D_28224 : decode_any W_28224 = Some (Jal 0 30280, 4%Z).
Proof. vm_refl. Qed.

Definition W_28228 : bv 32 := 0x000b0b1b.
Lemma F_28228 : fetch_word Ubsan.M.loaded_segments (0x28228 : word) = Some W_28228.
Proof. vm_refl. Qed.
Lemma D_28228 : decode_any W_28228 = Some (OpImm32 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2822c : bv 32 := 0x09613023.
Lemma F_2822c : fetch_word Ubsan.M.loaded_segments (0x2822c : word) = Some W_2822c.
Proof. vm_refl. Qed.
Lemma D_2822c : decode_any W_2822c = Some (Store SZ8 2 22 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_28230 : bv 32 := 0x01604463.
Lemma F_28230 : fetch_word Ubsan.M.loaded_segments (0x28230 : word) = Some W_28230.
Proof. vm_refl. Qed.
Lemma D_28230 : decode_any W_28230 = Some (Branch BC_LT 0 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28234 : bv 32 := 0x6380706f.
Lemma F_28234 : fetch_word Ubsan.M.loaded_segments (0x28234 : word) = Some W_28234.
Proof. vm_refl. Qed.
Lemma D_28234 : decode_any W_28234 = Some (Jal 0 30264, 4%Z).
Proof. vm_refl. Qed.

Definition W_28238 : bv 32 := 0x01bce633.
Lemma F_28238 : fetch_word Ubsan.M.loaded_segments (0x28238 : word) = Some W_28238.
Proof. vm_refl. Qed.
Lemma D_28238 : decode_any W_28238 = Some (Op ALU_OR 12 25 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_2823c : bv 32 := 0x01f67613.
Lemma F_2823c : fetch_word Ubsan.M.loaded_segments (0x2823c : word) = Some W_2823c.
Proof. vm_refl. Qed.
Lemma D_2823c : decode_any W_2823c = Some (OpImm ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28240 : bv 32 := 0x04613c23.
Lemma F_28240 : fetch_word Ubsan.M.loaded_segments (0x28240 : word) = Some W_28240.
Proof. vm_refl. Qed.
Lemma D_28240 : decode_any W_28240 = Some (Store SZ8 2 6 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28244 : bv 32 := 0x18060263.
Lemma F_28244 : fetch_word Ubsan.M.loaded_segments (0x28244 : word) = Some W_28244.
Proof. vm_refl. Qed.
Lemma D_28244 : decode_any W_28244 = Some (Branch BC_EQ 12 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_28248 : bv 32 := 0x02113423.
Lemma F_28248 : fetch_word Ubsan.M.loaded_segments (0x28248 : word) = Some W_28248.
Proof. vm_refl. Qed.
Lemma D_28248 : decode_any W_28248 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_2824c : bv 32 := 0x03a13823.
Lemma F_2824c : fetch_word Ubsan.M.loaded_segments (0x2824c : word) = Some W_2824c.
Proof. vm_refl. Qed.
Lemma D_2824c : decode_any W_2824c = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_28250 : bv 32 := 0x01fcf093.
Lemma F_28250 : fetch_word Ubsan.M.loaded_segments (0x28250 : word) = Some W_28250.
Proof. vm_refl. Qed.
Lemma D_28250 : decode_any W_28250 = Some (OpImm ALU_AND 1 25 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28254 : bv 32 := 0x01fdf613.
Lemma F_28254 : fetch_word Ubsan.M.loaded_segments (0x28254 : word) = Some W_28254.
Proof. vm_refl. Qed.
Lemma D_28254 : decode_any W_28254 = Some (OpImm ALU_AND 12 27 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28258 : bv 32 := 0x05013023.
Lemma F_28258 : fetch_word Ubsan.M.loaded_segments (0x28258 : word) = Some W_28258.
Proof. vm_refl. Qed.
Lemma D_28258 : decode_any W_28258 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_2825c : bv 32 := 0x05c13823.
Lemma F_2825c : fetch_word Ubsan.M.loaded_segments (0x2825c : word) = Some W_2825c.
Proof. vm_refl. Qed.
Lemma D_2825c : decode_any W_2825c = Some (Store SZ8 2 28 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_28260 : bv 32 := 0x05213423.
Lemma F_28260 : fetch_word Ubsan.M.loaded_segments (0x28260 : word) = Some W_28260.
Proof. vm_refl. Qed.
Lemma D_28260 : decode_any W_28260 = Some (Store SZ8 2 18 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_28264 : bv 32 := 0x03713c23.
Lemma F_28264 : fetch_word Ubsan.M.loaded_segments (0x28264 : word) = Some W_28264.
Proof. vm_refl. Qed.
Lemma D_28264 : decode_any W_28264 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_28268 : bv 32 := 0x18c09663.
Lemma F_28268 : fetch_word Ubsan.M.loaded_segments (0x28268 : word) = Some W_28268.
Proof. vm_refl. Qed.
Lemma D_28268 : decode_any W_28268 = Some (Branch BC_NE 1 12 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_2826c : bv 32 := 0x60008e63.
Lemma F_2826c : fetch_word Ubsan.M.loaded_segments (0x2826c : word) = Some W_2826c.
Proof. vm_refl. Qed.
Lemma D_2826c : decode_any W_2826c = Some (Branch BC_EQ 1 0 1564, 4%Z).
Proof. vm_refl. Qed.

Definition W_28270 : bv 32 := 0x02000613.
Lemma F_28270 : fetch_word Ubsan.M.loaded_segments (0x28270 : word) = Some W_28270.
Proof. vm_refl. Qed.
Lemma D_28270 : decode_any W_28270 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28274 : bv 32 := 0xfffea797.
Lemma F_28274 : fetch_word Ubsan.M.loaded_segments (0x28274 : word) = Some W_28274.
Proof. vm_refl. Qed.
Lemma D_28274 : decode_any W_28274 = Some (Auipc 15 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_28278 : bv 32 := 0x40160633.
Lemma F_28278 : fetch_word Ubsan.M.loaded_segments (0x28278 : word) = Some W_28278.
Proof. vm_refl. Qed.
Lemma D_28278 : decode_any W_28278 = Some (Op ALU_SUB 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2827c : bv 32 := 0x67878793.
Lemma F_2827c : fetch_word Ubsan.M.loaded_segments (0x2827c : word) = Some W_2827c.
Proof. vm_refl. Qed.
Lemma D_2827c : decode_any W_2827c = Some (OpImm ALU_ADD 15 15 1656, 4%Z).
Proof. vm_refl. Qed.

Definition W_28280 : bv 32 := 0x00261813.
Lemma F_28280 : fetch_word Ubsan.M.loaded_segments (0x28280 : word) = Some W_28280.
Proof. vm_refl. Qed.
Lemma D_28280 : decode_any W_28280 = Some (ShiftImm ALU_SLL 16 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28284 : bv 32 := 0xfff7c893.
Lemma F_28284 : fetch_word Ubsan.M.loaded_segments (0x28284 : word) = Some W_28284.
Proof. vm_refl. Qed.
Lemma D_28284 : decode_any W_28284 = Some (OpImm ALU_XOR 17 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28288 : bv 32 := 0x0108f463.
Lemma F_28288 : fetch_word Ubsan.M.loaded_segments (0x28288 : word) = Some W_28288.
Proof. vm_refl. Qed.
Lemma D_28288 : decode_any W_28288 = Some (Branch BC_GEU 17 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2828c : bv 32 := 0x51c0206f.
Lemma F_2828c : fetch_word Ubsan.M.loaded_segments (0x2828c : word) = Some W_2828c.
Proof. vm_refl. Qed.
Lemma D_2828c : decode_any W_2828c = Some (Jal 0 9500, 4%Z).
Proof. vm_refl. Qed.

Definition W_28290 : bv 32 := 0x02770e33.
Lemma F_28290 : fetch_word Ubsan.M.loaded_segments (0x28290 : word) = Some W_28290.
Proof. vm_refl. Qed.
Lemma D_28290 : decode_any W_28290 = Some (Mul M_MUL 28 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28294 : bv 32 := 0x027708bb.
Lemma F_28294 : fetch_word Ubsan.M.loaded_segments (0x28294 : word) = Some W_28294.
Proof. vm_refl. Qed.
Lemma D_28294 : decode_any W_28294 = Some (Mul32 M_MUL 17 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28298 : bv 32 := 0x01c88463.
Lemma F_28298 : fetch_word Ubsan.M.loaded_segments (0x28298 : word) = Some W_28298.
Proof. vm_refl. Qed.
Lemma D_28298 : decode_any W_28298 = Some (Branch BC_EQ 17 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2829c : bv 32 := 0x50c0206f.
Lemma F_2829c : fetch_word Ubsan.M.loaded_segments (0x2829c : word) = Some W_2829c.
Proof. vm_refl. Qed.
Lemma D_2829c : decode_any W_2829c = Some (Jal 0 9484, 4%Z).
Proof. vm_refl. Qed.

Definition W_282a0 : bv 32 := 0x000e0e1b.
Lemma F_282a0 : fetch_word Ubsan.M.loaded_segments (0x282a0 : word) = Some W_282a0.
Proof. vm_refl. Qed.
Lemma D_282a0 : decode_any W_282a0 = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_282a4 : bv 32 := 0x002e1893.
Lemma F_282a4 : fetch_word Ubsan.M.loaded_segments (0x282a4 : word) = Some W_282a4.
Proof. vm_refl. Qed.
Lemma D_282a4 : decode_any W_282a4 = Some (ShiftImm ALU_SLL 17 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_282a8 : bv 32 := 0x00a888b3.
Lemma F_282a8 : fetch_word Ubsan.M.loaded_segments (0x282a8 : word) = Some W_282a8.
Proof. vm_refl. Qed.
Lemma D_282a8 : decode_any W_282a8 = Some (Op ALU_ADD 17 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_282ac : bv 32 := 0x00a03333.
Lemma F_282ac : fetch_word Ubsan.M.loaded_segments (0x282ac : word) = Some W_282ac.
Proof. vm_refl. Qed.
Lemma D_282ac : decode_any W_282ac = Some (Op ALU_SLTU 6 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_282b0 : bv 32 := 0x0018be93.
Lemma F_282b0 : fetch_word Ubsan.M.loaded_segments (0x282b0 : word) = Some W_282b0.
Proof. vm_refl. Qed.
Lemma D_282b0 : decode_any W_282b0 = Some (OpImm ALU_SLTU 29 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_282b4 : bv 32 := 0x01d31463.
Lemma F_282b4 : fetch_word Ubsan.M.loaded_segments (0x282b4 : word) = Some W_282b4.
Proof. vm_refl. Qed.
Lemma D_282b4 : decode_any W_282b4 = Some (Branch BC_NE 6 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_282b8 : bv 32 := 0x4f00206f.
Lemma F_282b8 : fetch_word Ubsan.M.loaded_segments (0x282b8 : word) = Some W_282b8.
Proof. vm_refl. Qed.
Lemma D_282b8 : decode_any W_282b8 = Some (Jal 0 9456, 4%Z).
Proof. vm_refl. Qed.

Definition W_282bc : bv 32 := 0x00a8beb3.
Lemma F_282bc : fetch_word Ubsan.M.loaded_segments (0x282bc : word) = Some W_282bc.
Proof. vm_refl. Qed.
Lemma D_282bc : decode_any W_282bc = Some (Op ALU_SLTU 29 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_282c0 : bv 32 := 0x000e2e13.
Lemma F_282c0 : fetch_word Ubsan.M.loaded_segments (0x282c0 : word) = Some W_282c0.
Proof. vm_refl. Qed.
Lemma D_282c0 : decode_any W_282c0 = Some (OpImm ALU_SLT 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_282c4 : bv 32 := 0x01cece33.
Lemma F_282c4 : fetch_word Ubsan.M.loaded_segments (0x282c4 : word) = Some W_282c4.
Proof. vm_refl. Qed.
Lemma D_282c4 : decode_any W_282c4 = Some (Op ALU_XOR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_282c8 : bv 32 := 0x001e4e13.
Lemma F_282c8 : fetch_word Ubsan.M.loaded_segments (0x282c8 : word) = Some W_282c8.
Proof. vm_refl. Qed.
Lemma D_282c8 : decode_any W_282c8 = Some (OpImm ALU_XOR 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_282cc : bv 32 := 0x000e1463.
Lemma F_282cc : fetch_word Ubsan.M.loaded_segments (0x282cc : word) = Some W_282cc.
Proof. vm_refl. Qed.
Lemma D_282cc : decode_any W_282cc = Some (Branch BC_NE 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_282d0 : bv 32 := 0x4d80206f.
Lemma F_282d0 : fetch_word Ubsan.M.loaded_segments (0x282d0 : word) = Some W_282d0.
Proof. vm_refl. Qed.
Lemma D_282d0 : decode_any W_282d0 = Some (Jal 0 9432, 4%Z).
Proof. vm_refl. Qed.

Definition W_282d4 : bv 32 := 0x405cde1b.
Lemma F_282d4 : fetch_word Ubsan.M.loaded_segments (0x282d4 : word) = Some W_282d4.
Proof. vm_refl. Qed.
Lemma D_282d4 : decode_any W_282d4 = Some (ShiftImm32 ALU_SRA 28 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_282d8 : bv 32 := 0x002e1a13.
Lemma F_282d8 : fetch_word Ubsan.M.loaded_segments (0x282d8 : word) = Some W_282d8.
Proof. vm_refl. Qed.
Lemma D_282d8 : decode_any W_282d8 = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_282dc : bv 32 := 0x01488a33.
Lemma F_282dc : fetch_word Ubsan.M.loaded_segments (0x282dc : word) = Some W_282dc.
Proof. vm_refl. Qed.
Lemma D_282dc : decode_any W_282dc = Some (Op ALU_ADD 20 17 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_282e0 : bv 32 := 0x001a3e93.
Lemma F_282e0 : fetch_word Ubsan.M.loaded_segments (0x282e0 : word) = Some W_282e0.
Proof. vm_refl. Qed.
Lemma D_282e0 : decode_any W_282e0 = Some (OpImm ALU_SLTU 29 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_282e4 : bv 32 := 0x01d31463.
Lemma F_282e4 : fetch_word Ubsan.M.loaded_segments (0x282e4 : word) = Some W_282e4.
Proof. vm_refl. Qed.
Lemma D_282e4 : decode_any W_282e4 = Some (Branch BC_NE 6 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_282e8 : bv 32 := 0x4c00206f.
Lemma F_282e8 : fetch_word Ubsan.M.loaded_segments (0x282e8 : word) = Some W_282e8.
Proof. vm_refl. Qed.
Lemma D_282e8 : decode_any W_282e8 = Some (Jal 0 9408, 4%Z).
Proof. vm_refl. Qed.

Definition W_282ec : bv 32 := 0x011a38b3.
Lemma F_282ec : fetch_word Ubsan.M.loaded_segments (0x282ec : word) = Some W_282ec.
Proof. vm_refl. Qed.
Lemma D_282ec : decode_any W_282ec = Some (Op ALU_SLTU 17 20 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_282f0 : bv 32 := 0x000e2313.
Lemma F_282f0 : fetch_word Ubsan.M.loaded_segments (0x282f0 : word) = Some W_282f0.
Proof. vm_refl. Qed.
Lemma D_282f0 : decode_any W_282f0 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_282f4 : bv 32 := 0x0068c8b3.
Lemma F_282f4 : fetch_word Ubsan.M.loaded_segments (0x282f4 : word) = Some W_282f4.
Proof. vm_refl. Qed.
Lemma D_282f4 : decode_any W_282f4 = Some (Op ALU_XOR 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_282f8 : bv 32 := 0x0018c893.
Lemma F_282f8 : fetch_word Ubsan.M.loaded_segments (0x282f8 : word) = Some W_282f8.
Proof. vm_refl. Qed.
Lemma D_282f8 : decode_any W_282f8 = Some (OpImm ALU_XOR 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_282fc : bv 32 := 0x00089463.
Lemma F_282fc : fetch_word Ubsan.M.loaded_segments (0x282fc : word) = Some W_282fc.
Proof. vm_refl. Qed.
Lemma D_282fc : decode_any W_282fc = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28300 : bv 32 := 0x4a80206f.
Lemma F_28300 : fetch_word Ubsan.M.loaded_segments (0x28300 : word) = Some W_28300.
Proof. vm_refl. Qed.
Lemma D_28300 : decode_any W_28300 = Some (Jal 0 9384, 4%Z).
Proof. vm_refl. Qed.

Definition W_28304 : bv 32 := 0x05813883.
Lemma F_28304 : fetch_word Ubsan.M.loaded_segments (0x28304 : word) = Some W_28304.
Proof. vm_refl. Qed.
Lemma D_28304 : decode_any W_28304 = Some (Load SZ8 true 17 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28308 : bv 32 := 0x02588e33.
Lemma F_28308 : fetch_word Ubsan.M.loaded_segments (0x28308 : word) = Some W_28308.
Proof. vm_refl. Qed.
Lemma D_28308 : decode_any W_28308 = Some (Mul M_MUL 28 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2830c : bv 32 := 0x025888bb.
Lemma F_2830c : fetch_word Ubsan.M.loaded_segments (0x2830c : word) = Some W_2830c.
Proof. vm_refl. Qed.
Lemma D_2830c : decode_any W_2830c = Some (Mul32 M_MUL 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28310 : bv 32 := 0x01c88463.
Lemma F_28310 : fetch_word Ubsan.M.loaded_segments (0x28310 : word) = Some W_28310.
Proof. vm_refl. Qed.
Lemma D_28310 : decode_any W_28310 = Some (Branch BC_EQ 17 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28314 : bv 32 := 0x4940206f.
Lemma F_28314 : fetch_word Ubsan.M.loaded_segments (0x28314 : word) = Some W_28314.
Proof. vm_refl. Qed.
Lemma D_28314 : decode_any W_28314 = Some (Jal 0 9364, 4%Z).
Proof. vm_refl. Qed.

Definition W_28318 : bv 32 := 0x000e0e1b.
Lemma F_28318 : fetch_word Ubsan.M.loaded_segments (0x28318 : word) = Some W_28318.
Proof. vm_refl. Qed.
Lemma D_28318 : decode_any W_28318 = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2831c : bv 32 := 0x002e1313.
Lemma F_2831c : fetch_word Ubsan.M.loaded_segments (0x2831c : word) = Some W_2831c.
Proof. vm_refl. Qed.
Lemma D_2831c : decode_any W_2831c = Some (ShiftImm ALU_SLL 6 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28320 : bv 32 := 0x01330333.
Lemma F_28320 : fetch_word Ubsan.M.loaded_segments (0x28320 : word) = Some W_28320.
Proof. vm_refl. Qed.
Lemma D_28320 : decode_any W_28320 = Some (Op ALU_ADD 6 6 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28324 : bv 32 := 0x013038b3.
Lemma F_28324 : fetch_word Ubsan.M.loaded_segments (0x28324 : word) = Some W_28324.
Proof. vm_refl. Qed.
Lemma D_28324 : decode_any W_28324 = Some (Op ALU_SLTU 17 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28328 : bv 32 := 0x00133e93.
Lemma F_28328 : fetch_word Ubsan.M.loaded_segments (0x28328 : word) = Some W_28328.
Proof. vm_refl. Qed.
Lemma D_28328 : decode_any W_28328 = Some (OpImm ALU_SLTU 29 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2832c : bv 32 := 0x01d89463.
Lemma F_2832c : fetch_word Ubsan.M.loaded_segments (0x2832c : word) = Some W_2832c.
Proof. vm_refl. Qed.
Lemma D_2832c : decode_any W_2832c = Some (Branch BC_NE 17 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28330 : bv 32 := 0x4780206f.
Lemma F_28330 : fetch_word Ubsan.M.loaded_segments (0x28330 : word) = Some W_28330.
Proof. vm_refl. Qed.
Lemma D_28330 : decode_any W_28330 = Some (Jal 0 9336, 4%Z).
Proof. vm_refl. Qed.

Definition W_28334 : bv 32 := 0x01333eb3.
Lemma F_28334 : fetch_word Ubsan.M.loaded_segments (0x28334 : word) = Some W_28334.
Proof. vm_refl. Qed.
Lemma D_28334 : decode_any W_28334 = Some (Op ALU_SLTU 29 6 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28338 : bv 32 := 0x000e2e13.
Lemma F_28338 : fetch_word Ubsan.M.loaded_segments (0x28338 : word) = Some W_28338.
Proof. vm_refl. Qed.
Lemma D_28338 : decode_any W_28338 = Some (OpImm ALU_SLT 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2833c : bv 32 := 0x01cece33.
Lemma F_2833c : fetch_word Ubsan.M.loaded_segments (0x2833c : word) = Some W_2833c.
Proof. vm_refl. Qed.
Lemma D_2833c : decode_any W_2833c = Some (Op ALU_XOR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_28340 : bv 32 := 0x001e4e13.
Lemma F_28340 : fetch_word Ubsan.M.loaded_segments (0x28340 : word) = Some W_28340.
Proof. vm_refl. Qed.
Lemma D_28340 : decode_any W_28340 = Some (OpImm ALU_XOR 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28344 : bv 32 := 0x000e1463.
Lemma F_28344 : fetch_word Ubsan.M.loaded_segments (0x28344 : word) = Some W_28344.
Proof. vm_refl. Qed.
Lemma D_28344 : decode_any W_28344 = Some (Branch BC_NE 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28348 : bv 32 := 0x4600206f.
Lemma F_28348 : fetch_word Ubsan.M.loaded_segments (0x28348 : word) = Some W_28348.
Proof. vm_refl. Qed.
Lemma D_28348 : decode_any W_28348 = Some (Jal 0 9312, 4%Z).
Proof. vm_refl. Qed.

Definition W_2834c : bv 32 := 0x005dde1b.
Lemma F_2834c : fetch_word Ubsan.M.loaded_segments (0x2834c : word) = Some W_2834c.
Proof. vm_refl. Qed.
Lemma D_2834c : decode_any W_2834c = Some (ShiftImm32 ALU_SRL 28 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28350 : bv 32 := 0x002e1e13.
Lemma F_28350 : fetch_word Ubsan.M.loaded_segments (0x28350 : word) = Some W_28350.
Proof. vm_refl. Qed.
Lemma D_28350 : decode_any W_28350 = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28354 : bv 32 := 0x006e0ab3.
Lemma F_28354 : fetch_word Ubsan.M.loaded_segments (0x28354 : word) = Some W_28354.
Proof. vm_refl. Qed.
Lemma D_28354 : decode_any W_28354 = Some (Op ALU_ADD 21 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28358 : bv 32 := 0x006af463.
Lemma F_28358 : fetch_word Ubsan.M.loaded_segments (0x28358 : word) = Some W_28358.
Proof. vm_refl. Qed.
Lemma D_28358 : decode_any W_28358 = Some (Branch BC_GEU 21 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2835c : bv 32 := 0x44c0206f.
Lemma F_2835c : fetch_word Ubsan.M.loaded_segments (0x2835c : word) = Some W_2835c.
Proof. vm_refl. Qed.
Lemma D_2835c : decode_any W_2835c = Some (Jal 0 9292, 4%Z).
Proof. vm_refl. Qed.

Definition W_28360 : bv 32 := 0x001ab313.
Lemma F_28360 : fetch_word Ubsan.M.loaded_segments (0x28360 : word) = Some W_28360.
Proof. vm_refl. Qed.
Lemma D_28360 : decode_any W_28360 = Some (OpImm ALU_SLTU 6 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28364 : bv 32 := 0x0068c8b3.
Lemma F_28364 : fetch_word Ubsan.M.loaded_segments (0x28364 : word) = Some W_28364.
Proof. vm_refl. Qed.
Lemma D_28364 : decode_any W_28364 = Some (Op ALU_XOR 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28368 : bv 32 := 0x00089463.
Lemma F_28368 : fetch_word Ubsan.M.loaded_segments (0x28368 : word) = Some W_28368.
Proof. vm_refl. Qed.
Lemma D_28368 : decode_any W_28368 = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2836c : bv 32 := 0x43c0206f.
Lemma F_2836c : fetch_word Ubsan.M.loaded_segments (0x2836c : word) = Some W_2836c.
Proof. vm_refl. Qed.
Lemma D_2836c : decode_any W_2836c = Some (Jal 0 9276, 4%Z).
Proof. vm_refl. Qed.

Definition W_28370 : bv 32 := 0x010787b3.
Lemma F_28370 : fetch_word Ubsan.M.loaded_segments (0x28370 : word) = Some W_28370.
Proof. vm_refl. Qed.
Lemma D_28370 : decode_any W_28370 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28374 : bv 32 := 0x0007ab83.
Lemma F_28374 : fetch_word Ubsan.M.loaded_segments (0x28374 : word) = Some W_28374.
Proof. vm_refl. Qed.
Lemma D_28374 : decode_any W_28374 = Some (Load SZ4 true 23 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28378 : bv 32 := 0x40c4043b.
Lemma F_28378 : fetch_word Ubsan.M.loaded_segments (0x28378 : word) = Some W_28378.
Proof. vm_refl. Qed.
Lemma D_28378 : decode_any W_28378 = Some (Op32 ALU_SUB 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2837c : bv 32 := 0x74c4f063.
Lemma F_2837c : fetch_word Ubsan.M.loaded_segments (0x2837c : word) = Some W_2837c.
Proof. vm_refl. Qed.
Lemma D_2837c : decode_any W_2837c = Some (Branch BC_GEU 9 12 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_28380 : bv 32 := 0x0204061b.
Lemma F_28380 : fetch_word Ubsan.M.loaded_segments (0x28380 : word) = Some W_28380.
Proof. vm_refl. Qed.
Lemma D_28380 : decode_any W_28380 = Some (OpImm32 12 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28384 : bv 32 := 0x02000793.
Lemma F_28384 : fetch_word Ubsan.M.loaded_segments (0x28384 : word) = Some W_28384.
Proof. vm_refl. Qed.
Lemma D_28384 : decode_any W_28384 = Some (OpImm ALU_ADD 15 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28388 : bv 32 := 0x00c7f463.
Lemma F_28388 : fetch_word Ubsan.M.loaded_segments (0x28388 : word) = Some W_28388.
Proof. vm_refl. Qed.
Lemma D_28388 : decode_any W_28388 = Some (Branch BC_GEU 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2838c : bv 32 := 0x41c0206f.
Lemma F_2838c : fetch_word Ubsan.M.loaded_segments (0x2838c : word) = Some W_2838c.
Proof. vm_refl. Qed.
Lemma D_2838c : decode_any W_2838c = Some (Jal 0 9244, 4%Z).
Proof. vm_refl. Qed.

Definition W_28390 : bv 32 := 0x00261613.
Lemma F_28390 : fetch_word Ubsan.M.loaded_segments (0x28390 : word) = Some W_28390.
Proof. vm_refl. Qed.
Lemma D_28390 : decode_any W_28390 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28394 : bv 32 := 0xfffea797.
Lemma F_28394 : fetch_word Ubsan.M.loaded_segments (0x28394 : word) = Some W_28394.
Proof. vm_refl. Qed.
Lemma D_28394 : decode_any W_28394 = Some (Auipc 15 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_28398 : bv 32 := 0x5dc78793.
Lemma F_28398 : fetch_word Ubsan.M.loaded_segments (0x28398 : word) = Some W_28398.
Proof. vm_refl. Qed.
Lemma D_28398 : decode_any W_28398 = Some (OpImm ALU_ADD 15 15 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_2839c : bv 32 := 0xfff7c813.
Lemma F_2839c : fetch_word Ubsan.M.loaded_segments (0x2839c : word) = Some W_2839c.
Proof. vm_refl. Qed.
Lemma D_2839c : decode_any W_2839c = Some (OpImm ALU_XOR 16 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_283a0 : bv 32 := 0x00c87463.
Lemma F_283a0 : fetch_word Ubsan.M.loaded_segments (0x283a0 : word) = Some W_283a0.
Proof. vm_refl. Qed.
Lemma D_283a0 : decode_any W_283a0 = Some (Branch BC_GEU 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_283a4 : bv 32 := 0x4040206f.
Lemma F_283a4 : fetch_word Ubsan.M.loaded_segments (0x283a4 : word) = Some W_283a4.
Proof. vm_refl. Qed.
Lemma D_283a4 : decode_any W_283a4 = Some (Jal 0 9220, 4%Z).
Proof. vm_refl. Qed.

Definition W_283a8 : bv 32 := 0x00000f93.
Lemma F_283a8 : fetch_word Ubsan.M.loaded_segments (0x283a8 : word) = Some W_283a8.
Proof. vm_refl. Qed.
Lemma D_283a8 : decode_any W_283a8 = Some (OpImm ALU_ADD 31 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_283ac : bv 32 := 0x00000413.
Lemma F_283ac : fetch_word Ubsan.M.loaded_segments (0x283ac : word) = Some W_283ac.
Proof. vm_refl. Qed.
Lemma D_283ac : decode_any W_283ac = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_283b0 : bv 32 := 0x00000913.
Lemma F_283b0 : fetch_word Ubsan.M.loaded_segments (0x283b0 : word) = Some W_283b0.
Proof. vm_refl. Qed.
Lemma D_283b0 : decode_any W_283b0 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_283b4 : bv 32 := 0x00c78633.
Lemma F_283b4 : fetch_word Ubsan.M.loaded_segments (0x283b4 : word) = Some W_283b4.
Proof. vm_refl. Qed.
Lemma D_283b4 : decode_any W_283b4 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_283b8 : bv 32 := 0x00062783.
Lemma F_283b8 : fetch_word Ubsan.M.loaded_segments (0x283b8 : word) = Some W_283b8.
Proof. vm_refl. Qed.
Lemma D_283b8 : decode_any W_283b8 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_283bc : bv 32 := 0x00100613.
Lemma F_283bc : fetch_word Ubsan.M.loaded_segments (0x283bc : word) = Some W_283bc.
Proof. vm_refl. Qed.
Lemma D_283bc : decode_any W_283bc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_283c0 : bv 32 := 0x0177fbb3.
Lemma F_283c0 : fetch_word Ubsan.M.loaded_segments (0x283c0 : word) = Some W_283c0.
Proof. vm_refl. Qed.
Lemma D_283c0 : decode_any W_283c0 = Some (Op ALU_AND 23 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_283c4 : bv 32 := 0x5cd0006f.
Lemma F_283c4 : fetch_word Ubsan.M.loaded_segments (0x283c4 : word) = Some W_283c4.
Proof. vm_refl. Qed.
Lemma D_283c4 : decode_any W_283c4 = Some (Jal 0 3532, 4%Z).
Proof. vm_refl. Qed.

Definition W_283c8 : bv 32 := 0x01f47613.
Lemma F_283c8 : fetch_word Ubsan.M.loaded_segments (0x283c8 : word) = Some W_283c8.
Proof. vm_refl. Qed.
Lemma D_283c8 : decode_any W_283c8 = Some (OpImm ALU_AND 12 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_283cc : bv 32 := 0x1e060263.
Lemma F_283cc : fetch_word Ubsan.M.loaded_segments (0x283cc : word) = Some W_283cc.
Proof. vm_refl. Qed.
Lemma D_283cc : decode_any W_283cc = Some (Branch BC_EQ 12 0 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_283d0 : bv 32 := 0x00261693.
Lemma F_283d0 : fetch_word Ubsan.M.loaded_segments (0x283d0 : word) = Some W_283d0.
Proof. vm_refl. Qed.
Lemma D_283d0 : decode_any W_283d0 = Some (ShiftImm ALU_SLL 13 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_283d4 : bv 32 := 0xfffea797.
Lemma F_283d4 : fetch_word Ubsan.M.loaded_segments (0x283d4 : word) = Some W_283d4.
Proof. vm_refl. Qed.
Lemma D_283d4 : decode_any W_283d4 = Some (Auipc 15 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_283d8 : bv 32 := 0x59c78793.
Lemma F_283d8 : fetch_word Ubsan.M.loaded_segments (0x283d8 : word) = Some W_283d8.
Proof. vm_refl. Qed.
Lemma D_283d8 : decode_any W_283d8 = Some (OpImm ALU_ADD 15 15 1436, 4%Z).
Proof. vm_refl. Qed.

Definition W_283dc : bv 32 := 0xfff7c813.
Lemma F_283dc : fetch_word Ubsan.M.loaded_segments (0x283dc : word) = Some W_283dc.
Proof. vm_refl. Qed.
Lemma D_283dc : decode_any W_283dc = Some (OpImm ALU_XOR 16 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_283e0 : bv 32 := 0x00d87463.
Lemma F_283e0 : fetch_word Ubsan.M.loaded_segments (0x283e0 : word) = Some W_283e0.
Proof. vm_refl. Qed.
Lemma D_283e0 : decode_any W_283e0 = Some (Branch BC_GEU 16 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_283e4 : bv 32 := 0x3c40206f.
Lemma F_283e4 : fetch_word Ubsan.M.loaded_segments (0x283e4 : word) = Some W_283e4.
Proof. vm_refl. Qed.
Lemma D_283e4 : decode_any W_283e4 = Some (Jal 0 9156, 4%Z).
Proof. vm_refl. Qed.

Definition W_283e8 : bv 32 := 0x00d786b3.
Lemma F_283e8 : fetch_word Ubsan.M.loaded_segments (0x283e8 : word) = Some W_283e8.
Proof. vm_refl. Qed.
Lemma D_283e8 : decode_any W_283e8 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_283ec : bv 32 := 0x0006ae03.
Lemma F_283ec : fetch_word Ubsan.M.loaded_segments (0x283ec : word) = Some W_283ec.
Proof. vm_refl. Qed.
Lemma D_283ec : decode_any W_283ec = Some (Load SZ4 true 28 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_283f0 : bv 32 := 0x1c00006f.
Lemma F_283f0 : fetch_word Ubsan.M.loaded_segments (0x283f0 : word) = Some W_283f0.
Proof. vm_refl. Qed.
Lemma D_283f0 : decode_any W_283f0 = Some (Jal 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_283f4 : bv 32 := 0x00163793.
Lemma F_283f4 : fetch_word Ubsan.M.loaded_segments (0x283f4 : word) = Some W_283f4.
Proof. vm_refl. Qed.
Lemma D_283f4 : decode_any W_283f4 = Some (OpImm ALU_SLTU 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_283f8 : bv 32 := 0x0010b813.
Lemma F_283f8 : fetch_word Ubsan.M.loaded_segments (0x283f8 : word) = Some W_283f8.
Proof. vm_refl. Qed.
Lemma D_283f8 : decode_any W_283f8 = Some (OpImm ALU_SLTU 16 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_283fc : bv 32 := 0x02000a13.
Lemma F_283fc : fetch_word Ubsan.M.loaded_segments (0x283fc : word) = Some W_283fc.
Proof. vm_refl. Qed.
Lemma D_283fc : decode_any W_283fc = Some (OpImm ALU_ADD 20 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28400 : bv 32 := 0x40ca08b3.
Lemma F_28400 : fetch_word Ubsan.M.loaded_segments (0x28400 : word) = Some W_28400.
Proof. vm_refl. Qed.
Lemma D_28400 : decode_any W_28400 = Some (Op ALU_SUB 17 20 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28404 : bv 32 := 0x401a0ab3.
Lemma F_28404 : fetch_word Ubsan.M.loaded_segments (0x28404 : word) = Some W_28404.
Proof. vm_refl. Qed.
Lemma D_28404 : decode_any W_28404 = Some (Op ALU_SUB 21 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28408 : bv 32 := 0xfff80813.
Lemma F_28408 : fetch_word Ubsan.M.loaded_segments (0x28408 : word) = Some W_28408.
Proof. vm_refl. Qed.
Lemma D_28408 : decode_any W_28408 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_2840c : bv 32 := 0xfff78793.
Lemma F_2840c : fetch_word Ubsan.M.loaded_segments (0x2840c : word) = Some W_2840c.
Proof. vm_refl. Qed.
Lemma D_2840c : decode_any W_2840c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28410 : bv 32 := 0x01587bb3.
Lemma F_28410 : fetch_word Ubsan.M.loaded_segments (0x28410 : word) = Some W_28410.
Proof. vm_refl. Qed.
Lemma D_28410 : decode_any W_28410 = Some (Op ALU_AND 23 16 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_28414 : bv 32 := 0x0117f7b3.
Lemma F_28414 : fetch_word Ubsan.M.loaded_segments (0x28414 : word) = Some W_28414.
Proof. vm_refl. Qed.
Lemma D_28414 : decode_any W_28414 = Some (Op ALU_AND 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28418 : bv 32 := 0x0177b833.
Lemma F_28418 : fetch_word Ubsan.M.loaded_segments (0x28418 : word) = Some W_28418.
Proof. vm_refl. Qed.
Lemma D_28418 : decode_any W_28418 = Some (Op ALU_SLTU 16 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_2841c : bv 32 := 0x00184813.
Lemma F_2841c : fetch_word Ubsan.M.loaded_segments (0x2841c : word) = Some W_2841c.
Proof. vm_refl. Qed.
Lemma D_2841c : decode_any W_2841c = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28420 : bv 32 := 0x40fb8eb3.
Lemma F_28420 : fetch_word Ubsan.M.loaded_segments (0x28420 : word) = Some W_28420.
Proof. vm_refl. Qed.
Lemma D_28420 : decode_any W_28420 = Some (Op ALU_SUB 29 23 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28424 : bv 32 := 0x00581813.
Lemma F_28424 : fetch_word Ubsan.M.loaded_segments (0x28424 : word) = Some W_28424.
Proof. vm_refl. Qed.
Lemma D_28424 : decode_any W_28424 = Some (ShiftImm ALU_SLL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28428 : bv 32 := 0x010e8eb3.
Lemma F_28428 : fetch_word Ubsan.M.loaded_segments (0x28428 : word) = Some W_28428.
Proof. vm_refl. Qed.
Lemma D_28428 : decode_any W_28428 = Some (Op ALU_ADD 29 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2842c : bv 32 := 0x01da7463.
Lemma F_2842c : fetch_word Ubsan.M.loaded_segments (0x2842c : word) = Some W_2842c.
Proof. vm_refl. Qed.
Lemma D_2842c : decode_any W_2842c = Some (Branch BC_GEU 20 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28430 : bv 32 := 0x3780206f.
Lemma F_28430 : fetch_word Ubsan.M.loaded_segments (0x28430 : word) = Some W_28430.
Proof. vm_refl. Qed.
Lemma D_28430 : decode_any W_28430 = Some (Jal 0 9080, 4%Z).
Proof. vm_refl. Qed.

Definition W_28434 : bv 32 := 0x000e8f1b.
Lemma F_28434 : fetch_word Ubsan.M.loaded_segments (0x28434 : word) = Some W_28434.
Proof. vm_refl. Qed.
Lemma D_28434 : decode_any W_28434 = Some (OpImm32 30 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28438 : bv 32 := 0xfffea797.
Lemma F_28438 : fetch_word Ubsan.M.loaded_segments (0x28438 : word) = Some W_28438.
Proof. vm_refl. Qed.
Lemma D_28438 : decode_any W_28438 = Some (Auipc 15 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_2843c : bv 32 := 0x002f1313.
Lemma F_2843c : fetch_word Ubsan.M.loaded_segments (0x2843c : word) = Some W_2843c.
Proof. vm_refl. Qed.
Lemma D_2843c : decode_any W_2843c = Some (ShiftImm ALU_SLL 6 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28440 : bv 32 := 0x4b478813.
Lemma F_28440 : fetch_word Ubsan.M.loaded_segments (0x28440 : word) = Some W_28440.
Proof. vm_refl. Qed.
Lemma D_28440 : decode_any W_28440 = Some (OpImm ALU_ADD 16 15 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_28444 : bv 32 := 0xfff84793.
Lemma F_28444 : fetch_word Ubsan.M.loaded_segments (0x28444 : word) = Some W_28444.
Proof. vm_refl. Qed.
Lemma D_28444 : decode_any W_28444 = Some (OpImm ALU_XOR 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28448 : bv 32 := 0x0067f463.
Lemma F_28448 : fetch_word Ubsan.M.loaded_segments (0x28448 : word) = Some W_28448.
Proof. vm_refl. Qed.
Lemma D_28448 : decode_any W_28448 = Some (Branch BC_GEU 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2844c : bv 32 := 0x35c0206f.
Lemma F_2844c : fetch_word Ubsan.M.loaded_segments (0x2844c : word) = Some W_2844c.
Proof. vm_refl. Qed.
Lemma D_2844c : decode_any W_2844c = Some (Jal 0 9052, 4%Z).
Proof. vm_refl. Qed.

Definition W_28450 : bv 32 := 0x00680333.
Lemma F_28450 : fetch_word Ubsan.M.loaded_segments (0x28450 : word) = Some W_28450.
Proof. vm_refl. Qed.
Lemma D_28450 : decode_any W_28450 = Some (Op ALU_ADD 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28454 : bv 32 := 0x00032f83.
Lemma F_28454 : fetch_word Ubsan.M.loaded_segments (0x28454 : word) = Some W_28454.
Proof. vm_refl. Qed.
Lemma D_28454 : decode_any W_28454 = Some (Load SZ4 true 31 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28458 : bv 32 := 0x52008463.
Lemma F_28458 : fetch_word Ubsan.M.loaded_segments (0x28458 : word) = Some W_28458.
Proof. vm_refl. Qed.
Lemma D_28458 : decode_any W_28458 = Some (Branch BC_EQ 1 0 1320, 4%Z).
Proof. vm_refl. Qed.

Definition W_2845c : bv 32 := 0x002a9e13.
Lemma F_2845c : fetch_word Ubsan.M.loaded_segments (0x2845c : word) = Some W_2845c.
Proof. vm_refl. Qed.
Lemma D_2845c : decode_any W_2845c = Some (ShiftImm ALU_SLL 28 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28460 : bv 32 := 0x01c7f463.
Lemma F_28460 : fetch_word Ubsan.M.loaded_segments (0x28460 : word) = Some W_28460.
Proof. vm_refl. Qed.
Lemma D_28460 : decode_any W_28460 = Some (Branch BC_GEU 15 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28464 : bv 32 := 0x3440206f.
Lemma F_28464 : fetch_word Ubsan.M.loaded_segments (0x28464 : word) = Some W_28464.
Proof. vm_refl. Qed.
Lemma D_28464 : decode_any W_28464 = Some (Jal 0 9028, 4%Z).
Proof. vm_refl. Qed.

Definition W_28468 : bv 32 := 0x02770b33.
Lemma F_28468 : fetch_word Ubsan.M.loaded_segments (0x28468 : word) = Some W_28468.
Proof. vm_refl. Qed.
Lemma D_28468 : decode_any W_28468 = Some (Mul M_MUL 22 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_2846c : bv 32 := 0x027707bb.
Lemma F_2846c : fetch_word Ubsan.M.loaded_segments (0x2846c : word) = Some W_2846c.
Proof. vm_refl. Qed.
Lemma D_2846c : decode_any W_2846c = Some (Mul32 M_MUL 15 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28470 : bv 32 := 0x01678463.
Lemma F_28470 : fetch_word Ubsan.M.loaded_segments (0x28470 : word) = Some W_28470.
Proof. vm_refl. Qed.
Lemma D_28470 : decode_any W_28470 = Some (Branch BC_EQ 15 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28474 : bv 32 := 0x3340206f.
Lemma F_28474 : fetch_word Ubsan.M.loaded_segments (0x28474 : word) = Some W_28474.
Proof. vm_refl. Qed.
Lemma D_28474 : decode_any W_28474 = Some (Jal 0 9012, 4%Z).
Proof. vm_refl. Qed.

Definition W_28478 : bv 32 := 0x000b0b1b.
Lemma F_28478 : fetch_word Ubsan.M.loaded_segments (0x28478 : word) = Some W_28478.
Proof. vm_refl. Qed.
Lemma D_28478 : decode_any W_28478 = Some (OpImm32 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2847c : bv 32 := 0x002b1793.
Lemma F_2847c : fetch_word Ubsan.M.loaded_segments (0x2847c : word) = Some W_2847c.
Proof. vm_refl. Qed.
Lemma D_2847c : decode_any W_2847c = Some (ShiftImm ALU_SLL 15 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28480 : bv 32 := 0x00a787b3.
Lemma F_28480 : fetch_word Ubsan.M.loaded_segments (0x28480 : word) = Some W_28480.
Proof. vm_refl. Qed.
Lemma D_28480 : decode_any W_28480 = Some (Op ALU_ADD 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28484 : bv 32 := 0x00a03333.
Lemma F_28484 : fetch_word Ubsan.M.loaded_segments (0x28484 : word) = Some W_28484.
Proof. vm_refl. Qed.
Lemma D_28484 : decode_any W_28484 = Some (Op ALU_SLTU 6 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28488 : bv 32 := 0x0017bd13.
Lemma F_28488 : fetch_word Ubsan.M.loaded_segments (0x28488 : word) = Some W_28488.
Proof. vm_refl. Qed.
Lemma D_28488 : decode_any W_28488 = Some (OpImm ALU_SLTU 26 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2848c : bv 32 := 0x01a31463.
Lemma F_2848c : fetch_word Ubsan.M.loaded_segments (0x2848c : word) = Some W_2848c.
Proof. vm_refl. Qed.
Lemma D_2848c : decode_any W_2848c = Some (Branch BC_NE 6 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28490 : bv 32 := 0x3180206f.
Lemma F_28490 : fetch_word Ubsan.M.loaded_segments (0x28490 : word) = Some W_28490.
Proof. vm_refl. Qed.
Lemma D_28490 : decode_any W_28490 = Some (Jal 0 8984, 4%Z).
Proof. vm_refl. Qed.

Definition W_28494 : bv 32 := 0x00a7bd33.
Lemma F_28494 : fetch_word Ubsan.M.loaded_segments (0x28494 : word) = Some W_28494.
Proof. vm_refl. Qed.
Lemma D_28494 : decode_any W_28494 = Some (Op ALU_SLTU 26 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28498 : bv 32 := 0x000b2b13.
Lemma F_28498 : fetch_word Ubsan.M.loaded_segments (0x28498 : word) = Some W_28498.
Proof. vm_refl. Qed.
Lemma D_28498 : decode_any W_28498 = Some (OpImm ALU_SLT 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2849c : bv 32 := 0x016d4b33.
Lemma F_2849c : fetch_word Ubsan.M.loaded_segments (0x2849c : word) = Some W_2849c.
Proof. vm_refl. Qed.
Lemma D_2849c : decode_any W_2849c = Some (Op ALU_XOR 22 26 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_284a0 : bv 32 := 0x001b4b13.
Lemma F_284a0 : fetch_word Ubsan.M.loaded_segments (0x284a0 : word) = Some W_284a0.
Proof. vm_refl. Qed.
Lemma D_284a0 : decode_any W_284a0 = Some (OpImm ALU_XOR 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_284a4 : bv 32 := 0x000b1463.
Lemma F_284a4 : fetch_word Ubsan.M.loaded_segments (0x284a4 : word) = Some W_284a4.
Proof. vm_refl. Qed.
Lemma D_284a4 : decode_any W_284a4 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_284a8 : bv 32 := 0x3000206f.
Lemma F_284a8 : fetch_word Ubsan.M.loaded_segments (0x284a8 : word) = Some W_284a8.
Proof. vm_refl. Qed.
Lemma D_284a8 : decode_any W_284a8 = Some (Jal 0 8960, 4%Z).
Proof. vm_refl. Qed.

Definition W_284ac : bv 32 := 0x405cdb1b.
Lemma F_284ac : fetch_word Ubsan.M.loaded_segments (0x284ac : word) = Some W_284ac.
Proof. vm_refl. Qed.
Lemma D_284ac : decode_any W_284ac = Some (ShiftImm32 ALU_SRA 22 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_284b0 : bv 32 := 0x002b1c93.
Lemma F_284b0 : fetch_word Ubsan.M.loaded_segments (0x284b0 : word) = Some W_284b0.
Proof. vm_refl. Qed.
Lemma D_284b0 : decode_any W_284b0 = Some (ShiftImm ALU_SLL 25 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_284b4 : bv 32 := 0x01978cb3.
Lemma F_284b4 : fetch_word Ubsan.M.loaded_segments (0x284b4 : word) = Some W_284b4.
Proof. vm_refl. Qed.
Lemma D_284b4 : decode_any W_284b4 = Some (Op ALU_ADD 25 15 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_284b8 : bv 32 := 0x001cbd13.
Lemma F_284b8 : fetch_word Ubsan.M.loaded_segments (0x284b8 : word) = Some W_284b8.
Proof. vm_refl. Qed.
Lemma D_284b8 : decode_any W_284b8 = Some (OpImm ALU_SLTU 26 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_284bc : bv 32 := 0x01a31463.
Lemma F_284bc : fetch_word Ubsan.M.loaded_segments (0x284bc : word) = Some W_284bc.
Proof. vm_refl. Qed.
Lemma D_284bc : decode_any W_284bc = Some (Branch BC_NE 6 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_284c0 : bv 32 := 0x2e80206f.
Lemma F_284c0 : fetch_word Ubsan.M.loaded_segments (0x284c0 : word) = Some W_284c0.
Proof. vm_refl. Qed.
Lemma D_284c0 : decode_any W_284c0 = Some (Jal 0 8936, 4%Z).
Proof. vm_refl. Qed.

Definition W_284c4 : bv 32 := 0x00fcb7b3.
Lemma F_284c4 : fetch_word Ubsan.M.loaded_segments (0x284c4 : word) = Some W_284c4.
Proof. vm_refl. Qed.
Lemma D_284c4 : decode_any W_284c4 = Some (Op ALU_SLTU 15 25 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_284c8 : bv 32 := 0x000b2313.
Lemma F_284c8 : fetch_word Ubsan.M.loaded_segments (0x284c8 : word) = Some W_284c8.
Proof. vm_refl. Qed.
Lemma D_284c8 : decode_any W_284c8 = Some (OpImm ALU_SLT 6 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_284cc : bv 32 := 0x0067c7b3.
Lemma F_284cc : fetch_word Ubsan.M.loaded_segments (0x284cc : word) = Some W_284cc.
Proof. vm_refl. Qed.
Lemma D_284cc : decode_any W_284cc = Some (Op ALU_XOR 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_284d0 : bv 32 := 0x0017c793.
Lemma F_284d0 : fetch_word Ubsan.M.loaded_segments (0x284d0 : word) = Some W_284d0.
Proof. vm_refl. Qed.
Lemma D_284d0 : decode_any W_284d0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_284d4 : bv 32 := 0x00079463.
Lemma F_284d4 : fetch_word Ubsan.M.loaded_segments (0x284d4 : word) = Some W_284d4.
Proof. vm_refl. Qed.
Lemma D_284d4 : decode_any W_284d4 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_284d8 : bv 32 := 0x2d00206f.
Lemma F_284d8 : fetch_word Ubsan.M.loaded_segments (0x284d8 : word) = Some W_284d8.
Proof. vm_refl. Qed.
Lemma D_284d8 : decode_any W_284d8 = Some (Jal 0 8912, 4%Z).
Proof. vm_refl. Qed.

Definition W_284dc : bv 32 := 0x05813303.
Lemma F_284dc : fetch_word Ubsan.M.loaded_segments (0x284dc : word) = Some W_284dc.
Proof. vm_refl. Qed.
Lemma D_284dc : decode_any W_284dc = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_284e0 : bv 32 := 0x025307b3.
Lemma F_284e0 : fetch_word Ubsan.M.loaded_segments (0x284e0 : word) = Some W_284e0.
Proof. vm_refl. Qed.
Lemma D_284e0 : decode_any W_284e0 = Some (Mul M_MUL 15 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_284e4 : bv 32 := 0x0253033b.
Lemma F_284e4 : fetch_word Ubsan.M.loaded_segments (0x284e4 : word) = Some W_284e4.
Proof. vm_refl. Qed.
Lemma D_284e4 : decode_any W_284e4 = Some (Mul32 M_MUL 6 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_284e8 : bv 32 := 0x00f30463.
Lemma F_284e8 : fetch_word Ubsan.M.loaded_segments (0x284e8 : word) = Some W_284e8.
Proof. vm_refl. Qed.
Lemma D_284e8 : decode_any W_284e8 = Some (Branch BC_EQ 6 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_284ec : bv 32 := 0x2bc0206f.
Lemma F_284ec : fetch_word Ubsan.M.loaded_segments (0x284ec : word) = Some W_284ec.
Proof. vm_refl. Qed.
Lemma D_284ec : decode_any W_284ec = Some (Jal 0 8892, 4%Z).
Proof. vm_refl. Qed.

Definition W_284f0 : bv 32 := 0x0007879b.
Lemma F_284f0 : fetch_word Ubsan.M.loaded_segments (0x284f0 : word) = Some W_284f0.
Proof. vm_refl. Qed.
Lemma D_284f0 : decode_any W_284f0 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_284f4 : bv 32 := 0x00279b13.
Lemma F_284f4 : fetch_word Ubsan.M.loaded_segments (0x284f4 : word) = Some W_284f4.
Proof. vm_refl. Qed.
Lemma D_284f4 : decode_any W_284f4 = Some (ShiftImm ALU_SLL 22 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_284f8 : bv 32 := 0x013b0b33.
Lemma F_284f8 : fetch_word Ubsan.M.loaded_segments (0x284f8 : word) = Some W_284f8.
Proof. vm_refl. Qed.
Lemma D_284f8 : decode_any W_284f8 = Some (Op ALU_ADD 22 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_284fc : bv 32 := 0x01303333.
Lemma F_284fc : fetch_word Ubsan.M.loaded_segments (0x284fc : word) = Some W_284fc.
Proof. vm_refl. Qed.
Lemma D_284fc : decode_any W_284fc = Some (Op ALU_SLTU 6 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28500 : bv 32 := 0x001b3d13.
Lemma F_28500 : fetch_word Ubsan.M.loaded_segments (0x28500 : word) = Some W_28500.
Proof. vm_refl. Qed.
Lemma D_28500 : decode_any W_28500 = Some (OpImm ALU_SLTU 26 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28504 : bv 32 := 0x01a31463.
Lemma F_28504 : fetch_word Ubsan.M.loaded_segments (0x28504 : word) = Some W_28504.
Proof. vm_refl. Qed.
Lemma D_28504 : decode_any W_28504 = Some (Branch BC_NE 6 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28508 : bv 32 := 0x2a00206f.
Lemma F_28508 : fetch_word Ubsan.M.loaded_segments (0x28508 : word) = Some W_28508.
Proof. vm_refl. Qed.
Lemma D_28508 : decode_any W_28508 = Some (Jal 0 8864, 4%Z).
Proof. vm_refl. Qed.

Definition W_2850c : bv 32 := 0x013b3d33.
Lemma F_2850c : fetch_word Ubsan.M.loaded_segments (0x2850c : word) = Some W_2850c.
Proof. vm_refl. Qed.
Lemma D_2850c : decode_any W_2850c = Some (Op ALU_SLTU 26 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28510 : bv 32 := 0x0007a793.
Lemma F_28510 : fetch_word Ubsan.M.loaded_segments (0x28510 : word) = Some W_28510.
Proof. vm_refl. Qed.
Lemma D_28510 : decode_any W_28510 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28514 : bv 32 := 0x00fd47b3.
Lemma F_28514 : fetch_word Ubsan.M.loaded_segments (0x28514 : word) = Some W_28514.
Proof. vm_refl. Qed.
Lemma D_28514 : decode_any W_28514 = Some (Op ALU_XOR 15 26 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28518 : bv 32 := 0x0017c793.
Lemma F_28518 : fetch_word Ubsan.M.loaded_segments (0x28518 : word) = Some W_28518.
Proof. vm_refl. Qed.
Lemma D_28518 : decode_any W_28518 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2851c : bv 32 := 0x00079463.
Lemma F_2851c : fetch_word Ubsan.M.loaded_segments (0x2851c : word) = Some W_2851c.
Proof. vm_refl. Qed.
Lemma D_2851c : decode_any W_2851c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28520 : bv 32 := 0x2880206f.
Lemma F_28520 : fetch_word Ubsan.M.loaded_segments (0x28520 : word) = Some W_28520.
Proof. vm_refl. Qed.
Lemma D_28520 : decode_any W_28520 = Some (Jal 0 8840, 4%Z).
Proof. vm_refl. Qed.

Definition W_28524 : bv 32 := 0x005dd79b.
Lemma F_28524 : fetch_word Ubsan.M.loaded_segments (0x28524 : word) = Some W_28524.
Proof. vm_refl. Qed.
Lemma D_28524 : decode_any W_28524 = Some (ShiftImm32 ALU_SRL 15 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28528 : bv 32 := 0x00279793.
Lemma F_28528 : fetch_word Ubsan.M.loaded_segments (0x28528 : word) = Some W_28528.
Proof. vm_refl. Qed.
Lemma D_28528 : decode_any W_28528 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_2852c : bv 32 := 0x00fb07b3.
Lemma F_2852c : fetch_word Ubsan.M.loaded_segments (0x2852c : word) = Some W_2852c.
Proof. vm_refl. Qed.
Lemma D_2852c : decode_any W_2852c = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28530 : bv 32 := 0x0167f463.
Lemma F_28530 : fetch_word Ubsan.M.loaded_segments (0x28530 : word) = Some W_28530.
Proof. vm_refl. Qed.
Lemma D_28530 : decode_any W_28530 = Some (Branch BC_GEU 15 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28534 : bv 32 := 0x2740206f.
Lemma F_28534 : fetch_word Ubsan.M.loaded_segments (0x28534 : word) = Some W_28534.
Proof. vm_refl. Qed.
Lemma D_28534 : decode_any W_28534 = Some (Jal 0 8820, 4%Z).
Proof. vm_refl. Qed.

Definition W_28538 : bv 32 := 0x0017bb13.
Lemma F_28538 : fetch_word Ubsan.M.loaded_segments (0x28538 : word) = Some W_28538.
Proof. vm_refl. Qed.
Lemma D_28538 : decode_any W_28538 = Some (OpImm ALU_SLTU 22 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2853c : bv 32 := 0x01634333.
Lemma F_2853c : fetch_word Ubsan.M.loaded_segments (0x2853c : word) = Some W_2853c.
Proof. vm_refl. Qed.
Lemma D_2853c : decode_any W_2853c = Some (Op ALU_XOR 6 6 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_28540 : bv 32 := 0x00031463.
Lemma F_28540 : fetch_word Ubsan.M.loaded_segments (0x28540 : word) = Some W_28540.
Proof. vm_refl. Qed.
Lemma D_28540 : decode_any W_28540 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28544 : bv 32 := 0x2640206f.
Lemma F_28544 : fetch_word Ubsan.M.loaded_segments (0x28544 : word) = Some W_28544.
Proof. vm_refl. Qed.
Lemma D_28544 : decode_any W_28544 = Some (Jal 0 8804, 4%Z).
Proof. vm_refl. Qed.

Definition W_28548 : bv 32 := 0x01c80833.
Lemma F_28548 : fetch_word Ubsan.M.loaded_segments (0x28548 : word) = Some W_28548.
Proof. vm_refl. Qed.
Lemma D_28548 : decode_any W_28548 = Some (Op ALU_ADD 16 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_2854c : bv 32 := 0x00082d83.
Lemma F_2854c : fetch_word Ubsan.M.loaded_segments (0x2854c : word) = Some W_2854c.
Proof. vm_refl. Qed.
Lemma D_2854c : decode_any W_2854c = Some (Load SZ4 true 27 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28550 : bv 32 := 0x00c0b633.
Lemma F_28550 : fetch_word Ubsan.M.loaded_segments (0x28550 : word) = Some W_28550.
Proof. vm_refl. Qed.
Lemma D_28550 : decode_any W_28550 = Some (Op ALU_SLTU 12 1 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28554 : bv 32 := 0x00c13823.
Lemma F_28554 : fetch_word Ubsan.M.loaded_segments (0x28554 : word) = Some W_28554.
Proof. vm_refl. Qed.
Lemma D_28554 : decode_any W_28554 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28558 : bv 32 := 0x0098b633.
Lemma F_28558 : fetch_word Ubsan.M.loaded_segments (0x28558 : word) = Some W_28558.
Proof. vm_refl. Qed.
Lemma D_28558 : decode_any W_28558 = Some (Op ALU_SLTU 12 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_2855c : bv 32 := 0x00164d13.
Lemma F_2855c : fetch_word Ubsan.M.loaded_segments (0x2855c : word) = Some W_2855c.
Proof. vm_refl. Qed.
Lemma D_2855c : decode_any W_2855c = Some (OpImm ALU_XOR 26 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28560 : bv 32 := 0x4354f863.
Lemma F_28560 : fetch_word Ubsan.M.loaded_segments (0x28560 : word) = Some W_28560.
Proof. vm_refl. Qed.
Lemma D_28560 : decode_any W_28560 = Some (Branch BC_GEU 9 21 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_28564 : bv 32 := 0x4154063b.
Lemma F_28564 : fetch_word Ubsan.M.loaded_segments (0x28564 : word) = Some W_28564.
Proof. vm_refl. Qed.
Lemma D_28564 : decode_any W_28564 = Some (Op32 ALU_SUB 12 8 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_28568 : bv 32 := 0x0206061b.
Lemma F_28568 : fetch_word Ubsan.M.loaded_segments (0x28568 : word) = Some W_28568.
Proof. vm_refl. Qed.
Lemma D_28568 : decode_any W_28568 = Some (OpImm32 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_2856c : bv 32 := 0x02000813.
Lemma F_2856c : fetch_word Ubsan.M.loaded_segments (0x2856c : word) = Some W_2856c.
Proof. vm_refl. Qed.
Lemma D_2856c : decode_any W_2856c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28570 : bv 32 := 0x00c87463.
Lemma F_28570 : fetch_word Ubsan.M.loaded_segments (0x28570 : word) = Some W_28570.
Proof. vm_refl. Qed.
Lemma D_28570 : decode_any W_28570 = Some (Branch BC_GEU 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28574 : bv 32 := 0x2340206f.
Lemma F_28574 : fetch_word Ubsan.M.loaded_segments (0x28574 : word) = Some W_28574.
Proof. vm_refl. Qed.
Lemma D_28574 : decode_any W_28574 = Some (Jal 0 8756, 4%Z).
Proof. vm_refl. Qed.

Definition W_28578 : bv 32 := 0x00261613.
Lemma F_28578 : fetch_word Ubsan.M.loaded_segments (0x28578 : word) = Some W_28578.
Proof. vm_refl. Qed.
Lemma D_28578 : decode_any W_28578 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_2857c : bv 32 := 0xfffea817.
Lemma F_2857c : fetch_word Ubsan.M.loaded_segments (0x2857c : word) = Some W_2857c.
Proof. vm_refl. Qed.
Lemma D_2857c : decode_any W_2857c = Some (Auipc 16 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_28580 : bv 32 := 0x3f480813.
Lemma F_28580 : fetch_word Ubsan.M.loaded_segments (0x28580 : word) = Some W_28580.
Proof. vm_refl. Qed.
Lemma D_28580 : decode_any W_28580 = Some (OpImm ALU_ADD 16 16 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_28584 : bv 32 := 0xfff84893.
Lemma F_28584 : fetch_word Ubsan.M.loaded_segments (0x28584 : word) = Some W_28584.
Proof. vm_refl. Qed.
Lemma D_28584 : decode_any W_28584 = Some (OpImm ALU_XOR 17 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28588 : bv 32 := 0x00c8f463.
Lemma F_28588 : fetch_word Ubsan.M.loaded_segments (0x28588 : word) = Some W_28588.
Proof. vm_refl. Qed.
Lemma D_28588 : decode_any W_28588 = Some (Branch BC_GEU 17 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2858c : bv 32 := 0x21c0206f.
Lemma F_2858c : fetch_word Ubsan.M.loaded_segments (0x2858c : word) = Some W_2858c.
Proof. vm_refl. Qed.
Lemma D_2858c : decode_any W_2858c = Some (Jal 0 8732, 4%Z).
Proof. vm_refl. Qed.

Definition W_28590 : bv 32 := 0x06013823.
Lemma F_28590 : fetch_word Ubsan.M.loaded_segments (0x28590 : word) = Some W_28590.
Proof. vm_refl. Qed.
Lemma D_28590 : decode_any W_28590 = Some (Store SZ8 2 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_28594 : bv 32 := 0x00000913.
Lemma F_28594 : fetch_word Ubsan.M.loaded_segments (0x28594 : word) = Some W_28594.
Proof. vm_refl. Qed.
Lemma D_28594 : decode_any W_28594 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28598 : bv 32 := 0x00000313.
Lemma F_28598 : fetch_word Ubsan.M.loaded_segments (0x28598 : word) = Some W_28598.
Proof. vm_refl. Qed.
Lemma D_28598 : decode_any W_28598 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2859c : bv 32 := 0x00c80633.
Lemma F_2859c : fetch_word Ubsan.M.loaded_segments (0x2859c : word) = Some W_2859c.
Proof. vm_refl. Qed.
Lemma D_2859c : decode_any W_2859c = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_285a0 : bv 32 := 0x00062603.
Lemma F_285a0 : fetch_word Ubsan.M.loaded_segments (0x285a0 : word) = Some W_285a0.
Proof. vm_refl. Qed.
Lemma D_285a0 : decode_any W_285a0 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285a4 : bv 32 := 0x00100813.
Lemma F_285a4 : fetch_word Ubsan.M.loaded_segments (0x285a4 : word) = Some W_285a4.
Proof. vm_refl. Qed.
Lemma D_285a4 : decode_any W_285a4 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_285a8 : bv 32 := 0x01b67db3.
Lemma F_285a8 : fetch_word Ubsan.M.loaded_segments (0x285a8 : word) = Some W_285a8.
Proof. vm_refl. Qed.
Lemma D_285a8 : decode_any W_285a8 = Some (Op ALU_AND 27 12 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_285ac : bv 32 := 0x5500006f.
Lemma F_285ac : fetch_word Ubsan.M.loaded_segments (0x285ac : word) = Some W_285ac.
Proof. vm_refl. Qed.
Lemma D_285ac : decode_any W_285ac = Some (Jal 0 1360, 4%Z).
Proof. vm_refl. Qed.

Definition W_285b0 : bv 32 := 0x025307b3.
Lemma F_285b0 : fetch_word Ubsan.M.loaded_segments (0x285b0 : word) = Some W_285b0.
Proof. vm_refl. Qed.
Lemma D_285b0 : decode_any W_285b0 = Some (Mul M_MUL 15 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_285b4 : bv 32 := 0x025306bb.
Lemma F_285b4 : fetch_word Ubsan.M.loaded_segments (0x285b4 : word) = Some W_285b4.
Proof. vm_refl. Qed.
Lemma D_285b4 : decode_any W_285b4 = Some (Mul32 M_MUL 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_285b8 : bv 32 := 0x00f68463.
Lemma F_285b8 : fetch_word Ubsan.M.loaded_segments (0x285b8 : word) = Some W_285b8.
Proof. vm_refl. Qed.
Lemma D_285b8 : decode_any W_285b8 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285bc : bv 32 := 0x1ec0206f.
Lemma F_285bc : fetch_word Ubsan.M.loaded_segments (0x285bc : word) = Some W_285bc.
Proof. vm_refl. Qed.
Lemma D_285bc : decode_any W_285bc = Some (Jal 0 8684, 4%Z).
Proof. vm_refl. Qed.

Definition W_285c0 : bv 32 := 0x0007879b.
Lemma F_285c0 : fetch_word Ubsan.M.loaded_segments (0x285c0 : word) = Some W_285c0.
Proof. vm_refl. Qed.
Lemma D_285c0 : decode_any W_285c0 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285c4 : bv 32 := 0x00279413.
Lemma F_285c4 : fetch_word Ubsan.M.loaded_segments (0x285c4 : word) = Some W_285c4.
Proof. vm_refl. Qed.
Lemma D_285c4 : decode_any W_285c4 = Some (ShiftImm ALU_SLL 8 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_285c8 : bv 32 := 0x013406b3.
Lemma F_285c8 : fetch_word Ubsan.M.loaded_segments (0x285c8 : word) = Some W_285c8.
Proof. vm_refl. Qed.
Lemma D_285c8 : decode_any W_285c8 = Some (Op ALU_ADD 13 8 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_285cc : bv 32 := 0x01303833.
Lemma F_285cc : fetch_word Ubsan.M.loaded_segments (0x285cc : word) = Some W_285cc.
Proof. vm_refl. Qed.
Lemma D_285cc : decode_any W_285cc = Some (Op ALU_SLTU 16 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_285d0 : bv 32 := 0x0016b893.
Lemma F_285d0 : fetch_word Ubsan.M.loaded_segments (0x285d0 : word) = Some W_285d0.
Proof. vm_refl. Qed.
Lemma D_285d0 : decode_any W_285d0 = Some (OpImm ALU_SLTU 17 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_285d4 : bv 32 := 0x01181463.
Lemma F_285d4 : fetch_word Ubsan.M.loaded_segments (0x285d4 : word) = Some W_285d4.
Proof. vm_refl. Qed.
Lemma D_285d4 : decode_any W_285d4 = Some (Branch BC_NE 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285d8 : bv 32 := 0x1d00206f.
Lemma F_285d8 : fetch_word Ubsan.M.loaded_segments (0x285d8 : word) = Some W_285d8.
Proof. vm_refl. Qed.
Lemma D_285d8 : decode_any W_285d8 = Some (Jal 0 8656, 4%Z).
Proof. vm_refl. Qed.

Definition W_285dc : bv 32 := 0x0136b8b3.
Lemma F_285dc : fetch_word Ubsan.M.loaded_segments (0x285dc : word) = Some W_285dc.
Proof. vm_refl. Qed.
Lemma D_285dc : decode_any W_285dc = Some (Op ALU_SLTU 17 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_285e0 : bv 32 := 0x0007a793.
Lemma F_285e0 : fetch_word Ubsan.M.loaded_segments (0x285e0 : word) = Some W_285e0.
Proof. vm_refl. Qed.
Lemma D_285e0 : decode_any W_285e0 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285e4 : bv 32 := 0x00f8c7b3.
Lemma F_285e4 : fetch_word Ubsan.M.loaded_segments (0x285e4 : word) = Some W_285e4.
Proof. vm_refl. Qed.
Lemma D_285e4 : decode_any W_285e4 = Some (Op ALU_XOR 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_285e8 : bv 32 := 0x0017c793.
Lemma F_285e8 : fetch_word Ubsan.M.loaded_segments (0x285e8 : word) = Some W_285e8.
Proof. vm_refl. Qed.
Lemma D_285e8 : decode_any W_285e8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_285ec : bv 32 := 0x00079463.
Lemma F_285ec : fetch_word Ubsan.M.loaded_segments (0x285ec : word) = Some W_285ec.
Proof. vm_refl. Qed.
Lemma D_285ec : decode_any W_285ec = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285f0 : bv 32 := 0x1b80206f.
Lemma F_285f0 : fetch_word Ubsan.M.loaded_segments (0x285f0 : word) = Some W_285f0.
Proof. vm_refl. Qed.
Lemma D_285f0 : decode_any W_285f0 = Some (Jal 0 8632, 4%Z).
Proof. vm_refl. Qed.

Definition W_285f4 : bv 32 := 0x005dd91b.
Lemma F_285f4 : fetch_word Ubsan.M.loaded_segments (0x285f4 : word) = Some W_285f4.
Proof. vm_refl. Qed.
Lemma D_285f4 : decode_any W_285f4 = Some (ShiftImm32 ALU_SRL 18 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_285f8 : bv 32 := 0x00291913.
Lemma F_285f8 : fetch_word Ubsan.M.loaded_segments (0x285f8 : word) = Some W_285f8.
Proof. vm_refl. Qed.
Lemma D_285f8 : decode_any W_285f8 = Some (ShiftImm ALU_SLL 18 18 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_285fc : bv 32 := 0x012688b3.
Lemma F_285fc : fetch_word Ubsan.M.loaded_segments (0x285fc : word) = Some W_285fc.
Proof. vm_refl. Qed.
Lemma D_285fc : decode_any W_285fc = Some (Op ALU_ADD 17 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_28600 : bv 32 := 0x00d8f463.
Lemma F_28600 : fetch_word Ubsan.M.loaded_segments (0x28600 : word) = Some W_28600.
Proof. vm_refl. Qed.
Lemma D_28600 : decode_any W_28600 = Some (Branch BC_GEU 17 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28604 : bv 32 := 0x1a40206f.
Lemma F_28604 : fetch_word Ubsan.M.loaded_segments (0x28604 : word) = Some W_28604.
Proof. vm_refl. Qed.
Lemma D_28604 : decode_any W_28604 = Some (Jal 0 8612, 4%Z).
Proof. vm_refl. Qed.

Definition W_28608 : bv 32 := 0x0018b693.
Lemma F_28608 : fetch_word Ubsan.M.loaded_segments (0x28608 : word) = Some W_28608.
Proof. vm_refl. Qed.
Lemma D_28608 : decode_any W_28608 = Some (OpImm ALU_SLTU 13 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2860c : bv 32 := 0x00d846b3.
Lemma F_2860c : fetch_word Ubsan.M.loaded_segments (0x2860c : word) = Some W_2860c.
Proof. vm_refl. Qed.
Lemma D_2860c : decode_any W_2860c = Some (Op ALU_XOR 13 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28610 : bv 32 := 0x00069463.
Lemma F_28610 : fetch_word Ubsan.M.loaded_segments (0x28610 : word) = Some W_28610.
Proof. vm_refl. Qed.
Lemma D_28610 : decode_any W_28610 = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28614 : bv 32 := 0x1940206f.
Lemma F_28614 : fetch_word Ubsan.M.loaded_segments (0x28614 : word) = Some W_28614.
Proof. vm_refl. Qed.
Lemma D_28614 : decode_any W_28614 = Some (Jal 0 8596, 4%Z).
Proof. vm_refl. Qed.

Definition W_28618 : bv 32 := 0x027707b3.
Lemma F_28618 : fetch_word Ubsan.M.loaded_segments (0x28618 : word) = Some W_28618.
Proof. vm_refl. Qed.
Lemma D_28618 : decode_any W_28618 = Some (Mul M_MUL 15 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_2861c : bv 32 := 0x027706bb.
Lemma F_2861c : fetch_word Ubsan.M.loaded_segments (0x2861c : word) = Some W_2861c.
Proof. vm_refl. Qed.
Lemma D_2861c : decode_any W_2861c = Some (Mul32 M_MUL 13 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28620 : bv 32 := 0x00f68463.
Lemma F_28620 : fetch_word Ubsan.M.loaded_segments (0x28620 : word) = Some W_28620.
Proof. vm_refl. Qed.
Lemma D_28620 : decode_any W_28620 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28624 : bv 32 := 0x1840206f.
Lemma F_28624 : fetch_word Ubsan.M.loaded_segments (0x28624 : word) = Some W_28624.
Proof. vm_refl. Qed.
Lemma D_28624 : decode_any W_28624 = Some (Jal 0 8580, 4%Z).
Proof. vm_refl. Qed.

Definition W_28628 : bv 32 := 0x0007879b.
Lemma F_28628 : fetch_word Ubsan.M.loaded_segments (0x28628 : word) = Some W_28628.
Proof. vm_refl. Qed.
Lemma D_28628 : decode_any W_28628 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2862c : bv 32 := 0x00279b13.
Lemma F_2862c : fetch_word Ubsan.M.loaded_segments (0x2862c : word) = Some W_2862c.
Proof. vm_refl. Qed.
Lemma D_2862c : decode_any W_2862c = Some (ShiftImm ALU_SLL 22 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28630 : bv 32 := 0x00ab06b3.
Lemma F_28630 : fetch_word Ubsan.M.loaded_segments (0x28630 : word) = Some W_28630.
Proof. vm_refl. Qed.
Lemma D_28630 : decode_any W_28630 = Some (Op ALU_ADD 13 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28634 : bv 32 := 0x00a032b3.
Lemma F_28634 : fetch_word Ubsan.M.loaded_segments (0x28634 : word) = Some W_28634.
Proof. vm_refl. Qed.
Lemma D_28634 : decode_any W_28634 = Some (Op ALU_SLTU 5 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28638 : bv 32 := 0x0016b313.
Lemma F_28638 : fetch_word Ubsan.M.loaded_segments (0x28638 : word) = Some W_28638.
Proof. vm_refl. Qed.
Lemma D_28638 : decode_any W_28638 = Some (OpImm ALU_SLTU 6 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2863c : bv 32 := 0x00629463.
Lemma F_2863c : fetch_word Ubsan.M.loaded_segments (0x2863c : word) = Some W_2863c.
Proof. vm_refl. Qed.
Lemma D_2863c : decode_any W_2863c = Some (Branch BC_NE 5 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28640 : bv 32 := 0x1680206f.
Lemma F_28640 : fetch_word Ubsan.M.loaded_segments (0x28640 : word) = Some W_28640.
Proof. vm_refl. Qed.
Lemma D_28640 : decode_any W_28640 = Some (Jal 0 8552, 4%Z).
Proof. vm_refl. Qed.

Definition W_28644 : bv 32 := 0x00a6b333.
Lemma F_28644 : fetch_word Ubsan.M.loaded_segments (0x28644 : word) = Some W_28644.
Proof. vm_refl. Qed.
Lemma D_28644 : decode_any W_28644 = Some (Op ALU_SLTU 6 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28648 : bv 32 := 0x0007a793.
Lemma F_28648 : fetch_word Ubsan.M.loaded_segments (0x28648 : word) = Some W_28648.
Proof. vm_refl. Qed.
Lemma D_28648 : decode_any W_28648 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2864c : bv 32 := 0x00f347b3.
Lemma F_2864c : fetch_word Ubsan.M.loaded_segments (0x2864c : word) = Some W_2864c.
Proof. vm_refl. Qed.
Lemma D_2864c : decode_any W_2864c = Some (Op ALU_XOR 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28650 : bv 32 := 0x0017c793.
Lemma F_28650 : fetch_word Ubsan.M.loaded_segments (0x28650 : word) = Some W_28650.
Proof. vm_refl. Qed.
Lemma D_28650 : decode_any W_28650 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28654 : bv 32 := 0x00079463.
Lemma F_28654 : fetch_word Ubsan.M.loaded_segments (0x28654 : word) = Some W_28654.
Proof. vm_refl. Qed.
Lemma D_28654 : decode_any W_28654 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28658 : bv 32 := 0x1500206f.
Lemma F_28658 : fetch_word Ubsan.M.loaded_segments (0x28658 : word) = Some W_28658.
Proof. vm_refl. Qed.
Lemma D_28658 : decode_any W_28658 = Some (Jal 0 8528, 4%Z).
Proof. vm_refl. Qed.

Definition W_2865c : bv 32 := 0x405cd79b.
Lemma F_2865c : fetch_word Ubsan.M.loaded_segments (0x2865c : word) = Some W_2865c.
Proof. vm_refl. Qed.
Lemma D_2865c : decode_any W_2865c = Some (ShiftImm32 ALU_SRA 15 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28660 : bv 32 := 0x00279b93.
Lemma F_28660 : fetch_word Ubsan.M.loaded_segments (0x28660 : word) = Some W_28660.
Proof. vm_refl. Qed.
Lemma D_28660 : decode_any W_28660 = Some (ShiftImm ALU_SLL 23 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28664 : bv 32 := 0x017683b3.
Lemma F_28664 : fetch_word Ubsan.M.loaded_segments (0x28664 : word) = Some W_28664.
Proof. vm_refl. Qed.
Lemma D_28664 : decode_any W_28664 = Some (Op ALU_ADD 7 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_28668 : bv 32 := 0x0013b313.
Lemma F_28668 : fetch_word Ubsan.M.loaded_segments (0x28668 : word) = Some W_28668.
Proof. vm_refl. Qed.
Lemma D_28668 : decode_any W_28668 = Some (OpImm ALU_SLTU 6 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2866c : bv 32 := 0x00629463.
Lemma F_2866c : fetch_word Ubsan.M.loaded_segments (0x2866c : word) = Some W_2866c.
Proof. vm_refl. Qed.
Lemma D_2866c : decode_any W_2866c = Some (Branch BC_NE 5 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28670 : bv 32 := 0x1380206f.
Lemma F_28670 : fetch_word Ubsan.M.loaded_segments (0x28670 : word) = Some W_28670.
Proof. vm_refl. Qed.
Lemma D_28670 : decode_any W_28670 = Some (Jal 0 8504, 4%Z).
Proof. vm_refl. Qed.

Definition W_28674 : bv 32 := 0x00d3b6b3.
Lemma F_28674 : fetch_word Ubsan.M.loaded_segments (0x28674 : word) = Some W_28674.
Proof. vm_refl. Qed.
Lemma D_28674 : decode_any W_28674 = Some (Op ALU_SLTU 13 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28678 : bv 32 := 0x0007a793.
Lemma F_28678 : fetch_word Ubsan.M.loaded_segments (0x28678 : word) = Some W_28678.
Proof. vm_refl. Qed.
Lemma D_28678 : decode_any W_28678 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2867c : bv 32 := 0x00f6c6b3.
Lemma F_2867c : fetch_word Ubsan.M.loaded_segments (0x2867c : word) = Some W_2867c.
Proof. vm_refl. Qed.
Lemma D_2867c : decode_any W_2867c = Some (Op ALU_XOR 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28680 : bv 32 := 0x0016c693.
Lemma F_28680 : fetch_word Ubsan.M.loaded_segments (0x28680 : word) = Some W_28680.
Proof. vm_refl. Qed.
Lemma D_28680 : decode_any W_28680 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28684 : bv 32 := 0x00069463.
Lemma F_28684 : fetch_word Ubsan.M.loaded_segments (0x28684 : word) = Some W_28684.
Proof. vm_refl. Qed.
Lemma D_28684 : decode_any W_28684 = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28688 : bv 32 := 0x1200206f.
Lemma F_28688 : fetch_word Ubsan.M.loaded_segments (0x28688 : word) = Some W_28688.
Proof. vm_refl. Qed.
Lemma D_28688 : decode_any W_28688 = Some (Jal 0 8480, 4%Z).
Proof. vm_refl. Qed.

Definition W_2868c : bv 32 := 0xfffea697.
Lemma F_2868c : fetch_word Ubsan.M.loaded_segments (0x2868c : word) = Some W_2868c.
Proof. vm_refl. Qed.
Lemma D_2868c : decode_any W_2868c = Some (Auipc 13 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_28690 : bv 32 := 0xfff58793.
Lemma F_28690 : fetch_word Ubsan.M.loaded_segments (0x28690 : word) = Some W_28690.
Proof. vm_refl. Qed.
Lemma D_28690 : decode_any W_28690 = Some (OpImm ALU_ADD 15 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28694 : bv 32 := 0x00d00313.
Lemma F_28694 : fetch_word Ubsan.M.loaded_segments (0x28694 : word) = Some W_28694.
Proof. vm_refl. Qed.
Lemma D_28694 : decode_any W_28694 = Some (OpImm ALU_ADD 6 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28698 : bv 32 := 0xe3068693.
Lemma F_28698 : fetch_word Ubsan.M.loaded_segments (0x28698 : word) = Some W_28698.
Proof. vm_refl. Qed.
Lemma D_28698 : decode_any W_28698 = Some (OpImm ALU_ADD 13 13 3632, 4%Z).
Proof. vm_refl. Qed.

Definition W_2869c : bv 32 := 0x00f37463.
Lemma F_2869c : fetch_word Ubsan.M.loaded_segments (0x2869c : word) = Some W_2869c.
Proof. vm_refl. Qed.
Lemma D_2869c : decode_any W_2869c = Some (Branch BC_GEU 6 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_286a0 : bv 32 := 0x0100106f.
Lemma F_286a0 : fetch_word Ubsan.M.loaded_segments (0x286a0 : word) = Some W_286a0.
Proof. vm_refl. Qed.
Lemma D_286a0 : decode_any W_286a0 = Some (Jal 0 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_286a4 : bv 32 := 0x00279793.
Lemma F_286a4 : fetch_word Ubsan.M.loaded_segments (0x286a4 : word) = Some W_286a4.
Proof. vm_refl. Qed.
Lemma D_286a4 : decode_any W_286a4 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_286a8 : bv 32 := 0xfffea317.
Lemma F_286a8 : fetch_word Ubsan.M.loaded_segments (0x286a8 : word) = Some W_286a8.
Proof. vm_refl. Qed.
Lemma D_286a8 : decode_any W_286a8 = Some (Auipc 6 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_286ac : bv 32 := 0x20c30313.
Lemma F_286ac : fetch_word Ubsan.M.loaded_segments (0x286ac : word) = Some W_286ac.
Proof. vm_refl. Qed.
Lemma D_286ac : decode_any W_286ac = Some (OpImm ALU_ADD 6 6 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_286b0 : bv 32 := 0x006787b3.
Lemma F_286b0 : fetch_word Ubsan.M.loaded_segments (0x286b0 : word) = Some W_286b0.
Proof. vm_refl. Qed.
Lemma D_286b0 : decode_any W_286b0 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_286b4 : bv 32 := 0x0007a783.
Lemma F_286b4 : fetch_word Ubsan.M.loaded_segments (0x286b4 : word) = Some W_286b4.
Proof. vm_refl. Qed.
Lemma D_286b4 : decode_any W_286b4 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286b8 : bv 32 := 0x006787b3.
Lemma F_286b8 : fetch_word Ubsan.M.loaded_segments (0x286b8 : word) = Some W_286b8.
Proof. vm_refl. Qed.
Lemma D_286b8 : decode_any W_286b8 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_286bc : bv 32 := 0x00078067.
Lemma F_286bc : fetch_word Ubsan.M.loaded_segments (0x286bc : word) = Some W_286bc.
Proof. vm_refl. Qed.
Lemma D_286bc : decode_any W_286bc = Some (Jalr 0 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286c0 : bv 32 := 0x00000593.
Lemma F_286c0 : fetch_word Ubsan.M.loaded_segments (0x286c0 : word) = Some W_286c0.
Proof. vm_refl. Qed.
Lemma D_286c0 : decode_any W_286c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286c4 : bv 32 := 0x00000693.
Lemma F_286c4 : fetch_word Ubsan.M.loaded_segments (0x286c4 : word) = Some W_286c4.
Proof. vm_refl. Qed.
Lemma D_286c4 : decode_any W_286c4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286c8 : bv 32 := 0x00000c93.
Lemma F_286c8 : fetch_word Ubsan.M.loaded_segments (0x286c8 : word) = Some W_286c8.
Proof. vm_refl. Qed.
Lemma D_286c8 : decode_any W_286c8 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286cc : bv 32 := 0x015a07b3.
Lemma F_286cc : fetch_word Ubsan.M.loaded_segments (0x286cc : word) = Some W_286cc.
Proof. vm_refl. Qed.
Lemma D_286cc : decode_any W_286cc = Some (Op ALU_ADD 15 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_286d0 : bv 32 := 0xfffe4a13.
Lemma F_286d0 : fetch_word Ubsan.M.loaded_segments (0x286d0 : word) = Some W_286d0.
Proof. vm_refl. Qed.
Lemma D_286d0 : decode_any W_286d0 = Some (OpImm ALU_XOR 20 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_286d4 : bv 32 := 0x016b8b33.
Lemma F_286d4 : fetch_word Ubsan.M.loaded_segments (0x286d4 : word) = Some W_286d4.
Proof. vm_refl. Qed.
Lemma D_286d4 : decode_any W_286d4 = Some (Op ALU_ADD 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_286d8 : bv 32 := 0x0039fa93.
Lemma F_286d8 : fetch_word Ubsan.M.loaded_segments (0x286d8 : word) = Some W_286d8.
Proof. vm_refl. Qed.
Lemma D_286d8 : decode_any W_286d8 = Some (OpImm ALU_AND 21 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_286dc : bv 32 := 0x00890433.
Lemma F_286dc : fetch_word Ubsan.M.loaded_segments (0x286dc : word) = Some W_286dc.
Proof. vm_refl. Qed.
Lemma D_286dc : decode_any W_286dc = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_286e0 : bv 32 := 0x43ffd313.
Lemma F_286e0 : fetch_word Ubsan.M.loaded_segments (0x286e0 : word) = Some W_286e0.
Proof. vm_refl. Qed.
Lemma D_286e0 : decode_any W_286e0 = Some (ShiftImm ALU_SRA 6 31 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_286e4 : bv 32 := 0x01f37333.
Lemma F_286e4 : fetch_word Ubsan.M.loaded_segments (0x286e4 : word) = Some W_286e4.
Proof. vm_refl. Qed.
Lemma D_286e4 : decode_any W_286e4 = Some (Op ALU_AND 6 6 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_286e8 : bv 32 := 0x00357f93.
Lemma F_286e8 : fetch_word Ubsan.M.loaded_segments (0x286e8 : word) = Some W_286e8.
Proof. vm_refl. Qed.
Lemma D_286e8 : decode_any W_286e8 = Some (OpImm ALU_AND 31 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_286ec : bv 32 := 0x41be893b.
Lemma F_286ec : fetch_word Ubsan.M.loaded_segments (0x286ec : word) = Some W_286ec.
Proof. vm_refl. Qed.
Lemma D_286ec : decode_any W_286ec = Some (Op32 ALU_SUB 18 29 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_286f0 : bv 32 := 0x41e787bb.
Lemma F_286f0 : fetch_word Ubsan.M.loaded_segments (0x286f0 : word) = Some W_286f0.
Proof. vm_refl. Qed.
Lemma D_286f0 : decode_any W_286f0 = Some (Op32 ALU_SUB 15 15 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_286f4 : bv 32 := 0x02000f13.
Lemma F_286f4 : fetch_word Ubsan.M.loaded_segments (0x286f4 : word) = Some W_286f4.
Proof. vm_refl. Qed.
Lemma D_286f4 : decode_any W_286f4 = Some (OpImm ALU_ADD 30 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_286f8 : bv 32 := 0x01650533.
Lemma F_286f8 : fetch_word Ubsan.M.loaded_segments (0x286f8 : word) = Some W_286f8.
Proof. vm_refl. Qed.
Lemma D_286f8 : decode_any W_286f8 = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_286fc : bv 32 := 0x008989b3.
Lemma F_286fc : fetch_word Ubsan.M.loaded_segments (0x286fc : word) = Some W_286fc.
Proof. vm_refl. Qed.
Lemma D_286fc : decode_any W_286fc = Some (Op ALU_ADD 19 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28700 : bv 32 := 0x006787b3.
Lemma F_28700 : fetch_word Ubsan.M.loaded_segments (0x28700 : word) = Some W_28700.
Proof. vm_refl. Qed.
Lemma D_28700 : decode_any W_28700 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28704 : bv 32 := 0x41d787bb.
Lemma F_28704 : fetch_word Ubsan.M.loaded_segments (0x28704 : word) = Some W_28704.
Proof. vm_refl. Qed.
Lemma D_28704 : decode_any W_28704 = Some (Op32 ALU_SUB 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_28708 : bv 32 := 0x43f7d313.
Lemma F_28708 : fetch_word Ubsan.M.loaded_segments (0x28708 : word) = Some W_28708.
Proof. vm_refl. Qed.
Lemma D_28708 : decode_any W_28708 = Some (ShiftImm ALU_SRA 6 15 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_2870c : bv 32 := 0x00f377b3.
Lemma F_2870c : fetch_word Ubsan.M.loaded_segments (0x2870c : word) = Some W_2870c.
Proof. vm_refl. Qed.
Lemma D_2870c : decode_any W_2870c = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28710 : bv 32 := 0x00f907b3.
Lemma F_28710 : fetch_word Ubsan.M.loaded_segments (0x28710 : word) = Some W_28710.
Proof. vm_refl. Qed.
Lemma D_28710 : decode_any W_28710 = Some (Op ALU_ADD 15 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28714 : bv 32 := 0x0057d79b.
Lemma F_28714 : fetch_word Ubsan.M.loaded_segments (0x28714 : word) = Some W_28714.
Proof. vm_refl. Qed.
Lemma D_28714 : decode_any W_28714 = Some (ShiftImm32 ALU_SRL 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28718 : bv 32 := 0x40f00eb3.
Lemma F_28718 : fetch_word Ubsan.M.loaded_segments (0x28718 : word) = Some W_28718.
Proof. vm_refl. Qed.
Lemma D_28718 : decode_any W_28718 = Some (Op ALU_SUB 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2871c : bv 32 := 0xffb00413.
Lemma F_2871c : fetch_word Ubsan.M.loaded_segments (0x2871c : word) = Some W_2871c.
Proof. vm_refl. Qed.
Lemma D_2871c : decode_any W_2871c = Some (OpImm ALU_ADD 8 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_28720 : bv 32 := 0x05813083.
Lemma F_28720 : fetch_word Ubsan.M.loaded_segments (0x28720 : word) = Some W_28720.
Proof. vm_refl. Qed.
Lemma D_28720 : decode_any W_28720 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28724 : bv 32 := 0x03c0006f.
Lemma F_28724 : fetch_word Ubsan.M.loaded_segments (0x28724 : word) = Some W_28724.
Proof. vm_refl. Qed.
Lemma D_28724 : decode_any W_28724 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_28728 : bv 32 := 0x00092303.
Lemma F_28728 : fetch_word Ubsan.M.loaded_segments (0x28728 : word) = Some W_28728.
Proof. vm_refl. Qed.
Lemma D_28728 : decode_any W_28728 = Some (Load SZ4 true 6 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2872c : bv 32 := 0x0007a783.
Lemma F_2872c : fetch_word Ubsan.M.loaded_segments (0x2872c : word) = Some W_2872c.
Proof. vm_refl. Qed.
Lemma D_2872c : decode_any W_2872c = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28730 : bv 32 := 0x01437b33.
Lemma F_28730 : fetch_word Ubsan.M.loaded_segments (0x28730 : word) = Some W_28730.
Proof. vm_refl. Qed.
Lemma D_28730 : decode_any W_28730 = Some (Op ALU_AND 22 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_28734 : bv 32 := 0x0067e7b3.
Lemma F_28734 : fetch_word Ubsan.M.loaded_segments (0x28734 : word) = Some W_28734.
Proof. vm_refl. Qed.
Lemma D_28734 : decode_any W_28734 = Some (Op ALU_OR 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28738 : bv 32 := 0xfff7c793.
Lemma F_28738 : fetch_word Ubsan.M.loaded_segments (0x28738 : word) = Some W_28738.
Proof. vm_refl. Qed.
Lemma D_28738 : decode_any W_28738 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_2873c : bv 32 := 0x00fe77b3.
Lemma F_2873c : fetch_word Ubsan.M.loaded_segments (0x2873c : word) = Some W_2873c.
Proof. vm_refl. Qed.
Lemma D_2873c : decode_any W_2873c = Some (Op ALU_AND 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28740 : bv 32 := 0x0167e7b3.
Lemma F_28740 : fetch_word Ubsan.M.loaded_segments (0x28740 : word) = Some W_28740.
Proof. vm_refl. Qed.
Lemma D_28740 : decode_any W_28740 = Some (Op ALU_OR 15 15 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_28744 : bv 32 := 0x00f92023.
Lemma F_28744 : fetch_word Ubsan.M.loaded_segments (0x28744 : word) = Some W_28744.
Proof. vm_refl. Qed.
Lemma D_28744 : decode_any W_28744 = Some (Store SZ4 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28748 : bv 32 := 0x001c8c9b.
Lemma F_28748 : fetch_word Ubsan.M.loaded_segments (0x28748 : word) = Some W_28748.
Proof. vm_refl. Qed.
Lemma D_28748 : decode_any W_28748 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2874c : bv 32 := 0x00e686bb.
Lemma F_2874c : fetch_word Ubsan.M.loaded_segments (0x2874c : word) = Some W_2874c.
Proof. vm_refl. Qed.
Lemma D_2874c : decode_any W_2874c = Some (Op32 ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_28750 : bv 32 := 0x001585bb.
Lemma F_28750 : fetch_word Ubsan.M.loaded_segments (0x28750 : word) = Some W_28750.
Proof. vm_refl. Qed.
Lemma D_28750 : decode_any W_28750 = Some (Op32 ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28754 : bv 32 := 0x08013783.
Lemma F_28754 : fetch_word Ubsan.M.loaded_segments (0x28754 : word) = Some W_28754.
Proof. vm_refl. Qed.
Lemma D_28754 : decode_any W_28754 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_28758 : bv 32 := 0x00fc9463.
Lemma F_28758 : fetch_word Ubsan.M.loaded_segments (0x28758 : word) = Some W_28758.
Proof. vm_refl. Qed.
Lemma D_28758 : decode_any W_28758 = Some (Branch BC_NE 25 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2875c : bv 32 := 0x1100706f.
Lemma F_2875c : fetch_word Ubsan.M.loaded_segments (0x2875c : word) = Some W_2875c.
Proof. vm_refl. Qed.
Lemma D_2875c : decode_any W_2875c = Some (Jal 0 28944, 4%Z).
Proof. vm_refl. Qed.

Definition W_28760 : bv 32 := 0x021c8333.
Lemma F_28760 : fetch_word Ubsan.M.loaded_segments (0x28760 : word) = Some W_28760.
Proof. vm_refl. Qed.
Lemma D_28760 : decode_any W_28760 = Some (Mul M_MUL 6 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28764 : bv 32 := 0x021c87bb.
Lemma F_28764 : fetch_word Ubsan.M.loaded_segments (0x28764 : word) = Some W_28764.
Proof. vm_refl. Qed.
Lemma D_28764 : decode_any W_28764 = Some (Mul32 M_MUL 15 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28768 : bv 32 := 0x00678463.
Lemma F_28768 : fetch_word Ubsan.M.loaded_segments (0x28768 : word) = Some W_28768.
Proof. vm_refl. Qed.
Lemma D_28768 : decode_any W_28768 = Some (Branch BC_EQ 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2876c : bv 32 := 0x03c0206f.
Lemma F_2876c : fetch_word Ubsan.M.loaded_segments (0x2876c : word) = Some W_2876c.
Proof. vm_refl. Qed.
Lemma D_2876c : decode_any W_2876c = Some (Jal 0 8252, 4%Z).
Proof. vm_refl. Qed.

Definition W_28770 : bv 32 := 0x0003031b.
Lemma F_28770 : fetch_word Ubsan.M.loaded_segments (0x28770 : word) = Some W_28770.
Proof. vm_refl. Qed.
Lemma D_28770 : decode_any W_28770 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28774 : bv 32 := 0x00231793.
Lemma F_28774 : fetch_word Ubsan.M.loaded_segments (0x28774 : word) = Some W_28774.
Proof. vm_refl. Qed.
Lemma D_28774 : decode_any W_28774 = Some (ShiftImm ALU_SLL 15 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28778 : bv 32 := 0x00f887b3.
Lemma F_28778 : fetch_word Ubsan.M.loaded_segments (0x28778 : word) = Some W_28778.
Proof. vm_refl. Qed.
Lemma D_28778 : decode_any W_28778 = Some (Op ALU_ADD 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2877c : bv 32 := 0x0017b913.
Lemma F_2877c : fetch_word Ubsan.M.loaded_segments (0x2877c : word) = Some W_2877c.
Proof. vm_refl. Qed.
Lemma D_2877c : decode_any W_2877c = Some (OpImm ALU_SLTU 18 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28780 : bv 32 := 0x01281463.
Lemma F_28780 : fetch_word Ubsan.M.loaded_segments (0x28780 : word) = Some W_28780.
Proof. vm_refl. Qed.
Lemma D_28780 : decode_any W_28780 = Some (Branch BC_NE 16 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28784 : bv 32 := 0x0240206f.
Lemma F_28784 : fetch_word Ubsan.M.loaded_segments (0x28784 : word) = Some W_28784.
Proof. vm_refl. Qed.
Lemma D_28784 : decode_any W_28784 = Some (Jal 0 8228, 4%Z).
Proof. vm_refl. Qed.

Definition W_28788 : bv 32 := 0x0117b933.
Lemma F_28788 : fetch_word Ubsan.M.loaded_segments (0x28788 : word) = Some W_28788.
Proof. vm_refl. Qed.
Lemma D_28788 : decode_any W_28788 = Some (Op ALU_SLTU 18 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_2878c : bv 32 := 0x00032313.
Lemma F_2878c : fetch_word Ubsan.M.loaded_segments (0x2878c : word) = Some W_2878c.
Proof. vm_refl. Qed.
Lemma D_2878c : decode_any W_2878c = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28790 : bv 32 := 0x00694333.
Lemma F_28790 : fetch_word Ubsan.M.loaded_segments (0x28790 : word) = Some W_28790.
Proof. vm_refl. Qed.
Lemma D_28790 : decode_any W_28790 = Some (Op ALU_XOR 6 18 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28794 : bv 32 := 0x00134313.
Lemma F_28794 : fetch_word Ubsan.M.loaded_segments (0x28794 : word) = Some W_28794.
Proof. vm_refl. Qed.
Lemma D_28794 : decode_any W_28794 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28798 : bv 32 := 0x00031463.
Lemma F_28798 : fetch_word Ubsan.M.loaded_segments (0x28798 : word) = Some W_28798.
Proof. vm_refl. Qed.
Lemma D_28798 : decode_any W_28798 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2879c : bv 32 := 0x00c0206f.
Lemma F_2879c : fetch_word Ubsan.M.loaded_segments (0x2879c : word) = Some W_2879c.
Proof. vm_refl. Qed.
Lemma D_2879c : decode_any W_2879c = Some (Jal 0 8204, 4%Z).
Proof. vm_refl. Qed.

Definition W_287a0 : bv 32 := 0x02ec8333.
Lemma F_287a0 : fetch_word Ubsan.M.loaded_segments (0x287a0 : word) = Some W_287a0.
Proof. vm_refl. Qed.
Lemma D_287a0 : decode_any W_287a0 = Some (Mul M_MUL 6 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_287a4 : bv 32 := 0x02ec893b.
Lemma F_287a4 : fetch_word Ubsan.M.loaded_segments (0x287a4 : word) = Some W_287a4.
Proof. vm_refl. Qed.
Lemma D_287a4 : decode_any W_287a4 = Some (Mul32 M_MUL 18 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_287a8 : bv 32 := 0x00690463.
Lemma F_287a8 : fetch_word Ubsan.M.loaded_segments (0x287a8 : word) = Some W_287a8.
Proof. vm_refl. Qed.
Lemma D_287a8 : decode_any W_287a8 = Some (Branch BC_EQ 18 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_287ac : bv 32 := 0x7fd0106f.
Lemma F_287ac : fetch_word Ubsan.M.loaded_segments (0x287ac : word) = Some W_287ac.
Proof. vm_refl. Qed.
Lemma D_287ac : decode_any W_287ac = Some (Jal 0 8188, 4%Z).
Proof. vm_refl. Qed.

Definition W_287b0 : bv 32 := 0x0003031b.
Lemma F_287b0 : fetch_word Ubsan.M.loaded_segments (0x287b0 : word) = Some W_287b0.
Proof. vm_refl. Qed.
Lemma D_287b0 : decode_any W_287b0 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_287b4 : bv 32 := 0x00231913.
Lemma F_287b4 : fetch_word Ubsan.M.loaded_segments (0x287b4 : word) = Some W_287b4.
Proof. vm_refl. Qed.
Lemma D_287b4 : decode_any W_287b4 = Some (ShiftImm ALU_SLL 18 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_287b8 : bv 32 := 0x00790933.
Lemma F_287b8 : fetch_word Ubsan.M.loaded_segments (0x287b8 : word) = Some W_287b8.
Proof. vm_refl. Qed.
Lemma D_287b8 : decode_any W_287b8 = Some (Op ALU_ADD 18 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_287bc : bv 32 := 0x00193b13.
Lemma F_287bc : fetch_word Ubsan.M.loaded_segments (0x287bc : word) = Some W_287bc.
Proof. vm_refl. Qed.
Lemma D_287bc : decode_any W_287bc = Some (OpImm ALU_SLTU 22 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_287c0 : bv 32 := 0x01629463.
Lemma F_287c0 : fetch_word Ubsan.M.loaded_segments (0x287c0 : word) = Some W_287c0.
Proof. vm_refl. Qed.
Lemma D_287c0 : decode_any W_287c0 = Some (Branch BC_NE 5 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_287c4 : bv 32 := 0x7e50106f.
Lemma F_287c4 : fetch_word Ubsan.M.loaded_segments (0x287c4 : word) = Some W_287c4.
Proof. vm_refl. Qed.
Lemma D_287c4 : decode_any W_287c4 = Some (Jal 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_287c8 : bv 32 := 0x00793b33.
Lemma F_287c8 : fetch_word Ubsan.M.loaded_segments (0x287c8 : word) = Some W_287c8.
Proof. vm_refl. Qed.
Lemma D_287c8 : decode_any W_287c8 = Some (Op ALU_SLTU 22 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_287cc : bv 32 := 0x00032313.
Lemma F_287cc : fetch_word Ubsan.M.loaded_segments (0x287cc : word) = Some W_287cc.
Proof. vm_refl. Qed.
Lemma D_287cc : decode_any W_287cc = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_287d0 : bv 32 := 0x006b4333.
Lemma F_287d0 : fetch_word Ubsan.M.loaded_segments (0x287d0 : word) = Some W_287d0.
Proof. vm_refl. Qed.
Lemma D_287d0 : decode_any W_287d0 = Some (Op ALU_XOR 6 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_287d4 : bv 32 := 0x00134313.
Lemma F_287d4 : fetch_word Ubsan.M.loaded_segments (0x287d4 : word) = Some W_287d4.
Proof. vm_refl. Qed.
Lemma D_287d4 : decode_any W_287d4 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_287d8 : bv 32 := 0x00031463.
Lemma F_287d8 : fetch_word Ubsan.M.loaded_segments (0x287d8 : word) = Some W_287d8.
Proof. vm_refl. Qed.
Lemma D_287d8 : decode_any W_287d8 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_287dc : bv 32 := 0x7cd0106f.
Lemma F_287dc : fetch_word Ubsan.M.loaded_segments (0x287dc : word) = Some W_287dc.
Proof. vm_refl. Qed.
Lemma D_287dc : decode_any W_287dc = Some (Jal 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_287e0 : bv 32 := 0x07e4ee63.
Lemma F_287e0 : fetch_word Ubsan.M.loaded_segments (0x287e0 : word) = Some W_287e0.
Proof. vm_refl. Qed.
Lemma D_287e0 : decode_any W_287e0 = Some (Branch BC_LTU 9 30 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_287e4 : bv 32 := 0x000a8463.
Lemma F_287e4 : fetch_word Ubsan.M.loaded_segments (0x287e4 : word) = Some W_287e4.
Proof. vm_refl. Qed.
Lemma D_287e4 : decode_any W_287e4 = Some (Branch BC_EQ 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_287e8 : bv 32 := 0x7c10106f.
Lemma F_287e8 : fetch_word Ubsan.M.loaded_segments (0x287e8 : word) = Some W_287e8.
Proof. vm_refl. Qed.
Lemma D_287e8 : decode_any W_287e8 = Some (Jal 0 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_287ec : bv 32 := 0x00000793.
Lemma F_287ec : fetch_word Ubsan.M.loaded_segments (0x287ec : word) = Some W_287ec.
Proof. vm_refl. Qed.
Lemma D_287ec : decode_any W_287ec = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_287f0 : bv 32 := 0x00269913.
Lemma F_287f0 : fetch_word Ubsan.M.loaded_segments (0x287f0 : word) = Some W_287f0.
Proof. vm_refl. Qed.
Lemma D_287f0 : decode_any W_287f0 = Some (ShiftImm ALU_SLL 18 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_287f4 : bv 32 := 0x00259b13.
Lemma F_287f4 : fetch_word Ubsan.M.loaded_segments (0x287f4 : word) = Some W_287f4.
Proof. vm_refl. Qed.
Lemma D_287f4 : decode_any W_287f4 = Some (ShiftImm ALU_SLL 22 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_287f8 : bv 32 := 0x01250933.
Lemma F_287f8 : fetch_word Ubsan.M.loaded_segments (0x287f8 : word) = Some W_287f8.
Proof. vm_refl. Qed.
Lemma D_287f8 : decode_any W_287f8 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_287fc : bv 32 := 0x01698b33.
Lemma F_287fc : fetch_word Ubsan.M.loaded_segments (0x287fc : word) = Some W_287fc.
Proof. vm_refl. Qed.
Lemma D_287fc : decode_any W_287fc = Some (Op ALU_ADD 22 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_28800 : bv 32 := 0x000e8b93.
Lemma F_28800 : fetch_word Ubsan.M.loaded_segments (0x28800 : word) = Some W_28800.
Proof. vm_refl. Qed.
Lemma D_28800 : decode_any W_28800 = Some (OpImm ALU_ADD 23 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28804 : bv 32 := 0x00fb0333.
Lemma F_28804 : fetch_word Ubsan.M.loaded_segments (0x28804 : word) = Some W_28804.
Proof. vm_refl. Qed.
Lemma D_28804 : decode_any W_28804 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28808 : bv 32 := 0x00031463.
Lemma F_28808 : fetch_word Ubsan.M.loaded_segments (0x28808 : word) = Some W_28808.
Proof. vm_refl. Qed.
Lemma D_28808 : decode_any W_28808 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2880c : bv 32 := 0x79d0106f.
Lemma F_2880c : fetch_word Ubsan.M.loaded_segments (0x2880c : word) = Some W_2880c.
Proof. vm_refl. Qed.
Lemma D_2880c : decode_any W_2880c = Some (Jal 0 8092, 4%Z).
Proof. vm_refl. Qed.

Definition W_28810 : bv 32 := 0x000f8463.
Lemma F_28810 : fetch_word Ubsan.M.loaded_segments (0x28810 : word) = Some W_28810.
Proof. vm_refl. Qed.
Lemma D_28810 : decode_any W_28810 = Some (Branch BC_EQ 31 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28814 : bv 32 := 0x7950106f.
Lemma F_28814 : fetch_word Ubsan.M.loaded_segments (0x28814 : word) = Some W_28814.
Proof. vm_refl. Qed.
Lemma D_28814 : decode_any W_28814 = Some (Jal 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_28818 : bv 32 := 0x00f90c33.
Lemma F_28818 : fetch_word Ubsan.M.loaded_segments (0x28818 : word) = Some W_28818.
Proof. vm_refl. Qed.
Lemma D_28818 : decode_any W_28818 = Some (Op ALU_ADD 24 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2881c : bv 32 := 0x000c1463.
Lemma F_2881c : fetch_word Ubsan.M.loaded_segments (0x2881c : word) = Some W_2881c.
Proof. vm_refl. Qed.
Lemma D_2881c : decode_any W_2881c = Some (Branch BC_NE 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28820 : bv 32 := 0x7890106f.
Lemma F_28820 : fetch_word Ubsan.M.loaded_segments (0x28820 : word) = Some W_28820.
Proof. vm_refl. Qed.
Lemma D_28820 : decode_any W_28820 = Some (Jal 0 8072, 4%Z).
Proof. vm_refl. Qed.

Definition W_28824 : bv 32 := 0x00032d03.
Lemma F_28824 : fetch_word Ubsan.M.loaded_segments (0x28824 : word) = Some W_28824.
Proof. vm_refl. Qed.
Lemma D_28824 : decode_any W_28824 = Some (Load SZ4 true 26 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28828 : bv 32 := 0x000c2d83.
Lemma F_28828 : fetch_word Ubsan.M.loaded_segments (0x28828 : word) = Some W_28828.
Proof. vm_refl. Qed.
Lemma D_28828 : decode_any W_28828 = Some (Load SZ4 true 27 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2882c : bv 32 := 0x01aded33.
Lemma F_2882c : fetch_word Ubsan.M.loaded_segments (0x2882c : word) = Some W_2882c.
Proof. vm_refl. Qed.
Lemma D_2882c : decode_any W_2882c = Some (Op ALU_OR 26 27 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_28830 : bv 32 := 0xfffd4d13.
Lemma F_28830 : fetch_word Ubsan.M.loaded_segments (0x28830 : word) = Some W_28830.
Proof. vm_refl. Qed.
Lemma D_28830 : decode_any W_28830 = Some (OpImm ALU_XOR 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28834 : bv 32 := 0x01ac2023.
Lemma F_28834 : fetch_word Ubsan.M.loaded_segments (0x28834 : word) = Some W_28834.
Proof. vm_refl. Qed.
Lemma D_28834 : decode_any W_28834 = Some (Store SZ4 24 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28838 : bv 32 := 0x01847463.
Lemma F_28838 : fetch_word Ubsan.M.loaded_segments (0x28838 : word) = Some W_28838.
Proof. vm_refl. Qed.
Lemma D_28838 : decode_any W_28838 = Some (Branch BC_GEU 8 24 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2883c : bv 32 := 0x76d0106f.
Lemma F_2883c : fetch_word Ubsan.M.loaded_segments (0x2883c : word) = Some W_2883c.
Proof. vm_refl. Qed.
Lemma D_2883c : decode_any W_2883c = Some (Jal 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_28840 : bv 32 := 0x00647463.
Lemma F_28840 : fetch_word Ubsan.M.loaded_segments (0x28840 : word) = Some W_28840.
Proof. vm_refl. Qed.
Lemma D_28840 : decode_any W_28840 = Some (Branch BC_GEU 8 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28844 : bv 32 := 0x7650106f.
Lemma F_28844 : fetch_word Ubsan.M.loaded_segments (0x28844 : word) = Some W_28844.
Proof. vm_refl. Qed.
Lemma D_28844 : decode_any W_28844 = Some (Jal 0 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_28848 : bv 32 := 0x001b8b9b.
Lemma F_28848 : fetch_word Ubsan.M.loaded_segments (0x28848 : word) = Some W_28848.
Proof. vm_refl. Qed.
Lemma D_28848 : decode_any W_28848 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2884c : bv 32 := 0x00478793.
Lemma F_2884c : fetch_word Ubsan.M.loaded_segments (0x2884c : word) = Some W_2884c.
Proof. vm_refl. Qed.
Lemma D_2884c : decode_any W_2884c = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_28850 : bv 32 := 0xfa0b9ae3.
Lemma F_28850 : fetch_word Ubsan.M.loaded_segments (0x28850 : word) = Some W_28850.
Proof. vm_refl. Qed.
Lemma D_28850 : decode_any W_28850 = Some (Branch BC_NE 23 0 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_28854 : bv 32 := 0x00f90933.
Lemma F_28854 : fetch_word Ubsan.M.loaded_segments (0x28854 : word) = Some W_28854.
Proof. vm_refl. Qed.
Lemma D_28854 : decode_any W_28854 = Some (Op ALU_ADD 18 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28858 : bv 32 := 0x00fb07b3.
Lemma F_28858 : fetch_word Ubsan.M.loaded_segments (0x28858 : word) = Some W_28858.
Proof. vm_refl. Qed.
Lemma D_28858 : decode_any W_28858 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_2885c : bv 32 := 0xee0606e3.
Lemma F_2885c : fetch_word Ubsan.M.loaded_segments (0x2885c : word) = Some W_2885c.
Proof. vm_refl. Qed.
Lemma D_2885c : decode_any W_2885c = Some (Branch BC_EQ 12 0 7916, 4%Z).
Proof. vm_refl. Qed.

Definition W_28860 : bv 32 := 0x00091463.
Lemma F_28860 : fetch_word Ubsan.M.loaded_segments (0x28860 : word) = Some W_28860.
Proof. vm_refl. Qed.
Lemma D_28860 : decode_any W_28860 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28864 : bv 32 := 0x7450106f.
Lemma F_28864 : fetch_word Ubsan.M.loaded_segments (0x28864 : word) = Some W_28864.
Proof. vm_refl. Qed.
Lemma D_28864 : decode_any W_28864 = Some (Jal 0 8004, 4%Z).
Proof. vm_refl. Qed.

Definition W_28868 : bv 32 := 0x00397313.
Lemma F_28868 : fetch_word Ubsan.M.loaded_segments (0x28868 : word) = Some W_28868.
Proof. vm_refl. Qed.
Lemma D_28868 : decode_any W_28868 = Some (OpImm ALU_AND 6 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_2886c : bv 32 := 0x00030463.
Lemma F_2886c : fetch_word Ubsan.M.loaded_segments (0x2886c : word) = Some W_2886c.
Proof. vm_refl. Qed.
Lemma D_2886c : decode_any W_2886c = Some (Branch BC_EQ 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28870 : bv 32 := 0x7390106f.
Lemma F_28870 : fetch_word Ubsan.M.loaded_segments (0x28870 : word) = Some W_28870.
Proof. vm_refl. Qed.
Lemma D_28870 : decode_any W_28870 = Some (Jal 0 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_28874 : bv 32 := 0x00079463.
Lemma F_28874 : fetch_word Ubsan.M.loaded_segments (0x28874 : word) = Some W_28874.
Proof. vm_refl. Qed.
Lemma D_28874 : decode_any W_28874 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28878 : bv 32 := 0x7310106f.
Lemma F_28878 : fetch_word Ubsan.M.loaded_segments (0x28878 : word) = Some W_28878.
Proof. vm_refl. Qed.
Lemma D_28878 : decode_any W_28878 = Some (Jal 0 7984, 4%Z).
Proof. vm_refl. Qed.

Definition W_2887c : bv 32 := 0x0037f313.
Lemma F_2887c : fetch_word Ubsan.M.loaded_segments (0x2887c : word) = Some W_2887c.
Proof. vm_refl. Qed.
Lemma D_2887c : decode_any W_2887c = Some (OpImm ALU_AND 6 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_28880 : bv 32 := 0xea0304e3.
Lemma F_28880 : fetch_word Ubsan.M.loaded_segments (0x28880 : word) = Some W_28880.
Proof. vm_refl. Qed.
Lemma D_28880 : decode_any W_28880 = Some (Branch BC_EQ 6 0 7848, 4%Z).
Proof. vm_refl. Qed.

Definition W_28884 : bv 32 := 0x7250106f.
Lemma F_28884 : fetch_word Ubsan.M.loaded_segments (0x28884 : word) = Some W_28884.
Proof. vm_refl. Qed.
Lemma D_28884 : decode_any W_28884 = Some (Jal 0 7972, 4%Z).
Proof. vm_refl. Qed.

Definition W_28888 : bv 32 := 0x00545f9b.
Lemma F_28888 : fetch_word Ubsan.M.loaded_segments (0x28888 : word) = Some W_28888.
Proof. vm_refl. Qed.
Lemma D_28888 : decode_any W_28888 = Some (ShiftImm32 ALU_SRL 31 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2888c : bv 32 := 0x0e0f86e3.
Lemma F_2888c : fetch_word Ubsan.M.loaded_segments (0x2888c : word) = Some W_2888c.
Proof. vm_refl. Qed.
Lemma D_2888c : decode_any W_2888c = Some (Branch BC_EQ 31 0 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_28890 : bv 32 := 0x02770833.
Lemma F_28890 : fetch_word Ubsan.M.loaded_segments (0x28890 : word) = Some W_28890.
Proof. vm_refl. Qed.
Lemma D_28890 : decode_any W_28890 = Some (Mul M_MUL 16 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28894 : bv 32 := 0x0277063b.
Lemma F_28894 : fetch_word Ubsan.M.loaded_segments (0x28894 : word) = Some W_28894.
Proof. vm_refl. Qed.
Lemma D_28894 : decode_any W_28894 = Some (Mul32 M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28898 : bv 32 := 0x01060463.
Lemma F_28898 : fetch_word Ubsan.M.loaded_segments (0x28898 : word) = Some W_28898.
Proof. vm_refl. Qed.
Lemma D_28898 : decode_any W_28898 = Some (Branch BC_EQ 12 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2889c : bv 32 := 0x70d0106f.
Lemma F_2889c : fetch_word Ubsan.M.loaded_segments (0x2889c : word) = Some W_2889c.
Proof. vm_refl. Qed.
Lemma D_2889c : decode_any W_2889c = Some (Jal 0 7948, 4%Z).
Proof. vm_refl. Qed.

Definition W_288a0 : bv 32 := 0x0008081b.
Lemma F_288a0 : fetch_word Ubsan.M.loaded_segments (0x288a0 : word) = Some W_288a0.
Proof. vm_refl. Qed.
Lemma D_288a0 : decode_any W_288a0 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_288a4 : bv 32 := 0x00281613.
Lemma F_288a4 : fetch_word Ubsan.M.loaded_segments (0x288a4 : word) = Some W_288a4.
Proof. vm_refl. Qed.
Lemma D_288a4 : decode_any W_288a4 = Some (ShiftImm ALU_SLL 12 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_288a8 : bv 32 := 0x00a60633.
Lemma F_288a8 : fetch_word Ubsan.M.loaded_segments (0x288a8 : word) = Some W_288a8.
Proof. vm_refl. Qed.
Lemma D_288a8 : decode_any W_288a8 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_288ac : bv 32 := 0x00a037b3.
Lemma F_288ac : fetch_word Ubsan.M.loaded_segments (0x288ac : word) = Some W_288ac.
Proof. vm_refl. Qed.
Lemma D_288ac : decode_any W_288ac = Some (Op ALU_SLTU 15 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_288b0 : bv 32 := 0x00163893.
Lemma F_288b0 : fetch_word Ubsan.M.loaded_segments (0x288b0 : word) = Some W_288b0.
Proof. vm_refl. Qed.
Lemma D_288b0 : decode_any W_288b0 = Some (OpImm ALU_SLTU 17 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_288b4 : bv 32 := 0x01179463.
Lemma F_288b4 : fetch_word Ubsan.M.loaded_segments (0x288b4 : word) = Some W_288b4.
Proof. vm_refl. Qed.
Lemma D_288b4 : decode_any W_288b4 = Some (Branch BC_NE 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_288b8 : bv 32 := 0x6f10106f.
Lemma F_288b8 : fetch_word Ubsan.M.loaded_segments (0x288b8 : word) = Some W_288b8.
Proof. vm_refl. Qed.
Lemma D_288b8 : decode_any W_288b8 = Some (Jal 0 7920, 4%Z).
Proof. vm_refl. Qed.

Definition W_288bc : bv 32 := 0x00a638b3.
Lemma F_288bc : fetch_word Ubsan.M.loaded_segments (0x288bc : word) = Some W_288bc.
Proof. vm_refl. Qed.
Lemma D_288bc : decode_any W_288bc = Some (Op ALU_SLTU 17 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_288c0 : bv 32 := 0x00082813.
Lemma F_288c0 : fetch_word Ubsan.M.loaded_segments (0x288c0 : word) = Some W_288c0.
Proof. vm_refl. Qed.
Lemma D_288c0 : decode_any W_288c0 = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_288c4 : bv 32 := 0x0108c833.
Lemma F_288c4 : fetch_word Ubsan.M.loaded_segments (0x288c4 : word) = Some W_288c4.
Proof. vm_refl. Qed.
Lemma D_288c4 : decode_any W_288c4 = Some (Op ALU_XOR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_288c8 : bv 32 := 0x00184813.
Lemma F_288c8 : fetch_word Ubsan.M.loaded_segments (0x288c8 : word) = Some W_288c8.
Proof. vm_refl. Qed.
Lemma D_288c8 : decode_any W_288c8 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_288cc : bv 32 := 0x00081463.
Lemma F_288cc : fetch_word Ubsan.M.loaded_segments (0x288cc : word) = Some W_288cc.
Proof. vm_refl. Qed.
Lemma D_288cc : decode_any W_288cc = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_288d0 : bv 32 := 0x6d90106f.
Lemma F_288d0 : fetch_word Ubsan.M.loaded_segments (0x288d0 : word) = Some W_288d0.
Proof. vm_refl. Qed.
Lemma D_288d0 : decode_any W_288d0 = Some (Jal 0 7896, 4%Z).
Proof. vm_refl. Qed.

Definition W_288d4 : bv 32 := 0x405cd81b.
Lemma F_288d4 : fetch_word Ubsan.M.loaded_segments (0x288d4 : word) = Some W_288d4.
Proof. vm_refl. Qed.
Lemma D_288d4 : decode_any W_288d4 = Some (ShiftImm32 ALU_SRA 16 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_288d8 : bv 32 := 0x00281413.
Lemma F_288d8 : fetch_word Ubsan.M.loaded_segments (0x288d8 : word) = Some W_288d8.
Proof. vm_refl. Qed.
Lemma D_288d8 : decode_any W_288d8 = Some (ShiftImm ALU_SLL 8 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_288dc : bv 32 := 0x00860433.
Lemma F_288dc : fetch_word Ubsan.M.loaded_segments (0x288dc : word) = Some W_288dc.
Proof. vm_refl. Qed.
Lemma D_288dc : decode_any W_288dc = Some (Op ALU_ADD 8 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_288e0 : bv 32 := 0x00143893.
Lemma F_288e0 : fetch_word Ubsan.M.loaded_segments (0x288e0 : word) = Some W_288e0.
Proof. vm_refl. Qed.
Lemma D_288e0 : decode_any W_288e0 = Some (OpImm ALU_SLTU 17 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_288e4 : bv 32 := 0x01179463.
Lemma F_288e4 : fetch_word Ubsan.M.loaded_segments (0x288e4 : word) = Some W_288e4.
Proof. vm_refl. Qed.
Lemma D_288e4 : decode_any W_288e4 = Some (Branch BC_NE 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_288e8 : bv 32 := 0x6c10106f.
Lemma F_288e8 : fetch_word Ubsan.M.loaded_segments (0x288e8 : word) = Some W_288e8.
Proof. vm_refl. Qed.
Lemma D_288e8 : decode_any W_288e8 = Some (Jal 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_288ec : bv 32 := 0x00c43633.
Lemma F_288ec : fetch_word Ubsan.M.loaded_segments (0x288ec : word) = Some W_288ec.
Proof. vm_refl. Qed.
Lemma D_288ec : decode_any W_288ec = Some (Op ALU_SLTU 12 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_288f0 : bv 32 := 0x00082793.
Lemma F_288f0 : fetch_word Ubsan.M.loaded_segments (0x288f0 : word) = Some W_288f0.
Proof. vm_refl. Qed.
Lemma D_288f0 : decode_any W_288f0 = Some (OpImm ALU_SLT 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_288f4 : bv 32 := 0x00f64633.
Lemma F_288f4 : fetch_word Ubsan.M.loaded_segments (0x288f4 : word) = Some W_288f4.
Proof. vm_refl. Qed.
Lemma D_288f4 : decode_any W_288f4 = Some (Op ALU_XOR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_288f8 : bv 32 := 0x00164613.
Lemma F_288f8 : fetch_word Ubsan.M.loaded_segments (0x288f8 : word) = Some W_288f8.
Proof. vm_refl. Qed.
Lemma D_288f8 : decode_any W_288f8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_288fc : bv 32 := 0x00061463.
Lemma F_288fc : fetch_word Ubsan.M.loaded_segments (0x288fc : word) = Some W_288fc.
Proof. vm_refl. Qed.
Lemma D_288fc : decode_any W_288fc = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28900 : bv 32 := 0x6a90106f.
Lemma F_28900 : fetch_word Ubsan.M.loaded_segments (0x28900 : word) = Some W_28900.
Proof. vm_refl. Qed.
Lemma D_28900 : decode_any W_28900 = Some (Jal 0 7848, 4%Z).
Proof. vm_refl. Qed.

Definition W_28904 : bv 32 := 0x05813603.
Lemma F_28904 : fetch_word Ubsan.M.loaded_segments (0x28904 : word) = Some W_28904.
Proof. vm_refl. Qed.
Lemma D_28904 : decode_any W_28904 = Some (Load SZ8 true 12 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28908 : bv 32 := 0x02560833.
Lemma F_28908 : fetch_word Ubsan.M.loaded_segments (0x28908 : word) = Some W_28908.
Proof. vm_refl. Qed.
Lemma D_28908 : decode_any W_28908 = Some (Mul M_MUL 16 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2890c : bv 32 := 0x0256063b.
Lemma F_2890c : fetch_word Ubsan.M.loaded_segments (0x2890c : word) = Some W_2890c.
Proof. vm_refl. Qed.
Lemma D_2890c : decode_any W_2890c = Some (Mul32 M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28910 : bv 32 := 0x01060463.
Lemma F_28910 : fetch_word Ubsan.M.loaded_segments (0x28910 : word) = Some W_28910.
Proof. vm_refl. Qed.
Lemma D_28910 : decode_any W_28910 = Some (Branch BC_EQ 12 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28914 : bv 32 := 0x6950106f.
Lemma F_28914 : fetch_word Ubsan.M.loaded_segments (0x28914 : word) = Some W_28914.
Proof. vm_refl. Qed.
Lemma D_28914 : decode_any W_28914 = Some (Jal 0 7828, 4%Z).
Proof. vm_refl. Qed.

Definition W_28918 : bv 32 := 0x0008081b.
Lemma F_28918 : fetch_word Ubsan.M.loaded_segments (0x28918 : word) = Some W_28918.
Proof. vm_refl. Qed.
Lemma D_28918 : decode_any W_28918 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2891c : bv 32 := 0x00281793.
Lemma F_2891c : fetch_word Ubsan.M.loaded_segments (0x2891c : word) = Some W_2891c.
Proof. vm_refl. Qed.
Lemma D_2891c : decode_any W_2891c = Some (ShiftImm ALU_SLL 15 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28920 : bv 32 := 0x013787b3.
Lemma F_28920 : fetch_word Ubsan.M.loaded_segments (0x28920 : word) = Some W_28920.
Proof. vm_refl. Qed.
Lemma D_28920 : decode_any W_28920 = Some (Op ALU_ADD 15 15 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28924 : bv 32 := 0x01303633.
Lemma F_28924 : fetch_word Ubsan.M.loaded_segments (0x28924 : word) = Some W_28924.
Proof. vm_refl. Qed.
Lemma D_28924 : decode_any W_28924 = Some (Op ALU_SLTU 12 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28928 : bv 32 := 0x0017b893.
Lemma F_28928 : fetch_word Ubsan.M.loaded_segments (0x28928 : word) = Some W_28928.
Proof. vm_refl. Qed.
Lemma D_28928 : decode_any W_28928 = Some (OpImm ALU_SLTU 17 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2892c : bv 32 := 0x01161463.
Lemma F_2892c : fetch_word Ubsan.M.loaded_segments (0x2892c : word) = Some W_2892c.
Proof. vm_refl. Qed.
Lemma D_2892c : decode_any W_2892c = Some (Branch BC_NE 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28930 : bv 32 := 0x6790106f.
Lemma F_28930 : fetch_word Ubsan.M.loaded_segments (0x28930 : word) = Some W_28930.
Proof. vm_refl. Qed.
Lemma D_28930 : decode_any W_28930 = Some (Jal 0 7800, 4%Z).
Proof. vm_refl. Qed.

Definition W_28934 : bv 32 := 0x0137b8b3.
Lemma F_28934 : fetch_word Ubsan.M.loaded_segments (0x28934 : word) = Some W_28934.
Proof. vm_refl. Qed.
Lemma D_28934 : decode_any W_28934 = Some (Op ALU_SLTU 17 15 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28938 : bv 32 := 0x00082813.
Lemma F_28938 : fetch_word Ubsan.M.loaded_segments (0x28938 : word) = Some W_28938.
Proof. vm_refl. Qed.
Lemma D_28938 : decode_any W_28938 = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2893c : bv 32 := 0x0108c833.
Lemma F_2893c : fetch_word Ubsan.M.loaded_segments (0x2893c : word) = Some W_2893c.
Proof. vm_refl. Qed.
Lemma D_2893c : decode_any W_2893c = Some (Op ALU_XOR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28940 : bv 32 := 0x00184813.
Lemma F_28940 : fetch_word Ubsan.M.loaded_segments (0x28940 : word) = Some W_28940.
Proof. vm_refl. Qed.
Lemma D_28940 : decode_any W_28940 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28944 : bv 32 := 0x00081463.
Lemma F_28944 : fetch_word Ubsan.M.loaded_segments (0x28944 : word) = Some W_28944.
Proof. vm_refl. Qed.
Lemma D_28944 : decode_any W_28944 = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28948 : bv 32 := 0x6610106f.
Lemma F_28948 : fetch_word Ubsan.M.loaded_segments (0x28948 : word) = Some W_28948.
Proof. vm_refl. Qed.
Lemma D_28948 : decode_any W_28948 = Some (Jal 0 7776, 4%Z).
Proof. vm_refl. Qed.

Definition W_2894c : bv 32 := 0x005dd81b.
Lemma F_2894c : fetch_word Ubsan.M.loaded_segments (0x2894c : word) = Some W_2894c.
Proof. vm_refl. Qed.
Lemma D_2894c : decode_any W_2894c = Some (ShiftImm32 ALU_SRL 16 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28950 : bv 32 := 0x00281813.
Lemma F_28950 : fetch_word Ubsan.M.loaded_segments (0x28950 : word) = Some W_28950.
Proof. vm_refl. Qed.
Lemma D_28950 : decode_any W_28950 = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28954 : bv 32 := 0x00f80933.
Lemma F_28954 : fetch_word Ubsan.M.loaded_segments (0x28954 : word) = Some W_28954.
Proof. vm_refl. Qed.
Lemma D_28954 : decode_any W_28954 = Some (Op ALU_ADD 18 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28958 : bv 32 := 0x00f97463.
Lemma F_28958 : fetch_word Ubsan.M.loaded_segments (0x28958 : word) = Some W_28958.
Proof. vm_refl. Qed.
Lemma D_28958 : decode_any W_28958 = Some (Branch BC_GEU 18 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2895c : bv 32 := 0x64d0106f.
Lemma F_2895c : fetch_word Ubsan.M.loaded_segments (0x2895c : word) = Some W_2895c.
Proof. vm_refl. Qed.
Lemma D_2895c : decode_any W_2895c = Some (Jal 0 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_28960 : bv 32 := 0x00193793.
Lemma F_28960 : fetch_word Ubsan.M.loaded_segments (0x28960 : word) = Some W_28960.
Proof. vm_refl. Qed.
Lemma D_28960 : decode_any W_28960 = Some (OpImm ALU_SLTU 15 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28964 : bv 32 := 0x00f64633.
Lemma F_28964 : fetch_word Ubsan.M.loaded_segments (0x28964 : word) = Some W_28964.
Proof. vm_refl. Qed.
Lemma D_28964 : decode_any W_28964 = Some (Op ALU_XOR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28968 : bv 32 := 0x00061463.
Lemma F_28968 : fetch_word Ubsan.M.loaded_segments (0x28968 : word) = Some W_28968.
Proof. vm_refl. Qed.
Lemma D_28968 : decode_any W_28968 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2896c : bv 32 := 0x63d0106f.
Lemma F_2896c : fetch_word Ubsan.M.loaded_segments (0x2896c : word) = Some W_2896c.
Proof. vm_refl. Qed.
Lemma D_2896c : decode_any W_2896c = Some (Jal 0 7740, 4%Z).
Proof. vm_refl. Qed.

Definition W_28970 : bv 32 := 0x00000b93.
Lemma F_28970 : fetch_word Ubsan.M.loaded_segments (0x28970 : word) = Some W_28970.
Proof. vm_refl. Qed.
Lemma D_28970 : decode_any W_28970 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28974 : bv 32 := 0x00000a13.
Lemma F_28974 : fetch_word Ubsan.M.loaded_segments (0x28974 : word) = Some W_28974.
Proof. vm_refl. Qed.
Lemma D_28974 : decode_any W_28974 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28978 : bv 32 := 0x00000a93.
Lemma F_28978 : fetch_word Ubsan.M.loaded_segments (0x28978 : word) = Some W_28978.
Proof. vm_refl. Qed.
Lemma D_28978 : decode_any W_28978 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2897c : bv 32 := 0x1640006f.
Lemma F_2897c : fetch_word Ubsan.M.loaded_segments (0x2897c : word) = Some W_2897c.
Proof. vm_refl. Qed.
Lemma D_2897c : decode_any W_2897c = Some (Jal 0 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_28980 : bv 32 := 0x00000793.
Lemma F_28980 : fetch_word Ubsan.M.loaded_segments (0x28980 : word) = Some W_28980.
Proof. vm_refl. Qed.
Lemma D_28980 : decode_any W_28980 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28984 : bv 32 := 0x00000c93.
Lemma F_28984 : fetch_word Ubsan.M.loaded_segments (0x28984 : word) = Some W_28984.
Proof. vm_refl. Qed.
Lemma D_28984 : decode_any W_28984 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28988 : bv 32 := 0x00000a93.
Lemma F_28988 : fetch_word Ubsan.M.loaded_segments (0x28988 : word) = Some W_28988.
Proof. vm_refl. Qed.
Lemma D_28988 : decode_any W_28988 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2898c : bv 32 := 0x00000d93.
Lemma F_2898c : fetch_word Ubsan.M.loaded_segments (0x2898c : word) = Some W_2898c.
Proof. vm_refl. Qed.
Lemma D_2898c : decode_any W_2898c = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28990 : bv 32 := 0x4154063b.
Lemma F_28990 : fetch_word Ubsan.M.loaded_segments (0x28990 : word) = Some W_28990.
Proof. vm_refl. Qed.
Lemma D_28990 : decode_any W_28990 = Some (Op32 ALU_SUB 12 8 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_28994 : bv 32 := 0x0056561b.
Lemma F_28994 : fetch_word Ubsan.M.loaded_segments (0x28994 : word) = Some W_28994.
Proof. vm_refl. Qed.
Lemma D_28994 : decode_any W_28994 = Some (ShiftImm32 ALU_SRL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28998 : bv 32 := 0x06c13823.
Lemma F_28998 : fetch_word Ubsan.M.loaded_segments (0x28998 : word) = Some W_28998.
Proof. vm_refl. Qed.
Lemma D_28998 : decode_any W_28998 = Some (Store SZ8 2 12 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_2899c : bv 32 := 0x14060863.
Lemma F_2899c : fetch_word Ubsan.M.loaded_segments (0x2899c : word) = Some W_2899c.
Proof. vm_refl. Qed.
Lemma D_2899c : decode_any W_2899c = Some (Branch BC_EQ 12 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_289a0 : bv 32 := 0x02770633.
Lemma F_289a0 : fetch_word Ubsan.M.loaded_segments (0x289a0 : word) = Some W_289a0.
Proof. vm_refl. Qed.
Lemma D_289a0 : decode_any W_289a0 = Some (Mul M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_289a4 : bv 32 := 0x0277083b.
Lemma F_289a4 : fetch_word Ubsan.M.loaded_segments (0x289a4 : word) = Some W_289a4.
Proof. vm_refl. Qed.
Lemma D_289a4 : decode_any W_289a4 = Some (Mul32 M_MUL 16 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_289a8 : bv 32 := 0x00c80463.
Lemma F_289a8 : fetch_word Ubsan.M.loaded_segments (0x289a8 : word) = Some W_289a8.
Proof. vm_refl. Qed.
Lemma D_289a8 : decode_any W_289a8 = Some (Branch BC_EQ 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_289ac : bv 32 := 0x5fd0106f.
Lemma F_289ac : fetch_word Ubsan.M.loaded_segments (0x289ac : word) = Some W_289ac.
Proof. vm_refl. Qed.
Lemma D_289ac : decode_any W_289ac = Some (Jal 0 7676, 4%Z).
Proof. vm_refl. Qed.

Definition W_289b0 : bv 32 := 0x0006061b.
Lemma F_289b0 : fetch_word Ubsan.M.loaded_segments (0x289b0 : word) = Some W_289b0.
Proof. vm_refl. Qed.
Lemma D_289b0 : decode_any W_289b0 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_289b4 : bv 32 := 0x00261813.
Lemma F_289b4 : fetch_word Ubsan.M.loaded_segments (0x289b4 : word) = Some W_289b4.
Proof. vm_refl. Qed.
Lemma D_289b4 : decode_any W_289b4 = Some (ShiftImm ALU_SLL 16 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_289b8 : bv 32 := 0x01050833.
Lemma F_289b8 : fetch_word Ubsan.M.loaded_segments (0x289b8 : word) = Some W_289b8.
Proof. vm_refl. Qed.
Lemma D_289b8 : decode_any W_289b8 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_289bc : bv 32 := 0x00a03333.
Lemma F_289bc : fetch_word Ubsan.M.loaded_segments (0x289bc : word) = Some W_289bc.
Proof. vm_refl. Qed.
Lemma D_289bc : decode_any W_289bc = Some (Op ALU_SLTU 6 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_289c0 : bv 32 := 0x00183893.
Lemma F_289c0 : fetch_word Ubsan.M.loaded_segments (0x289c0 : word) = Some W_289c0.
Proof. vm_refl. Qed.
Lemma D_289c0 : decode_any W_289c0 = Some (OpImm ALU_SLTU 17 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_289c4 : bv 32 := 0x01131463.
Lemma F_289c4 : fetch_word Ubsan.M.loaded_segments (0x289c4 : word) = Some W_289c4.
Proof. vm_refl. Qed.
Lemma D_289c4 : decode_any W_289c4 = Some (Branch BC_NE 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_289c8 : bv 32 := 0x5e10106f.
Lemma F_289c8 : fetch_word Ubsan.M.loaded_segments (0x289c8 : word) = Some W_289c8.
Proof. vm_refl. Qed.
Lemma D_289c8 : decode_any W_289c8 = Some (Jal 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_289cc : bv 32 := 0x00a838b3.
Lemma F_289cc : fetch_word Ubsan.M.loaded_segments (0x289cc : word) = Some W_289cc.
Proof. vm_refl. Qed.
Lemma D_289cc : decode_any W_289cc = Some (Op ALU_SLTU 17 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_289d0 : bv 32 := 0x00062613.
Lemma F_289d0 : fetch_word Ubsan.M.loaded_segments (0x289d0 : word) = Some W_289d0.
Proof. vm_refl. Qed.
Lemma D_289d0 : decode_any W_289d0 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_289d4 : bv 32 := 0x00c8c633.
Lemma F_289d4 : fetch_word Ubsan.M.loaded_segments (0x289d4 : word) = Some W_289d4.
Proof. vm_refl. Qed.
Lemma D_289d4 : decode_any W_289d4 = Some (Op ALU_XOR 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_289d8 : bv 32 := 0x00164613.
Lemma F_289d8 : fetch_word Ubsan.M.loaded_segments (0x289d8 : word) = Some W_289d8.
Proof. vm_refl. Qed.
Lemma D_289d8 : decode_any W_289d8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_289dc : bv 32 := 0x00061463.
Lemma F_289dc : fetch_word Ubsan.M.loaded_segments (0x289dc : word) = Some W_289dc.
Proof. vm_refl. Qed.
Lemma D_289dc : decode_any W_289dc = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_289e0 : bv 32 := 0x5c90106f.
Lemma F_289e0 : fetch_word Ubsan.M.loaded_segments (0x289e0 : word) = Some W_289e0.
Proof. vm_refl. Qed.
Lemma D_289e0 : decode_any W_289e0 = Some (Jal 0 7624, 4%Z).
Proof. vm_refl. Qed.

Definition W_289e4 : bv 32 := 0x000b861b.
Lemma F_289e4 : fetch_word Ubsan.M.loaded_segments (0x289e4 : word) = Some W_289e4.
Proof. vm_refl. Qed.
Lemma D_289e4 : decode_any W_289e4 = Some (OpImm32 12 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_289e8 : bv 32 := 0x00c688b3.
Lemma F_289e8 : fetch_word Ubsan.M.loaded_segments (0x289e8 : word) = Some W_289e8.
Proof. vm_refl. Qed.
Lemma D_289e8 : decode_any W_289e8 = Some (Op ALU_ADD 17 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_289ec : bv 32 := 0x00c68e3b.
Lemma F_289ec : fetch_word Ubsan.M.loaded_segments (0x289ec : word) = Some W_289ec.
Proof. vm_refl. Qed.
Lemma D_289ec : decode_any W_289ec = Some (Op32 ALU_ADD 28 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_289f0 : bv 32 := 0x011e0463.
Lemma F_289f0 : fetch_word Ubsan.M.loaded_segments (0x289f0 : word) = Some W_289f0.
Proof. vm_refl. Qed.
Lemma D_289f0 : decode_any W_289f0 = Some (Branch BC_EQ 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_289f4 : bv 32 := 0x5b50106f.
Lemma F_289f4 : fetch_word Ubsan.M.loaded_segments (0x289f4 : word) = Some W_289f4.
Proof. vm_refl. Qed.
Lemma D_289f4 : decode_any W_289f4 = Some (Jal 0 7604, 4%Z).
Proof. vm_refl. Qed.

Definition W_289f8 : bv 32 := 0x4058de1b.
Lemma F_289f8 : fetch_word Ubsan.M.loaded_segments (0x289f8 : word) = Some W_289f8.
Proof. vm_refl. Qed.
Lemma D_289f8 : decode_any W_289f8 = Some (ShiftImm32 ALU_SRA 28 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_289fc : bv 32 := 0x002e1893.
Lemma F_289fc : fetch_word Ubsan.M.loaded_segments (0x289fc : word) = Some W_289fc.
Proof. vm_refl. Qed.
Lemma D_289fc : decode_any W_289fc = Some (ShiftImm ALU_SLL 17 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a00 : bv 32 := 0x01180933.
Lemma F_28a00 : fetch_word Ubsan.M.loaded_segments (0x28a00 : word) = Some W_28a00.
Proof. vm_refl. Qed.
Lemma D_28a00 : decode_any W_28a00 = Some (Op ALU_ADD 18 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a04 : bv 32 := 0x00193413.
Lemma F_28a04 : fetch_word Ubsan.M.loaded_segments (0x28a04 : word) = Some W_28a04.
Proof. vm_refl. Qed.
Lemma D_28a04 : decode_any W_28a04 = Some (OpImm ALU_SLTU 8 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a08 : bv 32 := 0x00831463.
Lemma F_28a08 : fetch_word Ubsan.M.loaded_segments (0x28a08 : word) = Some W_28a08.
Proof. vm_refl. Qed.
Lemma D_28a08 : decode_any W_28a08 = Some (Branch BC_NE 6 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a0c : bv 32 := 0x59d0106f.
Lemma F_28a0c : fetch_word Ubsan.M.loaded_segments (0x28a0c : word) = Some W_28a0c.
Proof. vm_refl. Qed.
Lemma D_28a0c : decode_any W_28a0c = Some (Jal 0 7580, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a10 : bv 32 := 0x01093833.
Lemma F_28a10 : fetch_word Ubsan.M.loaded_segments (0x28a10 : word) = Some W_28a10.
Proof. vm_refl. Qed.
Lemma D_28a10 : decode_any W_28a10 = Some (Op ALU_SLTU 16 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a14 : bv 32 := 0x000e2313.
Lemma F_28a14 : fetch_word Ubsan.M.loaded_segments (0x28a14 : word) = Some W_28a14.
Proof. vm_refl. Qed.
Lemma D_28a14 : decode_any W_28a14 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a18 : bv 32 := 0x00684833.
Lemma F_28a18 : fetch_word Ubsan.M.loaded_segments (0x28a18 : word) = Some W_28a18.
Proof. vm_refl. Qed.
Lemma D_28a18 : decode_any W_28a18 = Some (Op ALU_XOR 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a1c : bv 32 := 0x00184813.
Lemma F_28a1c : fetch_word Ubsan.M.loaded_segments (0x28a1c : word) = Some W_28a1c.
Proof. vm_refl. Qed.
Lemma D_28a1c : decode_any W_28a1c = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a20 : bv 32 := 0x00081463.
Lemma F_28a20 : fetch_word Ubsan.M.loaded_segments (0x28a20 : word) = Some W_28a20.
Proof. vm_refl. Qed.
Lemma D_28a20 : decode_any W_28a20 = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a24 : bv 32 := 0x5850106f.
Lemma F_28a24 : fetch_word Ubsan.M.loaded_segments (0x28a24 : word) = Some W_28a24.
Proof. vm_refl. Qed.
Lemma D_28a24 : decode_any W_28a24 = Some (Jal 0 7556, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a28 : bv 32 := 0x05813803.
Lemma F_28a28 : fetch_word Ubsan.M.loaded_segments (0x28a28 : word) = Some W_28a28.
Proof. vm_refl. Qed.
Lemma D_28a28 : decode_any W_28a28 = Some (Load SZ8 true 16 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a2c : bv 32 := 0x02580333.
Lemma F_28a2c : fetch_word Ubsan.M.loaded_segments (0x28a2c : word) = Some W_28a2c.
Proof. vm_refl. Qed.
Lemma D_28a2c : decode_any W_28a2c = Some (Mul M_MUL 6 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a30 : bv 32 := 0x0258083b.
Lemma F_28a30 : fetch_word Ubsan.M.loaded_segments (0x28a30 : word) = Some W_28a30.
Proof. vm_refl. Qed.
Lemma D_28a30 : decode_any W_28a30 = Some (Mul32 M_MUL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a34 : bv 32 := 0x00680463.
Lemma F_28a34 : fetch_word Ubsan.M.loaded_segments (0x28a34 : word) = Some W_28a34.
Proof. vm_refl. Qed.
Lemma D_28a34 : decode_any W_28a34 = Some (Branch BC_EQ 16 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a38 : bv 32 := 0x5710106f.
Lemma F_28a38 : fetch_word Ubsan.M.loaded_segments (0x28a38 : word) = Some W_28a38.
Proof. vm_refl. Qed.
Lemma D_28a38 : decode_any W_28a38 = Some (Jal 0 7536, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a3c : bv 32 := 0x0003031b.
Lemma F_28a3c : fetch_word Ubsan.M.loaded_segments (0x28a3c : word) = Some W_28a3c.
Proof. vm_refl. Qed.
Lemma D_28a3c : decode_any W_28a3c = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a40 : bv 32 := 0x00231813.
Lemma F_28a40 : fetch_word Ubsan.M.loaded_segments (0x28a40 : word) = Some W_28a40.
Proof. vm_refl. Qed.
Lemma D_28a40 : decode_any W_28a40 = Some (ShiftImm ALU_SLL 16 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a44 : bv 32 := 0x01098833.
Lemma F_28a44 : fetch_word Ubsan.M.loaded_segments (0x28a44 : word) = Some W_28a44.
Proof. vm_refl. Qed.
Lemma D_28a44 : decode_any W_28a44 = Some (Op ALU_ADD 16 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a48 : bv 32 := 0x01303e33.
Lemma F_28a48 : fetch_word Ubsan.M.loaded_segments (0x28a48 : word) = Some W_28a48.
Proof. vm_refl. Qed.
Lemma D_28a48 : decode_any W_28a48 = Some (Op ALU_SLTU 28 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a4c : bv 32 := 0x00183413.
Lemma F_28a4c : fetch_word Ubsan.M.loaded_segments (0x28a4c : word) = Some W_28a4c.
Proof. vm_refl. Qed.
Lemma D_28a4c : decode_any W_28a4c = Some (OpImm ALU_SLTU 8 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a50 : bv 32 := 0x008e1463.
Lemma F_28a50 : fetch_word Ubsan.M.loaded_segments (0x28a50 : word) = Some W_28a50.
Proof. vm_refl. Qed.
Lemma D_28a50 : decode_any W_28a50 = Some (Branch BC_NE 28 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a54 : bv 32 := 0x5550106f.
Lemma F_28a54 : fetch_word Ubsan.M.loaded_segments (0x28a54 : word) = Some W_28a54.
Proof. vm_refl. Qed.
Lemma D_28a54 : decode_any W_28a54 = Some (Jal 0 7508, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a58 : bv 32 := 0x01383433.
Lemma F_28a58 : fetch_word Ubsan.M.loaded_segments (0x28a58 : word) = Some W_28a58.
Proof. vm_refl. Qed.
Lemma D_28a58 : decode_any W_28a58 = Some (Op ALU_SLTU 8 16 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a5c : bv 32 := 0x00032313.
Lemma F_28a5c : fetch_word Ubsan.M.loaded_segments (0x28a5c : word) = Some W_28a5c.
Proof. vm_refl. Qed.
Lemma D_28a5c : decode_any W_28a5c = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a60 : bv 32 := 0x00644333.
Lemma F_28a60 : fetch_word Ubsan.M.loaded_segments (0x28a60 : word) = Some W_28a60.
Proof. vm_refl. Qed.
Lemma D_28a60 : decode_any W_28a60 = Some (Op ALU_XOR 6 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a64 : bv 32 := 0x00134313.
Lemma F_28a64 : fetch_word Ubsan.M.loaded_segments (0x28a64 : word) = Some W_28a64.
Proof. vm_refl. Qed.
Lemma D_28a64 : decode_any W_28a64 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a68 : bv 32 := 0x00031463.
Lemma F_28a68 : fetch_word Ubsan.M.loaded_segments (0x28a68 : word) = Some W_28a68.
Proof. vm_refl. Qed.
Lemma D_28a68 : decode_any W_28a68 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a6c : bv 32 := 0x53d0106f.
Lemma F_28a6c : fetch_word Ubsan.M.loaded_segments (0x28a6c : word) = Some W_28a6c.
Proof. vm_refl. Qed.
Lemma D_28a6c : decode_any W_28a6c = Some (Jal 0 7484, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a70 : bv 32 := 0x00cc0333.
Lemma F_28a70 : fetch_word Ubsan.M.loaded_segments (0x28a70 : word) = Some W_28a70.
Proof. vm_refl. Qed.
Lemma D_28a70 : decode_any W_28a70 = Some (Op ALU_ADD 6 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a74 : bv 32 := 0x00cc063b.
Lemma F_28a74 : fetch_word Ubsan.M.loaded_segments (0x28a74 : word) = Some W_28a74.
Proof. vm_refl. Qed.
Lemma D_28a74 : decode_any W_28a74 = Some (Op32 ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a78 : bv 32 := 0x00660463.
Lemma F_28a78 : fetch_word Ubsan.M.loaded_segments (0x28a78 : word) = Some W_28a78.
Proof. vm_refl. Qed.
Lemma D_28a78 : decode_any W_28a78 = Some (Branch BC_EQ 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a7c : bv 32 := 0x52d0106f.
Lemma F_28a7c : fetch_word Ubsan.M.loaded_segments (0x28a7c : word) = Some W_28a7c.
Proof. vm_refl. Qed.
Lemma D_28a7c : decode_any W_28a7c = Some (Jal 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a80 : bv 32 := 0x4053561b.
Lemma F_28a80 : fetch_word Ubsan.M.loaded_segments (0x28a80 : word) = Some W_28a80.
Proof. vm_refl. Qed.
Lemma D_28a80 : decode_any W_28a80 = Some (ShiftImm32 ALU_SRA 12 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a84 : bv 32 := 0x00261313.
Lemma F_28a84 : fetch_word Ubsan.M.loaded_segments (0x28a84 : word) = Some W_28a84.
Proof. vm_refl. Qed.
Lemma D_28a84 : decode_any W_28a84 = Some (ShiftImm ALU_SLL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a88 : bv 32 := 0x01030333.
Lemma F_28a88 : fetch_word Ubsan.M.loaded_segments (0x28a88 : word) = Some W_28a88.
Proof. vm_refl. Qed.
Lemma D_28a88 : decode_any W_28a88 = Some (Op ALU_ADD 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a8c : bv 32 := 0x00133413.
Lemma F_28a8c : fetch_word Ubsan.M.loaded_segments (0x28a8c : word) = Some W_28a8c.
Proof. vm_refl. Qed.
Lemma D_28a8c : decode_any W_28a8c = Some (OpImm ALU_SLTU 8 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a90 : bv 32 := 0x008e1463.
Lemma F_28a90 : fetch_word Ubsan.M.loaded_segments (0x28a90 : word) = Some W_28a90.
Proof. vm_refl. Qed.
Lemma D_28a90 : decode_any W_28a90 = Some (Branch BC_NE 28 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a94 : bv 32 := 0x5150106f.
Lemma F_28a94 : fetch_word Ubsan.M.loaded_segments (0x28a94 : word) = Some W_28a94.
Proof. vm_refl. Qed.
Lemma D_28a94 : decode_any W_28a94 = Some (Jal 0 7444, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a98 : bv 32 := 0x01033833.
Lemma F_28a98 : fetch_word Ubsan.M.loaded_segments (0x28a98 : word) = Some W_28a98.
Proof. vm_refl. Qed.
Lemma D_28a98 : decode_any W_28a98 = Some (Op ALU_SLTU 16 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28a9c : bv 32 := 0x00062613.
Lemma F_28a9c : fetch_word Ubsan.M.loaded_segments (0x28a9c : word) = Some W_28a9c.
Proof. vm_refl. Qed.
Lemma D_28a9c : decode_any W_28a9c = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28aa0 : bv 32 := 0x00c84633.
Lemma F_28aa0 : fetch_word Ubsan.M.loaded_segments (0x28aa0 : word) = Some W_28aa0.
Proof. vm_refl. Qed.
Lemma D_28aa0 : decode_any W_28aa0 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28aa4 : bv 32 := 0x00164613.
Lemma F_28aa4 : fetch_word Ubsan.M.loaded_segments (0x28aa4 : word) = Some W_28aa4.
Proof. vm_refl. Qed.
Lemma D_28aa4 : decode_any W_28aa4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28aa8 : bv 32 := 0x00061463.
Lemma F_28aa8 : fetch_word Ubsan.M.loaded_segments (0x28aa8 : word) = Some W_28aa8.
Proof. vm_refl. Qed.
Lemma D_28aa8 : decode_any W_28aa8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28aac : bv 32 := 0x4fd0106f.
Lemma F_28aac : fetch_word Ubsan.M.loaded_segments (0x28aac : word) = Some W_28aac.
Proof. vm_refl. Qed.
Lemma D_28aac : decode_any W_28aac = Some (Jal 0 7420, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ab0 : bv 32 := 0x00000813.
Lemma F_28ab0 : fetch_word Ubsan.M.loaded_segments (0x28ab0 : word) = Some W_28ab0.
Proof. vm_refl. Qed.
Lemma D_28ab0 : decode_any W_28ab0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ab4 : bv 32 := 0x02013023.
Lemma F_28ab4 : fetch_word Ubsan.M.loaded_segments (0x28ab4 : word) = Some W_28ab4.
Proof. vm_refl. Qed.
Lemma D_28ab4 : decode_any W_28ab4 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ab8 : bv 32 := 0x04c0006f.
Lemma F_28ab8 : fetch_word Ubsan.M.loaded_segments (0x28ab8 : word) = Some W_28ab8.
Proof. vm_refl. Qed.
Lemma D_28ab8 : decode_any W_28ab8 = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_28abc : bv 32 := 0x00545f9b.
Lemma F_28abc : fetch_word Ubsan.M.loaded_segments (0x28abc : word) = Some W_28abc.
Proof. vm_refl. Qed.
Lemma D_28abc : decode_any W_28abc = Some (ShiftImm32 ALU_SRL 31 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ac0 : bv 32 := 0x6c0f8263.
Lemma F_28ac0 : fetch_word Ubsan.M.loaded_segments (0x28ac0 : word) = Some W_28ac0.
Proof. vm_refl. Qed.
Lemma D_28ac0 : decode_any W_28ac0 = Some (Branch BC_EQ 31 0 1732, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ac4 : bv 32 := 0x004a0413.
Lemma F_28ac4 : fetch_word Ubsan.M.loaded_segments (0x28ac4 : word) = Some W_28ac4.
Proof. vm_refl. Qed.
Lemma D_28ac4 : decode_any W_28ac4 = Some (OpImm ALU_ADD 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ac8 : bv 32 := 0x00500613.
Lemma F_28ac8 : fetch_word Ubsan.M.loaded_segments (0x28ac8 : word) = Some W_28ac8.
Proof. vm_refl. Qed.
Lemma D_28ac8 : decode_any W_28ac8 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28acc : bv 32 := 0x00c47463.
Lemma F_28acc : fetch_word Ubsan.M.loaded_segments (0x28acc : word) = Some W_28acc.
Proof. vm_refl. Qed.
Lemma D_28acc : decode_any W_28acc = Some (Branch BC_GEU 8 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ad0 : bv 32 := 0x4d90106f.
Lemma F_28ad0 : fetch_word Ubsan.M.loaded_segments (0x28ad0 : word) = Some W_28ad0.
Proof. vm_refl. Qed.
Lemma D_28ad0 : decode_any W_28ad0 = Some (Jal 0 7384, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ad4 : bv 32 := 0x004a8913.
Lemma F_28ad4 : fetch_word Ubsan.M.loaded_segments (0x28ad4 : word) = Some W_28ad4.
Proof. vm_refl. Qed.
Lemma D_28ad4 : decode_any W_28ad4 = Some (OpImm ALU_ADD 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ad8 : bv 32 := 0x00c97463.
Lemma F_28ad8 : fetch_word Ubsan.M.loaded_segments (0x28ad8 : word) = Some W_28ad8.
Proof. vm_refl. Qed.
Lemma D_28ad8 : decode_any W_28ad8 = Some (Branch BC_GEU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28adc : bv 32 := 0x4cd0106f.
Lemma F_28adc : fetch_word Ubsan.M.loaded_segments (0x28adc : word) = Some W_28adc.
Proof. vm_refl. Qed.
Lemma D_28adc : decode_any W_28adc = Some (Jal 0 7372, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ae0 : bv 32 := 0x00000613.
Lemma F_28ae0 : fetch_word Ubsan.M.loaded_segments (0x28ae0 : word) = Some W_28ae0.
Proof. vm_refl. Qed.
Lemma D_28ae0 : decode_any W_28ae0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ae4 : bv 32 := 0x00000b13.
Lemma F_28ae4 : fetch_word Ubsan.M.loaded_segments (0x28ae4 : word) = Some W_28ae4.
Proof. vm_refl. Qed.
Lemma D_28ae4 : decode_any W_28ae4 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ae8 : bv 32 := 0x6ac0006f.
Lemma F_28ae8 : fetch_word Ubsan.M.loaded_segments (0x28ae8 : word) = Some W_28ae8.
Proof. vm_refl. Qed.
Lemma D_28ae8 : decode_any W_28ae8 = Some (Jal 0 1708, 4%Z).
Proof. vm_refl. Qed.

Definition W_28aec : bv 32 := 0x00000813.
Lemma F_28aec : fetch_word Ubsan.M.loaded_segments (0x28aec : word) = Some W_28aec.
Proof. vm_refl. Qed.
Lemma D_28aec : decode_any W_28aec = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28af0 : bv 32 := 0x06013823.
Lemma F_28af0 : fetch_word Ubsan.M.loaded_segments (0x28af0 : word) = Some W_28af0.
Proof. vm_refl. Qed.
Lemma D_28af0 : decode_any W_28af0 = Some (Store SZ8 2 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_28af4 : bv 32 := 0x00000913.
Lemma F_28af4 : fetch_word Ubsan.M.loaded_segments (0x28af4 : word) = Some W_28af4.
Proof. vm_refl. Qed.
Lemma D_28af4 : decode_any W_28af4 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28af8 : bv 32 := 0x00000313.
Lemma F_28af8 : fetch_word Ubsan.M.loaded_segments (0x28af8 : word) = Some W_28af8.
Proof. vm_refl. Qed.
Lemma D_28af8 : decode_any W_28af8 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28afc : bv 32 := 0x00100613.
Lemma F_28afc : fetch_word Ubsan.M.loaded_segments (0x28afc : word) = Some W_28afc.
Proof. vm_refl. Qed.
Lemma D_28afc : decode_any W_28afc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b00 : bv 32 := 0x02c13023.
Lemma F_28b00 : fetch_word Ubsan.M.loaded_segments (0x28b00 : word) = Some W_28b00.
Proof. vm_refl. Qed.
Lemma D_28b00 : decode_any W_28b00 = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b04 : bv 32 := 0x00968633.
Lemma F_28b04 : fetch_word Ubsan.M.loaded_segments (0x28b04 : word) = Some W_28b04.
Proof. vm_refl. Qed.
Lemma D_28b04 : decode_any W_28b04 = Some (Op ALU_ADD 12 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b08 : bv 32 := 0x009684bb.
Lemma F_28b08 : fetch_word Ubsan.M.loaded_segments (0x28b08 : word) = Some W_28b08.
Proof. vm_refl. Qed.
Lemma D_28b08 : decode_any W_28b08 = Some (Op32 ALU_ADD 9 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b0c : bv 32 := 0x00c48463.
Lemma F_28b0c : fetch_word Ubsan.M.loaded_segments (0x28b0c : word) = Some W_28b0c.
Proof. vm_refl. Qed.
Lemma D_28b0c : decode_any W_28b0c = Some (Branch BC_EQ 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b10 : bv 32 := 0x4990106f.
Lemma F_28b10 : fetch_word Ubsan.M.loaded_segments (0x28b10 : word) = Some W_28b10.
Proof. vm_refl. Qed.
Lemma D_28b10 : decode_any W_28b10 = Some (Jal 0 7320, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b14 : bv 32 := 0x01f67b13.
Lemma F_28b14 : fetch_word Ubsan.M.loaded_segments (0x28b14 : word) = Some W_28b14.
Proof. vm_refl. Qed.
Lemma D_28b14 : decode_any W_28b14 = Some (OpImm ALU_AND 22 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b18 : bv 32 := 0x001b3613.
Lemma F_28b18 : fetch_word Ubsan.M.loaded_segments (0x28b18 : word) = Some W_28b18.
Proof. vm_refl. Qed.
Lemma D_28b18 : decode_any W_28b18 = Some (OpImm ALU_SLTU 12 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b1c : bv 32 := 0x01066633.
Lemma F_28b1c : fetch_word Ubsan.M.loaded_segments (0x28b1c : word) = Some W_28b1c.
Proof. vm_refl. Qed.
Lemma D_28b1c : decode_any W_28b1c = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b20 : bv 32 := 0x41da043b.
Lemma F_28b20 : fetch_word Ubsan.M.loaded_segments (0x28b20 : word) = Some W_28b20.
Proof. vm_refl. Qed.
Lemma D_28b20 : decode_any W_28b20 = Some (Op32 ALU_SUB 8 20 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b24 : bv 32 := 0x00c13c23.
Lemma F_28b24 : fetch_word Ubsan.M.loaded_segments (0x28b24 : word) = Some W_28b24.
Proof. vm_refl. Qed.
Lemma D_28b24 : decode_any W_28b24 = Some (Store SZ8 2 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b28 : bv 32 := 0x00060863.
Lemma F_28b28 : fetch_word Ubsan.M.loaded_segments (0x28b28 : word) = Some W_28b28.
Proof. vm_refl. Qed.
Lemma D_28b28 : decode_any W_28b28 = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b2c : bv 32 := 0x00000513.
Lemma F_28b2c : fetch_word Ubsan.M.loaded_segments (0x28b2c : word) = Some W_28b2c.
Proof. vm_refl. Qed.
Lemma D_28b2c : decode_any W_28b2c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b30 : bv 32 := 0x06013423.
Lemma F_28b30 : fetch_word Ubsan.M.loaded_segments (0x28b30 : word) = Some W_28b30.
Proof. vm_refl. Qed.
Lemma D_28b30 : decode_any W_28b30 = Some (Store SZ8 2 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b34 : bv 32 := 0x1940006f.
Lemma F_28b34 : fetch_word Ubsan.M.loaded_segments (0x28b34 : word) = Some W_28b34.
Proof. vm_refl. Qed.
Lemma D_28b34 : decode_any W_28b34 = Some (Jal 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b38 : bv 32 := 0x002b1493.
Lemma F_28b38 : fetch_word Ubsan.M.loaded_segments (0x28b38 : word) = Some W_28b38.
Proof. vm_refl. Qed.
Lemma D_28b38 : decode_any W_28b38 = Some (ShiftImm ALU_SLL 9 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b3c : bv 32 := 0xfffea617.
Lemma F_28b3c : fetch_word Ubsan.M.loaded_segments (0x28b3c : word) = Some W_28b3c.
Proof. vm_refl. Qed.
Lemma D_28b3c : decode_any W_28b3c = Some (Auipc 12 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b40 : bv 32 := 0xe3460a13.
Lemma F_28b40 : fetch_word Ubsan.M.loaded_segments (0x28b40 : word) = Some W_28b40.
Proof. vm_refl. Qed.
Lemma D_28b40 : decode_any W_28b40 = Some (OpImm ALU_ADD 20 12 3636, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b44 : bv 32 := 0xfffa4613.
Lemma F_28b44 : fetch_word Ubsan.M.loaded_segments (0x28b44 : word) = Some W_28b44.
Proof. vm_refl. Qed.
Lemma D_28b44 : decode_any W_28b44 = Some (OpImm ALU_XOR 12 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b48 : bv 32 := 0x00967463.
Lemma F_28b48 : fetch_word Ubsan.M.loaded_segments (0x28b48 : word) = Some W_28b48.
Proof. vm_refl. Qed.
Lemma D_28b48 : decode_any W_28b48 = Some (Branch BC_GEU 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b4c : bv 32 := 0x45d0106f.
Lemma F_28b4c : fetch_word Ubsan.M.loaded_segments (0x28b4c : word) = Some W_28b4c.
Proof. vm_refl. Qed.
Lemma D_28b4c : decode_any W_28b4c = Some (Jal 0 7260, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b50 : bv 32 := 0x02770633.
Lemma F_28b50 : fetch_word Ubsan.M.loaded_segments (0x28b50 : word) = Some W_28b50.
Proof. vm_refl. Qed.
Lemma D_28b50 : decode_any W_28b50 = Some (Mul M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b54 : bv 32 := 0x0277083b.
Lemma F_28b54 : fetch_word Ubsan.M.loaded_segments (0x28b54 : word) = Some W_28b54.
Proof. vm_refl. Qed.
Lemma D_28b54 : decode_any W_28b54 = Some (Mul32 M_MUL 16 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b58 : bv 32 := 0x00c80463.
Lemma F_28b58 : fetch_word Ubsan.M.loaded_segments (0x28b58 : word) = Some W_28b58.
Proof. vm_refl. Qed.
Lemma D_28b58 : decode_any W_28b58 = Some (Branch BC_EQ 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b5c : bv 32 := 0x44d0106f.
Lemma F_28b5c : fetch_word Ubsan.M.loaded_segments (0x28b5c : word) = Some W_28b5c.
Proof. vm_refl. Qed.
Lemma D_28b5c : decode_any W_28b5c = Some (Jal 0 7244, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b60 : bv 32 := 0x0006061b.
Lemma F_28b60 : fetch_word Ubsan.M.loaded_segments (0x28b60 : word) = Some W_28b60.
Proof. vm_refl. Qed.
Lemma D_28b60 : decode_any W_28b60 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b64 : bv 32 := 0x00261393.
Lemma F_28b64 : fetch_word Ubsan.M.loaded_segments (0x28b64 : word) = Some W_28b64.
Proof. vm_refl. Qed.
Lemma D_28b64 : decode_any W_28b64 = Some (ShiftImm ALU_SLL 7 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b68 : bv 32 := 0x007503b3.
Lemma F_28b68 : fetch_word Ubsan.M.loaded_segments (0x28b68 : word) = Some W_28b68.
Proof. vm_refl. Qed.
Lemma D_28b68 : decode_any W_28b68 = Some (Op ALU_ADD 7 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b6c : bv 32 := 0x00a03833.
Lemma F_28b6c : fetch_word Ubsan.M.loaded_segments (0x28b6c : word) = Some W_28b6c.
Proof. vm_refl. Qed.
Lemma D_28b6c : decode_any W_28b6c = Some (Op ALU_SLTU 16 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b70 : bv 32 := 0x0013be13.
Lemma F_28b70 : fetch_word Ubsan.M.loaded_segments (0x28b70 : word) = Some W_28b70.
Proof. vm_refl. Qed.
Lemma D_28b70 : decode_any W_28b70 = Some (OpImm ALU_SLTU 28 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b74 : bv 32 := 0x01c81463.
Lemma F_28b74 : fetch_word Ubsan.M.loaded_segments (0x28b74 : word) = Some W_28b74.
Proof. vm_refl. Qed.
Lemma D_28b74 : decode_any W_28b74 = Some (Branch BC_NE 16 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b78 : bv 32 := 0x4310106f.
Lemma F_28b78 : fetch_word Ubsan.M.loaded_segments (0x28b78 : word) = Some W_28b78.
Proof. vm_refl. Qed.
Lemma D_28b78 : decode_any W_28b78 = Some (Jal 0 7216, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b7c : bv 32 := 0x00a3b533.
Lemma F_28b7c : fetch_word Ubsan.M.loaded_segments (0x28b7c : word) = Some W_28b7c.
Proof. vm_refl. Qed.
Lemma D_28b7c : decode_any W_28b7c = Some (Op ALU_SLTU 10 7 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b80 : bv 32 := 0x00062613.
Lemma F_28b80 : fetch_word Ubsan.M.loaded_segments (0x28b80 : word) = Some W_28b80.
Proof. vm_refl. Qed.
Lemma D_28b80 : decode_any W_28b80 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b84 : bv 32 := 0x00c54533.
Lemma F_28b84 : fetch_word Ubsan.M.loaded_segments (0x28b84 : word) = Some W_28b84.
Proof. vm_refl. Qed.
Lemma D_28b84 : decode_any W_28b84 = Some (Op ALU_XOR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b88 : bv 32 := 0x00154513.
Lemma F_28b88 : fetch_word Ubsan.M.loaded_segments (0x28b88 : word) = Some W_28b88.
Proof. vm_refl. Qed.
Lemma D_28b88 : decode_any W_28b88 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b8c : bv 32 := 0x00051463.
Lemma F_28b8c : fetch_word Ubsan.M.loaded_segments (0x28b8c : word) = Some W_28b8c.
Proof. vm_refl. Qed.
Lemma D_28b8c : decode_any W_28b8c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b90 : bv 32 := 0x4190106f.
Lemma F_28b90 : fetch_word Ubsan.M.loaded_segments (0x28b90 : word) = Some W_28b90.
Proof. vm_refl. Qed.
Lemma D_28b90 : decode_any W_28b90 = Some (Jal 0 7192, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b94 : bv 32 := 0x000b8b9b.
Lemma F_28b94 : fetch_word Ubsan.M.loaded_segments (0x28b94 : word) = Some W_28b94.
Proof. vm_refl. Qed.
Lemma D_28b94 : decode_any W_28b94 = Some (OpImm32 23 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b98 : bv 32 := 0x01768533.
Lemma F_28b98 : fetch_word Ubsan.M.loaded_segments (0x28b98 : word) = Some W_28b98.
Proof. vm_refl. Qed.
Lemma D_28b98 : decode_any W_28b98 = Some (Op ALU_ADD 10 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_28b9c : bv 32 := 0x0176863b.
Lemma F_28b9c : fetch_word Ubsan.M.loaded_segments (0x28b9c : word) = Some W_28b9c.
Proof. vm_refl. Qed.
Lemma D_28b9c : decode_any W_28b9c = Some (Op32 ALU_ADD 12 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ba0 : bv 32 := 0x00a60463.
Lemma F_28ba0 : fetch_word Ubsan.M.loaded_segments (0x28ba0 : word) = Some W_28ba0.
Proof. vm_refl. Qed.
Lemma D_28ba0 : decode_any W_28ba0 = Some (Branch BC_EQ 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ba4 : bv 32 := 0x4050106f.
Lemma F_28ba4 : fetch_word Ubsan.M.loaded_segments (0x28ba4 : word) = Some W_28ba4.
Proof. vm_refl. Qed.
Lemma D_28ba4 : decode_any W_28ba4 = Some (Jal 0 7172, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ba8 : bv 32 := 0x4055551b.
Lemma F_28ba8 : fetch_word Ubsan.M.loaded_segments (0x28ba8 : word) = Some W_28ba8.
Proof. vm_refl. Qed.
Lemma D_28ba8 : decode_any W_28ba8 = Some (ShiftImm32 ALU_SRA 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bac : bv 32 := 0x00251613.
Lemma F_28bac : fetch_word Ubsan.M.loaded_segments (0x28bac : word) = Some W_28bac.
Proof. vm_refl. Qed.
Lemma D_28bac : decode_any W_28bac = Some (ShiftImm ALU_SLL 12 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bb0 : bv 32 := 0x00760633.
Lemma F_28bb0 : fetch_word Ubsan.M.loaded_segments (0x28bb0 : word) = Some W_28bb0.
Proof. vm_refl. Qed.
Lemma D_28bb0 : decode_any W_28bb0 = Some (Op ALU_ADD 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bb4 : bv 32 := 0x00163693.
Lemma F_28bb4 : fetch_word Ubsan.M.loaded_segments (0x28bb4 : word) = Some W_28bb4.
Proof. vm_refl. Qed.
Lemma D_28bb4 : decode_any W_28bb4 = Some (OpImm ALU_SLTU 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bb8 : bv 32 := 0x00d81463.
Lemma F_28bb8 : fetch_word Ubsan.M.loaded_segments (0x28bb8 : word) = Some W_28bb8.
Proof. vm_refl. Qed.
Lemma D_28bb8 : decode_any W_28bb8 = Some (Branch BC_NE 16 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bbc : bv 32 := 0x3ed0106f.
Lemma F_28bbc : fetch_word Ubsan.M.loaded_segments (0x28bbc : word) = Some W_28bbc.
Proof. vm_refl. Qed.
Lemma D_28bbc : decode_any W_28bbc = Some (Jal 0 7148, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bc0 : bv 32 := 0x007636b3.
Lemma F_28bc0 : fetch_word Ubsan.M.loaded_segments (0x28bc0 : word) = Some W_28bc0.
Proof. vm_refl. Qed.
Lemma D_28bc0 : decode_any W_28bc0 = Some (Op ALU_SLTU 13 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bc4 : bv 32 := 0x00052513.
Lemma F_28bc4 : fetch_word Ubsan.M.loaded_segments (0x28bc4 : word) = Some W_28bc4.
Proof. vm_refl. Qed.
Lemma D_28bc4 : decode_any W_28bc4 = Some (OpImm ALU_SLT 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bc8 : bv 32 := 0x00a6c533.
Lemma F_28bc8 : fetch_word Ubsan.M.loaded_segments (0x28bc8 : word) = Some W_28bc8.
Proof. vm_refl. Qed.
Lemma D_28bc8 : decode_any W_28bc8 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bcc : bv 32 := 0x00154513.
Lemma F_28bcc : fetch_word Ubsan.M.loaded_segments (0x28bcc : word) = Some W_28bcc.
Proof. vm_refl. Qed.
Lemma D_28bcc : decode_any W_28bcc = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bd0 : bv 32 := 0x00051463.
Lemma F_28bd0 : fetch_word Ubsan.M.loaded_segments (0x28bd0 : word) = Some W_28bd0.
Proof. vm_refl. Qed.
Lemma D_28bd0 : decode_any W_28bd0 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bd4 : bv 32 := 0x3d50106f.
Lemma F_28bd4 : fetch_word Ubsan.M.loaded_segments (0x28bd4 : word) = Some W_28bd4.
Proof. vm_refl. Qed.
Lemma D_28bd4 : decode_any W_28bd4 = Some (Jal 0 7124, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bd8 : bv 32 := 0x07013683.
Lemma F_28bd8 : fetch_word Ubsan.M.loaded_segments (0x28bd8 : word) = Some W_28bd8.
Proof. vm_refl. Qed.
Lemma D_28bd8 : decode_any W_28bd8 = Some (Load SZ8 true 13 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bdc : bv 32 := 0x00269693.
Lemma F_28bdc : fetch_word Ubsan.M.loaded_segments (0x28bdc : word) = Some W_28bdc.
Proof. vm_refl. Qed.
Lemma D_28bdc : decode_any W_28bdc = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28be0 : bv 32 := 0x00d60533.
Lemma F_28be0 : fetch_word Ubsan.M.loaded_segments (0x28be0 : word) = Some W_28be0.
Proof. vm_refl. Qed.
Lemma D_28be0 : decode_any W_28be0 = Some (Op ALU_ADD 10 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28be4 : bv 32 := 0x00c57463.
Lemma F_28be4 : fetch_word Ubsan.M.loaded_segments (0x28be4 : word) = Some W_28be4.
Proof. vm_refl. Qed.
Lemma D_28be4 : decode_any W_28be4 = Some (Branch BC_GEU 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28be8 : bv 32 := 0x3c10106f.
Lemma F_28be8 : fetch_word Ubsan.M.loaded_segments (0x28be8 : word) = Some W_28be8.
Proof. vm_refl. Qed.
Lemma D_28be8 : decode_any W_28be8 = Some (Jal 0 7104, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bec : bv 32 := 0x00153613.
Lemma F_28bec : fetch_word Ubsan.M.loaded_segments (0x28bec : word) = Some W_28bec.
Proof. vm_refl. Qed.
Lemma D_28bec : decode_any W_28bec = Some (OpImm ALU_SLTU 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bf0 : bv 32 := 0x00c84633.
Lemma F_28bf0 : fetch_word Ubsan.M.loaded_segments (0x28bf0 : word) = Some W_28bf0.
Proof. vm_refl. Qed.
Lemma D_28bf0 : decode_any W_28bf0 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bf4 : bv 32 := 0x00061463.
Lemma F_28bf4 : fetch_word Ubsan.M.loaded_segments (0x28bf4 : word) = Some W_28bf4.
Proof. vm_refl. Qed.
Lemma D_28bf4 : decode_any W_28bf4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bf8 : bv 32 := 0x3b10106f.
Lemma F_28bf8 : fetch_word Ubsan.M.loaded_segments (0x28bf8 : word) = Some W_28bf8.
Proof. vm_refl. Qed.
Lemma D_28bf8 : decode_any W_28bf8 = Some (Jal 0 7088, 4%Z).
Proof. vm_refl. Qed.

Definition W_28bfc : bv 32 := 0x05813803.
Lemma F_28bfc : fetch_word Ubsan.M.loaded_segments (0x28bfc : word) = Some W_28bfc.
Proof. vm_refl. Qed.
Lemma D_28bfc : decode_any W_28bfc = Some (Load SZ8 true 16 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c00 : bv 32 := 0x02580633.
Lemma F_28c00 : fetch_word Ubsan.M.loaded_segments (0x28c00 : word) = Some W_28c00.
Proof. vm_refl. Qed.
Lemma D_28c00 : decode_any W_28c00 = Some (Mul M_MUL 12 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c04 : bv 32 := 0x0258083b.
Lemma F_28c04 : fetch_word Ubsan.M.loaded_segments (0x28c04 : word) = Some W_28c04.
Proof. vm_refl. Qed.
Lemma D_28c04 : decode_any W_28c04 = Some (Mul32 M_MUL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c08 : bv 32 := 0x00c80463.
Lemma F_28c08 : fetch_word Ubsan.M.loaded_segments (0x28c08 : word) = Some W_28c08.
Proof. vm_refl. Qed.
Lemma D_28c08 : decode_any W_28c08 = Some (Branch BC_EQ 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c0c : bv 32 := 0x39d0106f.
Lemma F_28c0c : fetch_word Ubsan.M.loaded_segments (0x28c0c : word) = Some W_28c0c.
Proof. vm_refl. Qed.
Lemma D_28c0c : decode_any W_28c0c = Some (Jal 0 7068, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c10 : bv 32 := 0x0006061b.
Lemma F_28c10 : fetch_word Ubsan.M.loaded_segments (0x28c10 : word) = Some W_28c10.
Proof. vm_refl. Qed.
Lemma D_28c10 : decode_any W_28c10 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c14 : bv 32 := 0x00261293.
Lemma F_28c14 : fetch_word Ubsan.M.loaded_segments (0x28c14 : word) = Some W_28c14.
Proof. vm_refl. Qed.
Lemma D_28c14 : decode_any W_28c14 = Some (ShiftImm ALU_SLL 5 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c18 : bv 32 := 0x005982b3.
Lemma F_28c18 : fetch_word Ubsan.M.loaded_segments (0x28c18 : word) = Some W_28c18.
Proof. vm_refl. Qed.
Lemma D_28c18 : decode_any W_28c18 = Some (Op ALU_ADD 5 19 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c1c : bv 32 := 0x01303833.
Lemma F_28c1c : fetch_word Ubsan.M.loaded_segments (0x28c1c : word) = Some W_28c1c.
Proof. vm_refl. Qed.
Lemma D_28c1c : decode_any W_28c1c = Some (Op ALU_SLTU 16 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c20 : bv 32 := 0x0012b393.
Lemma F_28c20 : fetch_word Ubsan.M.loaded_segments (0x28c20 : word) = Some W_28c20.
Proof. vm_refl. Qed.
Lemma D_28c20 : decode_any W_28c20 = Some (OpImm ALU_SLTU 7 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c24 : bv 32 := 0x00781463.
Lemma F_28c24 : fetch_word Ubsan.M.loaded_segments (0x28c24 : word) = Some W_28c24.
Proof. vm_refl. Qed.
Lemma D_28c24 : decode_any W_28c24 = Some (Branch BC_NE 16 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c28 : bv 32 := 0x3810106f.
Lemma F_28c28 : fetch_word Ubsan.M.loaded_segments (0x28c28 : word) = Some W_28c28.
Proof. vm_refl. Qed.
Lemma D_28c28 : decode_any W_28c28 = Some (Jal 0 7040, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c2c : bv 32 := 0x0132b3b3.
Lemma F_28c2c : fetch_word Ubsan.M.loaded_segments (0x28c2c : word) = Some W_28c2c.
Proof. vm_refl. Qed.
Lemma D_28c2c : decode_any W_28c2c = Some (Op ALU_SLTU 7 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c30 : bv 32 := 0x00062613.
Lemma F_28c30 : fetch_word Ubsan.M.loaded_segments (0x28c30 : word) = Some W_28c30.
Proof. vm_refl. Qed.
Lemma D_28c30 : decode_any W_28c30 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c34 : bv 32 := 0x00c3c633.
Lemma F_28c34 : fetch_word Ubsan.M.loaded_segments (0x28c34 : word) = Some W_28c34.
Proof. vm_refl. Qed.
Lemma D_28c34 : decode_any W_28c34 = Some (Op ALU_XOR 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c38 : bv 32 := 0x00164613.
Lemma F_28c38 : fetch_word Ubsan.M.loaded_segments (0x28c38 : word) = Some W_28c38.
Proof. vm_refl. Qed.
Lemma D_28c38 : decode_any W_28c38 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c3c : bv 32 := 0x00061463.
Lemma F_28c3c : fetch_word Ubsan.M.loaded_segments (0x28c3c : word) = Some W_28c3c.
Proof. vm_refl. Qed.
Lemma D_28c3c : decode_any W_28c3c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c40 : bv 32 := 0x3690106f.
Lemma F_28c40 : fetch_word Ubsan.M.loaded_segments (0x28c40 : word) = Some W_28c40.
Proof. vm_refl. Qed.
Lemma D_28c40 : decode_any W_28c40 = Some (Jal 0 7016, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c44 : bv 32 := 0x017c0633.
Lemma F_28c44 : fetch_word Ubsan.M.loaded_segments (0x28c44 : word) = Some W_28c44.
Proof. vm_refl. Qed.
Lemma D_28c44 : decode_any W_28c44 = Some (Op ALU_ADD 12 24 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c48 : bv 32 := 0x017c03bb.
Lemma F_28c48 : fetch_word Ubsan.M.loaded_segments (0x28c48 : word) = Some W_28c48.
Proof. vm_refl. Qed.
Lemma D_28c48 : decode_any W_28c48 = Some (Op32 ALU_ADD 7 24 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c4c : bv 32 := 0x00c38463.
Lemma F_28c4c : fetch_word Ubsan.M.loaded_segments (0x28c4c : word) = Some W_28c4c.
Proof. vm_refl. Qed.
Lemma D_28c4c : decode_any W_28c4c = Some (Branch BC_EQ 7 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c50 : bv 32 := 0x3590106f.
Lemma F_28c50 : fetch_word Ubsan.M.loaded_segments (0x28c50 : word) = Some W_28c50.
Proof. vm_refl. Qed.
Lemma D_28c50 : decode_any W_28c50 = Some (Jal 0 7000, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c54 : bv 32 := 0x4056561b.
Lemma F_28c54 : fetch_word Ubsan.M.loaded_segments (0x28c54 : word) = Some W_28c54.
Proof. vm_refl. Qed.
Lemma D_28c54 : decode_any W_28c54 = Some (ShiftImm32 ALU_SRA 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c58 : bv 32 := 0x00261393.
Lemma F_28c58 : fetch_word Ubsan.M.loaded_segments (0x28c58 : word) = Some W_28c58.
Proof. vm_refl. Qed.
Lemma D_28c58 : decode_any W_28c58 = Some (ShiftImm ALU_SLL 7 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c5c : bv 32 := 0x005383b3.
Lemma F_28c5c : fetch_word Ubsan.M.loaded_segments (0x28c5c : word) = Some W_28c5c.
Proof. vm_refl. Qed.
Lemma D_28c5c : decode_any W_28c5c = Some (Op ALU_ADD 7 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c60 : bv 32 := 0x0013be13.
Lemma F_28c60 : fetch_word Ubsan.M.loaded_segments (0x28c60 : word) = Some W_28c60.
Proof. vm_refl. Qed.
Lemma D_28c60 : decode_any W_28c60 = Some (OpImm ALU_SLTU 28 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c64 : bv 32 := 0x01c81463.
Lemma F_28c64 : fetch_word Ubsan.M.loaded_segments (0x28c64 : word) = Some W_28c64.
Proof. vm_refl. Qed.
Lemma D_28c64 : decode_any W_28c64 = Some (Branch BC_NE 16 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c68 : bv 32 := 0x3410106f.
Lemma F_28c68 : fetch_word Ubsan.M.loaded_segments (0x28c68 : word) = Some W_28c68.
Proof. vm_refl. Qed.
Lemma D_28c68 : decode_any W_28c68 = Some (Jal 0 6976, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c6c : bv 32 := 0x0053b2b3.
Lemma F_28c6c : fetch_word Ubsan.M.loaded_segments (0x28c6c : word) = Some W_28c6c.
Proof. vm_refl. Qed.
Lemma D_28c6c : decode_any W_28c6c = Some (Op ALU_SLTU 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c70 : bv 32 := 0x00062613.
Lemma F_28c70 : fetch_word Ubsan.M.loaded_segments (0x28c70 : word) = Some W_28c70.
Proof. vm_refl. Qed.
Lemma D_28c70 : decode_any W_28c70 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c74 : bv 32 := 0x00c2c633.
Lemma F_28c74 : fetch_word Ubsan.M.loaded_segments (0x28c74 : word) = Some W_28c74.
Proof. vm_refl. Qed.
Lemma D_28c74 : decode_any W_28c74 = Some (Op ALU_XOR 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c78 : bv 32 := 0x00164613.
Lemma F_28c78 : fetch_word Ubsan.M.loaded_segments (0x28c78 : word) = Some W_28c78.
Proof. vm_refl. Qed.
Lemma D_28c78 : decode_any W_28c78 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c7c : bv 32 := 0x00061463.
Lemma F_28c7c : fetch_word Ubsan.M.loaded_segments (0x28c7c : word) = Some W_28c7c.
Proof. vm_refl. Qed.
Lemma D_28c7c : decode_any W_28c7c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c80 : bv 32 := 0x3290106f.
Lemma F_28c80 : fetch_word Ubsan.M.loaded_segments (0x28c80 : word) = Some W_28c80.
Proof. vm_refl. Qed.
Lemma D_28c80 : decode_any W_28c80 = Some (Jal 0 6952, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c84 : bv 32 := 0x007686b3.
Lemma F_28c84 : fetch_word Ubsan.M.loaded_segments (0x28c84 : word) = Some W_28c84.
Proof. vm_refl. Qed.
Lemma D_28c84 : decode_any W_28c84 = Some (Op ALU_ADD 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c88 : bv 32 := 0x0076f463.
Lemma F_28c88 : fetch_word Ubsan.M.loaded_segments (0x28c88 : word) = Some W_28c88.
Proof. vm_refl. Qed.
Lemma D_28c88 : decode_any W_28c88 = Some (Branch BC_GEU 13 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c8c : bv 32 := 0x31d0106f.
Lemma F_28c8c : fetch_word Ubsan.M.loaded_segments (0x28c8c : word) = Some W_28c8c.
Proof. vm_refl. Qed.
Lemma D_28c8c : decode_any W_28c8c = Some (Jal 0 6940, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c90 : bv 32 := 0x0016b613.
Lemma F_28c90 : fetch_word Ubsan.M.loaded_segments (0x28c90 : word) = Some W_28c90.
Proof. vm_refl. Qed.
Lemma D_28c90 : decode_any W_28c90 = Some (OpImm ALU_SLTU 12 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c94 : bv 32 := 0x00c84633.
Lemma F_28c94 : fetch_word Ubsan.M.loaded_segments (0x28c94 : word) = Some W_28c94.
Proof. vm_refl. Qed.
Lemma D_28c94 : decode_any W_28c94 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c98 : bv 32 := 0x00061463.
Lemma F_28c98 : fetch_word Ubsan.M.loaded_segments (0x28c98 : word) = Some W_28c98.
Proof. vm_refl. Qed.
Lemma D_28c98 : decode_any W_28c98 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28c9c : bv 32 := 0x30d0106f.
Lemma F_28c9c : fetch_word Ubsan.M.loaded_segments (0x28c9c : word) = Some W_28c9c.
Proof. vm_refl. Qed.
Lemma D_28c9c : decode_any W_28c9c = Some (Jal 0 6924, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ca0 : bv 32 := 0x009a04b3.
Lemma F_28ca0 : fetch_word Ubsan.M.loaded_segments (0x28ca0 : word) = Some W_28ca0.
Proof. vm_refl. Qed.
Lemma D_28ca0 : decode_any W_28ca0 = Some (Op ALU_ADD 9 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ca4 : bv 32 := 0x0004a603.
Lemma F_28ca4 : fetch_word Ubsan.M.loaded_segments (0x28ca4 : word) = Some W_28ca4.
Proof. vm_refl. Qed.
Lemma D_28ca4 : decode_any W_28ca4 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ca8 : bv 32 := 0x06c13023.
Lemma F_28ca8 : fetch_word Ubsan.M.loaded_segments (0x28ca8 : word) = Some W_28ca8.
Proof. vm_refl. Qed.
Lemma D_28ca8 : decode_any W_28ca8 = Some (Store SZ8 2 12 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cac : bv 32 := 0x07013603.
Lemma F_28cac : fetch_word Ubsan.M.loaded_segments (0x28cac : word) = Some W_28cac.
Proof. vm_refl. Qed.
Lemma D_28cac : decode_any W_28cac = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cb0 : bv 32 := 0x00261613.
Lemma F_28cb0 : fetch_word Ubsan.M.loaded_segments (0x28cb0 : word) = Some W_28cb0.
Proof. vm_refl. Qed.
Lemma D_28cb0 : decode_any W_28cb0 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cb4 : bv 32 := 0x00c38633.
Lemma F_28cb4 : fetch_word Ubsan.M.loaded_segments (0x28cb4 : word) = Some W_28cb4.
Proof. vm_refl. Qed.
Lemma D_28cb4 : decode_any W_28cb4 = Some (Op ALU_ADD 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cb8 : bv 32 := 0x06c13423.
Lemma F_28cb8 : fetch_word Ubsan.M.loaded_segments (0x28cb8 : word) = Some W_28cb8.
Proof. vm_refl. Qed.
Lemma D_28cb8 : decode_any W_28cb8 = Some (Store SZ8 2 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cbc : bv 32 := 0x01642633.
Lemma F_28cbc : fetch_word Ubsan.M.loaded_segments (0x28cbc : word) = Some W_28cbc.
Proof. vm_refl. Qed.
Lemma D_28cbc : decode_any W_28cbc = Some (Op ALU_SLT 12 8 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cc0 : bv 32 := 0x00164613.
Lemma F_28cc0 : fetch_word Ubsan.M.loaded_segments (0x28cc0 : word) = Some W_28cc0.
Proof. vm_refl. Qed.
Lemma D_28cc0 : decode_any W_28cc0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cc4 : bv 32 := 0x00c13423.
Lemma F_28cc4 : fetch_word Ubsan.M.loaded_segments (0x28cc4 : word) = Some W_28cc4.
Proof. vm_refl. Qed.
Lemma D_28cc4 : decode_any W_28cc4 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cc8 : bv 32 := 0xfffe8697.
Lemma F_28cc8 : fetch_word Ubsan.M.loaded_segments (0x28cc8 : word) = Some W_28cc8.
Proof. vm_refl. Qed.
Lemma D_28cc8 : decode_any W_28cc8 = Some (Auipc 13 1048552, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ccc : bv 32 := 0xfff58613.
Lemma F_28ccc : fetch_word Ubsan.M.loaded_segments (0x28ccc : word) = Some W_28ccc.
Proof. vm_refl. Qed.
Lemma D_28ccc : decode_any W_28ccc = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cd0 : bv 32 := 0x00d00813.
Lemma F_28cd0 : fetch_word Ubsan.M.loaded_segments (0x28cd0 : word) = Some W_28cd0.
Proof. vm_refl. Qed.
Lemma D_28cd0 : decode_any W_28cd0 = Some (OpImm ALU_ADD 16 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cd4 : bv 32 := 0xb6e68693.
Lemma F_28cd4 : fetch_word Ubsan.M.loaded_segments (0x28cd4 : word) = Some W_28cd4.
Proof. vm_refl. Qed.
Lemma D_28cd4 : decode_any W_28cd4 = Some (OpImm ALU_ADD 13 13 2926, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cd8 : bv 32 := 0x1cc86ce3.
Lemma F_28cd8 : fetch_word Ubsan.M.loaded_segments (0x28cd8 : word) = Some W_28cd8.
Proof. vm_refl. Qed.
Lemma D_28cd8 : decode_any W_28cd8 = Some (Branch BC_LTU 16 12 2520, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cdc : bv 32 := 0x00261613.
Lemma F_28cdc : fetch_word Ubsan.M.loaded_segments (0x28cdc : word) = Some W_28cdc.
Proof. vm_refl. Qed.
Lemma D_28cdc : decode_any W_28cdc = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ce0 : bv 32 := 0xfffea817.
Lemma F_28ce0 : fetch_word Ubsan.M.loaded_segments (0x28ce0 : word) = Some W_28ce0.
Proof. vm_refl. Qed.
Lemma D_28ce0 : decode_any W_28ce0 = Some (Auipc 16 1048554, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ce4 : bv 32 := 0xb6480813.
Lemma F_28ce4 : fetch_word Ubsan.M.loaded_segments (0x28ce4 : word) = Some W_28ce4.
Proof. vm_refl. Qed.
Lemma D_28ce4 : decode_any W_28ce4 = Some (OpImm ALU_ADD 16 16 2916, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ce8 : bv 32 := 0x01060633.
Lemma F_28ce8 : fetch_word Ubsan.M.loaded_segments (0x28ce8 : word) = Some W_28ce8.
Proof. vm_refl. Qed.
Lemma D_28ce8 : decode_any W_28ce8 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cec : bv 32 := 0x00062603.
Lemma F_28cec : fetch_word Ubsan.M.loaded_segments (0x28cec : word) = Some W_28cec.
Proof. vm_refl. Qed.
Lemma D_28cec : decode_any W_28cec = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cf0 : bv 32 := 0x01060633.
Lemma F_28cf0 : fetch_word Ubsan.M.loaded_segments (0x28cf0 : word) = Some W_28cf0.
Proof. vm_refl. Qed.
Lemma D_28cf0 : decode_any W_28cf0 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cf4 : bv 32 := 0x05813803.
Lemma F_28cf4 : fetch_word Ubsan.M.loaded_segments (0x28cf4 : word) = Some W_28cf4.
Proof. vm_refl. Qed.
Lemma D_28cf4 : decode_any W_28cf4 = Some (Load SZ8 true 16 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cf8 : bv 32 := 0x00082813.
Lemma F_28cf8 : fetch_word Ubsan.M.loaded_segments (0x28cf8 : word) = Some W_28cf8.
Proof. vm_refl. Qed.
Lemma D_28cf8 : decode_any W_28cf8 = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28cfc : bv 32 := 0x07013c23.
Lemma F_28cfc : fetch_word Ubsan.M.loaded_segments (0x28cfc : word) = Some W_28cfc.
Proof. vm_refl. Qed.
Lemma D_28cfc : decode_any W_28cfc = Some (Store SZ8 2 16 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d00 : bv 32 := 0x00060067.
Lemma F_28d00 : fetch_word Ubsan.M.loaded_segments (0x28d00 : word) = Some W_28d00.
Proof. vm_refl. Qed.
Lemma D_28d00 : decode_any W_28d00 = Some (Jalr 0 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d04 : bv 32 := 0x18008263.
Lemma F_28d04 : fetch_word Ubsan.M.loaded_segments (0x28d04 : word) = Some W_28d04.
Proof. vm_refl. Qed.
Lemma D_28d04 : decode_any W_28d04 = Some (Branch BC_EQ 1 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d08 : bv 32 := 0x00000593.
Lemma F_28d08 : fetch_word Ubsan.M.loaded_segments (0x28d08 : word) = Some W_28d08.
Proof. vm_refl. Qed.
Lemma D_28d08 : decode_any W_28d08 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d0c : bv 32 := 0xffffc613.
Lemma F_28d0c : fetch_word Ubsan.M.loaded_segments (0x28d0c : word) = Some W_28d0c.
Proof. vm_refl. Qed.
Lemma D_28d0c : decode_any W_28d0c = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d10 : bv 32 := 0x00c13023.
Lemma F_28d10 : fetch_word Ubsan.M.loaded_segments (0x28d10 : word) = Some W_28d10.
Proof. vm_refl. Qed.
Lemma D_28d10 : decode_any W_28d10 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d14 : bv 32 := 0xfffdc293.
Lemma F_28d14 : fetch_word Ubsan.M.loaded_segments (0x28d14 : word) = Some W_28d14.
Proof. vm_refl. Qed.
Lemma D_28d14 : decode_any W_28d14 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d18 : bv 32 := 0x00271393.
Lemma F_28d18 : fetch_word Ubsan.M.loaded_segments (0x28d18 : word) = Some W_28d18.
Proof. vm_refl. Qed.
Lemma D_28d18 : decode_any W_28d18 = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d1c : bv 32 := 0x05813683.
Lemma F_28d1c : fetch_word Ubsan.M.loaded_segments (0x28d1c : word) = Some W_28d1c.
Proof. vm_refl. Qed.
Lemma D_28d1c : decode_any W_28d1c = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d20 : bv 32 := 0x00269693.
Lemma F_28d20 : fetch_word Ubsan.M.loaded_segments (0x28d20 : word) = Some W_28d20.
Proof. vm_refl. Qed.
Lemma D_28d20 : decode_any W_28d20 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d24 : bv 32 := 0x003cfb93.
Lemma F_28d24 : fetch_word Ubsan.M.loaded_segments (0x28d24 : word) = Some W_28d24.
Proof. vm_refl. Qed.
Lemma D_28d24 : decode_any W_28d24 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d28 : bv 32 := 0x0037f613.
Lemma F_28d28 : fetch_word Ubsan.M.loaded_segments (0x28d28 : word) = Some W_28d28.
Proof. vm_refl. Qed.
Lemma D_28d28 : decode_any W_28d28 = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d2c : bv 32 := 0x05013483.
Lemma F_28d2c : fetch_word Ubsan.M.loaded_segments (0x28d2c : word) = Some W_28d2c.
Proof. vm_refl. Qed.
Lemma D_28d2c : decode_any W_28d2c = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d30 : bv 32 := 0x02813803.
Lemma F_28d30 : fetch_word Ubsan.M.loaded_segments (0x28d30 : word) = Some W_28d30.
Proof. vm_refl. Qed.
Lemma D_28d30 : decode_any W_28d30 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d34 : bv 32 := 0x4098083b.
Lemma F_28d34 : fetch_word Ubsan.M.loaded_segments (0x28d34 : word) = Some W_28d34.
Proof. vm_refl. Qed.
Lemma D_28d34 : decode_any W_28d34 = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d38 : bv 32 := 0x03813883.
Lemma F_28d38 : fetch_word Ubsan.M.loaded_segments (0x28d38 : word) = Some W_28d38.
Proof. vm_refl. Qed.
Lemma D_28d38 : decode_any W_28d38 = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d3c : bv 32 := 0x03013e03.
Lemma F_28d3c : fetch_word Ubsan.M.loaded_segments (0x28d3c : word) = Some W_28d3c.
Proof. vm_refl. Qed.
Lemma D_28d3c : decode_any W_28d3c = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d40 : bv 32 := 0x011e08b3.
Lemma F_28d40 : fetch_word Ubsan.M.loaded_segments (0x28d40 : word) = Some W_28d40.
Proof. vm_refl. Qed.
Lemma D_28d40 : decode_any W_28d40 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d44 : bv 32 := 0x04813a03.
Lemma F_28d44 : fetch_word Ubsan.M.loaded_segments (0x28d44 : word) = Some W_28d44.
Proof. vm_refl. Qed.
Lemma D_28d44 : decode_any W_28d44 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d48 : bv 32 := 0x43fa5e13.
Lemma F_28d48 : fetch_word Ubsan.M.loaded_segments (0x28d48 : word) = Some W_28d48.
Proof. vm_refl. Qed.
Lemma D_28d48 : decode_any W_28d48 = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d4c : bv 32 := 0x01013983.
Lemma F_28d4c : fetch_word Ubsan.M.loaded_segments (0x28d4c : word) = Some W_28d4c.
Proof. vm_refl. Qed.
Lemma D_28d4c : decode_any W_28d4c = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d50 : bv 32 := 0x0019f993.
Lemma F_28d50 : fetch_word Ubsan.M.loaded_segments (0x28d50 : word) = Some W_28d50.
Proof. vm_refl. Qed.
Lemma D_28d50 : decode_any W_28d50 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d54 : bv 32 := 0x001d7c13.
Lemma F_28d54 : fetch_word Ubsan.M.loaded_segments (0x28d54 : word) = Some W_28d54.
Proof. vm_refl. Qed.
Lemma D_28d54 : decode_any W_28d54 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d58 : bv 32 := 0x01f00093.
Lemma F_28d58 : fetch_word Ubsan.M.loaded_segments (0x28d58 : word) = Some W_28d58.
Proof. vm_refl. Qed.
Lemma D_28d58 : decode_any W_28d58 = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d5c : bv 32 := 0x014e7e33.
Lemma F_28d5c : fetch_word Ubsan.M.loaded_segments (0x28d5c : word) = Some W_28d5c.
Proof. vm_refl. Qed.
Lemma D_28d5c : decode_any W_28d5c = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d60 : bv 32 := 0x409888bb.
Lemma F_28d60 : fetch_word Ubsan.M.loaded_segments (0x28d60 : word) = Some W_28d60.
Proof. vm_refl. Qed.
Lemma D_28d60 : decode_any W_28d60 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d64 : bv 32 := 0x00d78a33.
Lemma F_28d64 : fetch_word Ubsan.M.loaded_segments (0x28d64 : word) = Some W_28d64.
Proof. vm_refl. Qed.
Lemma D_28d64 : decode_any W_28d64 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d68 : bv 32 := 0x00163b13.
Lemma F_28d68 : fetch_word Ubsan.M.loaded_segments (0x28d68 : word) = Some W_28d68.
Proof. vm_refl. Qed.
Lemma D_28d68 : decode_any W_28d68 = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d6c : bv 32 := 0x04013603.
Lemma F_28d6c : fetch_word Ubsan.M.loaded_segments (0x28d6c : word) = Some W_28d6c.
Proof. vm_refl. Qed.
Lemma D_28d6c : decode_any W_28d6c = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d70 : bv 32 := 0x40c8863b.
Lemma F_28d70 : fetch_word Ubsan.M.loaded_segments (0x28d70 : word) = Some W_28d70.
Proof. vm_refl. Qed.
Lemma D_28d70 : decode_any W_28d70 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d74 : bv 32 := 0x01c6063b.
Lemma F_28d74 : fetch_word Ubsan.M.loaded_segments (0x28d74 : word) = Some W_28d74.
Proof. vm_refl. Qed.
Lemma D_28d74 : decode_any W_28d74 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d78 : bv 32 := 0x43f65893.
Lemma F_28d78 : fetch_word Ubsan.M.loaded_segments (0x28d78 : word) = Some W_28d78.
Proof. vm_refl. Qed.
Lemma D_28d78 : decode_any W_28d78 = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d7c : bv 32 := 0x00c8f633.
Lemma F_28d7c : fetch_word Ubsan.M.loaded_segments (0x28d7c : word) = Some W_28d7c.
Proof. vm_refl. Qed.
Lemma D_28d7c : decode_any W_28d7c = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d80 : bv 32 := 0x40c80e3b.
Lemma F_28d80 : fetch_word Ubsan.M.loaded_segments (0x28d80 : word) = Some W_28d80.
Proof. vm_refl. Qed.
Lemma D_28d80 : decode_any W_28d80 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d84 : bv 32 := 0x00072493.
Lemma F_28d84 : fetch_word Ubsan.M.loaded_segments (0x28d84 : word) = Some W_28d84.
Proof. vm_refl. Qed.
Lemma D_28d84 : decode_any W_28d84 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d88 : bv 32 := 0x000c8813.
Lemma F_28d88 : fetch_word Ubsan.M.loaded_segments (0x28d88 : word) = Some W_28d88.
Proof. vm_refl. Qed.
Lemma D_28d88 : decode_any W_28d88 = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d8c : bv 32 := 0x00b78d33.
Lemma F_28d8c : fetch_word Ubsan.M.loaded_segments (0x28d8c : word) = Some W_28d8c.
Proof. vm_refl. Qed.
Lemma D_28d8c : decode_any W_28d8c = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d90 : bv 32 := 0x01a03633.
Lemma F_28d90 : fetch_word Ubsan.M.loaded_segments (0x28d90 : word) = Some W_28d90.
Proof. vm_refl. Qed.
Lemma D_28d90 : decode_any W_28d90 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d94 : bv 32 := 0x00cb7633.
Lemma F_28d94 : fetch_word Ubsan.M.loaded_segments (0x28d94 : word) = Some W_28d94.
Proof. vm_refl. Qed.
Lemma D_28d94 : decode_any W_28d94 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d98 : bv 32 := 0x04098a63.
Lemma F_28d98 : fetch_word Ubsan.M.loaded_segments (0x28d98 : word) = Some W_28d98.
Proof. vm_refl. Qed.
Lemma D_28d98 : decode_any W_28d98 = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_28d9c : bv 32 := 0x00061463.
Lemma F_28d9c : fetch_word Ubsan.M.loaded_segments (0x28d9c : word) = Some W_28d9c.
Proof. vm_refl. Qed.
Lemma D_28d9c : decode_any W_28d9c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28da0 : bv 32 := 0x2090106f.
Lemma F_28da0 : fetch_word Ubsan.M.loaded_segments (0x28da0 : word) = Some W_28da0.
Proof. vm_refl. Qed.
Lemma D_28da0 : decode_any W_28da0 = Some (Jal 0 6664, 4%Z).
Proof. vm_refl. Qed.

Definition W_28da4 : bv 32 := 0x02000613.
Lemma F_28da4 : fetch_word Ubsan.M.loaded_segments (0x28da4 : word) = Some W_28da4.
Proof. vm_refl. Qed.
Lemma D_28da4 : decode_any W_28da4 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28da8 : bv 32 := 0x00cf1463.
Lemma F_28da8 : fetch_word Ubsan.M.loaded_segments (0x28da8 : word) = Some W_28da8.
Proof. vm_refl. Qed.
Lemma D_28da8 : decode_any W_28da8 = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dac : bv 32 := 0x1fd0106f.
Lemma F_28dac : fetch_word Ubsan.M.loaded_segments (0x28dac : word) = Some W_28dac.
Proof. vm_refl. Qed.
Lemma D_28dac : decode_any W_28dac = Some (Jal 0 6652, 4%Z).
Proof. vm_refl. Qed.

Definition W_28db0 : bv 32 := 0x000d2603.
Lemma F_28db0 : fetch_word Ubsan.M.loaded_segments (0x28db0 : word) = Some W_28db0.
Proof. vm_refl. Qed.
Lemma D_28db0 : decode_any W_28db0 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28db4 : bv 32 := 0x01d61abb.
Lemma F_28db4 : fetch_word Ubsan.M.loaded_segments (0x28db4 : word) = Some W_28db4.
Proof. vm_refl. Qed.
Lemma D_28db4 : decode_any W_28db4 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_28db8 : bv 32 := 0x040c1663.
Lemma F_28db8 : fetch_word Ubsan.M.loaded_segments (0x28db8 : word) = Some W_28db8.
Proof. vm_refl. Qed.
Lemma D_28db8 : decode_any W_28db8 = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dbc : bv 32 := 0xffb00613.
Lemma F_28dbc : fetch_word Ubsan.M.loaded_segments (0x28dbc : word) = Some W_28dbc.
Proof. vm_refl. Qed.
Lemma D_28dbc : decode_any W_28dbc = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dc0 : bv 32 := 0x01a67463.
Lemma F_28dc0 : fetch_word Ubsan.M.loaded_segments (0x28dc0 : word) = Some W_28dc0.
Proof. vm_refl. Qed.
Lemma D_28dc0 : decode_any W_28dc0 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dc4 : bv 32 := 0x1e50106f.
Lemma F_28dc4 : fetch_word Ubsan.M.loaded_segments (0x28dc4 : word) = Some W_28dc4.
Proof. vm_refl. Qed.
Lemma D_28dc4 : decode_any W_28dc4 = Some (Jal 0 6628, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dc8 : bv 32 := 0x0080f463.
Lemma F_28dc8 : fetch_word Ubsan.M.loaded_segments (0x28dc8 : word) = Some W_28dc8.
Proof. vm_refl. Qed.
Lemma D_28dc8 : decode_any W_28dc8 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dcc : bv 32 := 0x1dd0106f.
Lemma F_28dcc : fetch_word Ubsan.M.loaded_segments (0x28dcc : word) = Some W_28dcc.
Proof. vm_refl. Qed.
Lemma D_28dcc : decode_any W_28dcc = Some (Jal 0 6620, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dd0 : bv 32 := 0x004d2603.
Lemma F_28dd0 : fetch_word Ubsan.M.loaded_segments (0x28dd0 : word) = Some W_28dd0.
Proof. vm_refl. Qed.
Lemma D_28dd0 : decode_any W_28dd0 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dd4 : bv 32 := 0x00013883.
Lemma F_28dd4 : fetch_word Ubsan.M.loaded_segments (0x28dd4 : word) = Some W_28dd4.
Proof. vm_refl. Qed.
Lemma D_28dd4 : decode_any W_28dd4 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dd8 : bv 32 := 0x011af8b3.
Lemma F_28dd8 : fetch_word Ubsan.M.loaded_segments (0x28dd8 : word) = Some W_28dd8.
Proof. vm_refl. Qed.
Lemma D_28dd8 : decode_any W_28dd8 = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ddc : bv 32 := 0x0086563b.
Lemma F_28ddc : fetch_word Ubsan.M.loaded_segments (0x28ddc : word) = Some W_28ddc.
Proof. vm_refl. Qed.
Lemma D_28ddc : decode_any W_28ddc = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28de0 : bv 32 := 0x01f67633.
Lemma F_28de0 : fetch_word Ubsan.M.loaded_segments (0x28de0 : word) = Some W_28de0.
Proof. vm_refl. Qed.
Lemma D_28de0 : decode_any W_28de0 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28de4 : bv 32 := 0x01166ab3.
Lemma F_28de4 : fetch_word Ubsan.M.loaded_segments (0x28de4 : word) = Some W_28de4.
Proof. vm_refl. Qed.
Lemma D_28de4 : decode_any W_28de4 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28de8 : bv 32 := 0x01c0006f.
Lemma F_28de8 : fetch_word Ubsan.M.loaded_segments (0x28de8 : word) = Some W_28de8.
Proof. vm_refl. Qed.
Lemma D_28de8 : decode_any W_28de8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dec : bv 32 := 0x00061463.
Lemma F_28dec : fetch_word Ubsan.M.loaded_segments (0x28dec : word) = Some W_28dec.
Proof. vm_refl. Qed.
Lemma D_28dec : decode_any W_28dec = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28df0 : bv 32 := 0x1b90106f.
Lemma F_28df0 : fetch_word Ubsan.M.loaded_segments (0x28df0 : word) = Some W_28df0.
Proof. vm_refl. Qed.
Lemma D_28df0 : decode_any W_28df0 = Some (Jal 0 6584, 4%Z).
Proof. vm_refl. Qed.

Definition W_28df4 : bv 32 := 0x0080f463.
Lemma F_28df4 : fetch_word Ubsan.M.loaded_segments (0x28df4 : word) = Some W_28df4.
Proof. vm_refl. Qed.
Lemma D_28df4 : decode_any W_28df4 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28df8 : bv 32 := 0x1b10106f.
Lemma F_28df8 : fetch_word Ubsan.M.loaded_segments (0x28df8 : word) = Some W_28df8.
Proof. vm_refl. Qed.
Lemma D_28df8 : decode_any W_28df8 = Some (Jal 0 6576, 4%Z).
Proof. vm_refl. Qed.

Definition W_28dfc : bv 32 := 0x000d2603.
Lemma F_28dfc : fetch_word Ubsan.M.loaded_segments (0x28dfc : word) = Some W_28dfc.
Proof. vm_refl. Qed.
Lemma D_28dfc : decode_any W_28dfc = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e00 : bv 32 := 0x00865abb.
Lemma F_28e00 : fetch_word Ubsan.M.loaded_segments (0x28e00 : word) = Some W_28e00.
Proof. vm_refl. Qed.
Lemma D_28e00 : decode_any W_28e00 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e04 : bv 32 := 0x000b8463.
Lemma F_28e04 : fetch_word Ubsan.M.loaded_segments (0x28e04 : word) = Some W_28e04.
Proof. vm_refl. Qed.
Lemma D_28e04 : decode_any W_28e04 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e08 : bv 32 := 0x1a10106f.
Lemma F_28e08 : fetch_word Ubsan.M.loaded_segments (0x28e08 : word) = Some W_28e08.
Proof. vm_refl. Qed.
Lemma D_28e08 : decode_any W_28e08 = Some (Jal 0 6560, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e0c : bv 32 := 0x000c9463.
Lemma F_28e0c : fetch_word Ubsan.M.loaded_segments (0x28e0c : word) = Some W_28e0c.
Proof. vm_refl. Qed.
Lemma D_28e0c : decode_any W_28e0c = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e10 : bv 32 := 0x1990106f.
Lemma F_28e10 : fetch_word Ubsan.M.loaded_segments (0x28e10 : word) = Some W_28e10.
Proof. vm_refl. Qed.
Lemma D_28e10 : decode_any W_28e10 = Some (Jal 0 6552, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e14 : bv 32 := 0x000ca603.
Lemma F_28e14 : fetch_word Ubsan.M.loaded_segments (0x28e14 : word) = Some W_28e14.
Proof. vm_refl. Qed.
Lemma D_28e14 : decode_any W_28e14 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e18 : bv 32 := 0x005678b3.
Lemma F_28e18 : fetch_word Ubsan.M.loaded_segments (0x28e18 : word) = Some W_28e18.
Proof. vm_refl. Qed.
Lemma D_28e18 : decode_any W_28e18 = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e1c : bv 32 := 0x01566633.
Lemma F_28e1c : fetch_word Ubsan.M.loaded_segments (0x28e1c : word) = Some W_28e1c.
Proof. vm_refl. Qed.
Lemma D_28e1c : decode_any W_28e1c = Some (Op ALU_OR 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e20 : bv 32 := 0xfff64613.
Lemma F_28e20 : fetch_word Ubsan.M.loaded_segments (0x28e20 : word) = Some W_28e20.
Proof. vm_refl. Qed.
Lemma D_28e20 : decode_any W_28e20 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e24 : bv 32 := 0x00cdf633.
Lemma F_28e24 : fetch_word Ubsan.M.loaded_segments (0x28e24 : word) = Some W_28e24.
Proof. vm_refl. Qed.
Lemma D_28e24 : decode_any W_28e24 = Some (Op ALU_AND 12 27 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e28 : bv 32 := 0x01166633.
Lemma F_28e28 : fetch_word Ubsan.M.loaded_segments (0x28e28 : word) = Some W_28e28.
Proof. vm_refl. Qed.
Lemma D_28e28 : decode_any W_28e28 = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e2c : bv 32 := 0x01038ab3.
Lemma F_28e2c : fetch_word Ubsan.M.loaded_segments (0x28e2c : word) = Some W_28e2c.
Proof. vm_refl. Qed.
Lemma D_28e2c : decode_any W_28e2c = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e30 : bv 32 := 0x00cca023.
Lemma F_28e30 : fetch_word Ubsan.M.loaded_segments (0x28e30 : word) = Some W_28e30.
Proof. vm_refl. Qed.
Lemma D_28e30 : decode_any W_28e30 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e34 : bv 32 := 0x000a9463.
Lemma F_28e34 : fetch_word Ubsan.M.loaded_segments (0x28e34 : word) = Some W_28e34.
Proof. vm_refl. Qed.
Lemma D_28e34 : decode_any W_28e34 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e38 : bv 32 := 0x1710106f.
Lemma F_28e38 : fetch_word Ubsan.M.loaded_segments (0x28e38 : word) = Some W_28e38.
Proof. vm_refl. Qed.
Lemma D_28e38 : decode_any W_28e38 = Some (Jal 0 6512, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e3c : bv 32 := 0x010ab633.
Lemma F_28e3c : fetch_word Ubsan.M.loaded_segments (0x28e3c : word) = Some W_28e3c.
Proof. vm_refl. Qed.
Lemma D_28e3c : decode_any W_28e3c = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e40 : bv 32 := 0x00964633.
Lemma F_28e40 : fetch_word Ubsan.M.loaded_segments (0x28e40 : word) = Some W_28e40.
Proof. vm_refl. Qed.
Lemma D_28e40 : decode_any W_28e40 = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e44 : bv 32 := 0x00164613.
Lemma F_28e44 : fetch_word Ubsan.M.loaded_segments (0x28e44 : word) = Some W_28e44.
Proof. vm_refl. Qed.
Lemma D_28e44 : decode_any W_28e44 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e48 : bv 32 := 0x00061463.
Lemma F_28e48 : fetch_word Ubsan.M.loaded_segments (0x28e48 : word) = Some W_28e48.
Proof. vm_refl. Qed.
Lemma D_28e48 : decode_any W_28e48 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e4c : bv 32 := 0x15d0106f.
Lemma F_28e4c : fetch_word Ubsan.M.loaded_segments (0x28e4c : word) = Some W_28e4c.
Proof. vm_refl. Qed.
Lemma D_28e4c : decode_any W_28e4c = Some (Jal 0 6492, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e50 : bv 32 := 0x00ba0633.
Lemma F_28e50 : fetch_word Ubsan.M.loaded_segments (0x28e50 : word) = Some W_28e50.
Proof. vm_refl. Qed.
Lemma D_28e50 : decode_any W_28e50 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e54 : bv 32 := 0x00061463.
Lemma F_28e54 : fetch_word Ubsan.M.loaded_segments (0x28e54 : word) = Some W_28e54.
Proof. vm_refl. Qed.
Lemma D_28e54 : decode_any W_28e54 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e58 : bv 32 := 0x1510106f.
Lemma F_28e58 : fetch_word Ubsan.M.loaded_segments (0x28e58 : word) = Some W_28e58.
Proof. vm_refl. Qed.
Lemma D_28e58 : decode_any W_28e58 = Some (Jal 0 6480, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e5c : bv 32 := 0x01a63633.
Lemma F_28e5c : fetch_word Ubsan.M.loaded_segments (0x28e5c : word) = Some W_28e5c.
Proof. vm_refl. Qed.
Lemma D_28e5c : decode_any W_28e5c = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e60 : bv 32 := 0x07813803.
Lemma F_28e60 : fetch_word Ubsan.M.loaded_segments (0x28e60 : word) = Some W_28e60.
Proof. vm_refl. Qed.
Lemma D_28e60 : decode_any W_28e60 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e64 : bv 32 := 0x01064633.
Lemma F_28e64 : fetch_word Ubsan.M.loaded_segments (0x28e64 : word) = Some W_28e64.
Proof. vm_refl. Qed.
Lemma D_28e64 : decode_any W_28e64 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e68 : bv 32 := 0x00164613.
Lemma F_28e68 : fetch_word Ubsan.M.loaded_segments (0x28e68 : word) = Some W_28e68.
Proof. vm_refl. Qed.
Lemma D_28e68 : decode_any W_28e68 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e6c : bv 32 := 0x00061463.
Lemma F_28e6c : fetch_word Ubsan.M.loaded_segments (0x28e6c : word) = Some W_28e6c.
Proof. vm_refl. Qed.
Lemma D_28e6c : decode_any W_28e6c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e70 : bv 32 := 0x1390106f.
Lemma F_28e70 : fetch_word Ubsan.M.loaded_segments (0x28e70 : word) = Some W_28e70.
Proof. vm_refl. Qed.
Lemma D_28e70 : decode_any W_28e70 = Some (Jal 0 6456, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e74 : bv 32 := 0x001e0e1b.
Lemma F_28e74 : fetch_word Ubsan.M.loaded_segments (0x28e74 : word) = Some W_28e74.
Proof. vm_refl. Qed.
Lemma D_28e74 : decode_any W_28e74 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e78 : bv 32 := 0x00d585b3.
Lemma F_28e78 : fetch_word Ubsan.M.loaded_segments (0x28e78 : word) = Some W_28e78.
Proof. vm_refl. Qed.
Lemma D_28e78 : decode_any W_28e78 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e7c : bv 32 := 0x007c8cb3.
Lemma F_28e7c : fetch_word Ubsan.M.loaded_segments (0x28e7c : word) = Some W_28e7c.
Proof. vm_refl. Qed.
Lemma D_28e7c : decode_any W_28e7c = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e80 : bv 32 := 0x000a8813.
Lemma F_28e80 : fetch_word Ubsan.M.loaded_segments (0x28e80 : word) = Some W_28e80.
Proof. vm_refl. Qed.
Lemma D_28e80 : decode_any W_28e80 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e84 : bv 32 := 0xf00e14e3.
Lemma F_28e84 : fetch_word Ubsan.M.loaded_segments (0x28e84 : word) = Some W_28e84.
Proof. vm_refl. Qed.
Lemma D_28e84 : decode_any W_28e84 = Some (Branch BC_NE 28 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e88 : bv 32 := 0x02013583.
Lemma F_28e88 : fetch_word Ubsan.M.loaded_segments (0x28e88 : word) = Some W_28e88.
Proof. vm_refl. Qed.
Lemma D_28e88 : decode_any W_28e88 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e8c : bv 32 := 0x16059e63.
Lemma F_28e8c : fetch_word Ubsan.M.loaded_segments (0x28e8c : word) = Some W_28e8c.
Proof. vm_refl. Qed.
Lemma D_28e8c : decode_any W_28e8c = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e90 : bv 32 := 0xffffc693.
Lemma F_28e90 : fetch_word Ubsan.M.loaded_segments (0x28e90 : word) = Some W_28e90.
Proof. vm_refl. Qed.
Lemma D_28e90 : decode_any W_28e90 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e94 : bv 32 := 0x00271293.
Lemma F_28e94 : fetch_word Ubsan.M.loaded_segments (0x28e94 : word) = Some W_28e94.
Proof. vm_refl. Qed.
Lemma D_28e94 : decode_any W_28e94 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e98 : bv 32 := 0x05813383.
Lemma F_28e98 : fetch_word Ubsan.M.loaded_segments (0x28e98 : word) = Some W_28e98.
Proof. vm_refl. Qed.
Lemma D_28e98 : decode_any W_28e98 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_28e9c : bv 32 := 0x00239393.
Lemma F_28e9c : fetch_word Ubsan.M.loaded_segments (0x28e9c : word) = Some W_28e9c.
Proof. vm_refl. Qed.
Lemma D_28e9c : decode_any W_28e9c = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ea0 : bv 32 := 0x00337613.
Lemma F_28ea0 : fetch_word Ubsan.M.loaded_segments (0x28ea0 : word) = Some W_28ea0.
Proof. vm_refl. Qed.
Lemma D_28ea0 : decode_any W_28ea0 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ea4 : bv 32 := 0x00397793.
Lemma F_28ea4 : fetch_word Ubsan.M.loaded_segments (0x28ea4 : word) = Some W_28ea4.
Proof. vm_refl. Qed.
Lemma D_28ea4 : decode_any W_28ea4 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ea8 : bv 32 := 0x07013a03.
Lemma F_28ea8 : fetch_word Ubsan.M.loaded_segments (0x28ea8 : word) = Some W_28ea8.
Proof. vm_refl. Qed.
Lemma D_28ea8 : decode_any W_28ea8 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_28eac : bv 32 := 0x002a1a13.
Lemma F_28eac : fetch_word Ubsan.M.loaded_segments (0x28eac : word) = Some W_28eac.
Proof. vm_refl. Qed.
Lemma D_28eac : decode_any W_28eac = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_28eb0 : bv 32 := 0x00072b93.
Lemma F_28eb0 : fetch_word Ubsan.M.loaded_segments (0x28eb0 : word) = Some W_28eb0.
Proof. vm_refl. Qed.
Lemma D_28eb0 : decode_any W_28eb0 = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28eb4 : bv 32 := 0x02000c93.
Lemma F_28eb4 : fetch_word Ubsan.M.loaded_segments (0x28eb4 : word) = Some W_28eb4.
Proof. vm_refl. Qed.
Lemma D_28eb4 : decode_any W_28eb4 = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28eb8 : bv 32 := 0xffb00d13.
Lemma F_28eb8 : fetch_word Ubsan.M.loaded_segments (0x28eb8 : word) = Some W_28eb8.
Proof. vm_refl. Qed.
Lemma D_28eb8 : decode_any W_28eb8 = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ebc : bv 32 := 0x0017b793.
Lemma F_28ebc : fetch_word Ubsan.M.loaded_segments (0x28ebc : word) = Some W_28ebc.
Proof. vm_refl. Qed.
Lemma D_28ebc : decode_any W_28ebc = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ec0 : bv 32 := 0x02f13023.
Lemma F_28ec0 : fetch_word Ubsan.M.loaded_segments (0x28ec0 : word) = Some W_28ec0.
Proof. vm_refl. Qed.
Lemma D_28ec0 : decode_any W_28ec0 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ec4 : bv 32 := 0x00163613.
Lemma F_28ec4 : fetch_word Ubsan.M.loaded_segments (0x28ec4 : word) = Some W_28ec4.
Proof. vm_refl. Qed.
Lemma D_28ec4 : decode_any W_28ec4 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ec8 : bv 32 := 0x00c13823.
Lemma F_28ec8 : fetch_word Ubsan.M.loaded_segments (0x28ec8 : word) = Some W_28ec8.
Proof. vm_refl. Qed.
Lemma D_28ec8 : decode_any W_28ec8 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ecc : bv 32 := 0x01f00993.
Lemma F_28ecc : fetch_word Ubsan.M.loaded_segments (0x28ecc : word) = Some W_28ecc.
Proof. vm_refl. Qed.
Lemma D_28ecc : decode_any W_28ecc = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ed0 : bv 32 := 0x00030b13.
Lemma F_28ed0 : fetch_word Ubsan.M.loaded_segments (0x28ed0 : word) = Some W_28ed0.
Proof. vm_refl. Qed.
Lemma D_28ed0 : decode_any W_28ed0 = Some (OpImm ALU_ADD 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ed4 : bv 32 := 0x00090c13.
Lemma F_28ed4 : fetch_word Ubsan.M.loaded_segments (0x28ed4 : word) = Some W_28ed4.
Proof. vm_refl. Qed.
Lemma D_28ed4 : decode_any W_28ed4 = Some (OpImm ALU_ADD 24 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ed8 : bv 32 := 0x07013603.
Lemma F_28ed8 : fetch_word Ubsan.M.loaded_segments (0x28ed8 : word) = Some W_28ed8.
Proof. vm_refl. Qed.
Lemma D_28ed8 : decode_any W_28ed8 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_28edc : bv 32 := 0x0a060e63.
Lemma F_28edc : fetch_word Ubsan.M.loaded_segments (0x28edc : word) = Some W_28edc.
Proof. vm_refl. Qed.
Lemma D_28edc : decode_any W_28edc = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ee0 : bv 32 := 0x00000d93.
Lemma F_28ee0 : fetch_word Ubsan.M.loaded_segments (0x28ee0 : word) = Some W_28ee0.
Proof. vm_refl. Qed.
Lemma D_28ee0 : decode_any W_28ee0 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ee4 : bv 32 := 0x00603833.
Lemma F_28ee4 : fetch_word Ubsan.M.loaded_segments (0x28ee4 : word) = Some W_28ee4.
Proof. vm_refl. Qed.
Lemma D_28ee4 : decode_any W_28ee4 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ee8 : bv 32 := 0x01203e33.
Lemma F_28ee8 : fetch_word Ubsan.M.loaded_segments (0x28ee8 : word) = Some W_28ee8.
Proof. vm_refl. Qed.
Lemma D_28ee8 : decode_any W_28ee8 = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_28eec : bv 32 := 0x01013603.
Lemma F_28eec : fetch_word Ubsan.M.loaded_segments (0x28eec : word) = Some W_28eec.
Proof. vm_refl. Qed.
Lemma D_28eec : decode_any W_28eec = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ef0 : bv 32 := 0x010674b3.
Lemma F_28ef0 : fetch_word Ubsan.M.loaded_segments (0x28ef0 : word) = Some W_28ef0.
Proof. vm_refl. Qed.
Lemma D_28ef0 : decode_any W_28ef0 = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ef4 : bv 32 := 0x02013603.
Lemma F_28ef4 : fetch_word Ubsan.M.loaded_segments (0x28ef4 : word) = Some W_28ef4.
Proof. vm_refl. Qed.
Lemma D_28ef4 : decode_any W_28ef4 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ef8 : bv 32 := 0x01c67ab3.
Lemma F_28ef8 : fetch_word Ubsan.M.loaded_segments (0x28ef8 : word) = Some W_28ef8.
Proof. vm_refl. Qed.
Lemma D_28ef8 : decode_any W_28ef8 = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_28efc : bv 32 := 0x01bb0633.
Lemma F_28efc : fetch_word Ubsan.M.loaded_segments (0x28efc : word) = Some W_28efc.
Proof. vm_refl. Qed.
Lemma D_28efc : decode_any W_28efc = Some (Op ALU_ADD 12 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f00 : bv 32 := 0x00667463.
Lemma F_28f00 : fetch_word Ubsan.M.loaded_segments (0x28f00 : word) = Some W_28f00.
Proof. vm_refl. Qed.
Lemma D_28f00 : decode_any W_28f00 = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f04 : bv 32 := 0x0a50106f.
Lemma F_28f04 : fetch_word Ubsan.M.loaded_segments (0x28f04 : word) = Some W_28f04.
Proof. vm_refl. Qed.
Lemma D_28f04 : decode_any W_28f04 = Some (Jal 0 6308, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f08 : bv 32 := 0x00163613.
Lemma F_28f08 : fetch_word Ubsan.M.loaded_segments (0x28f08 : word) = Some W_28f08.
Proof. vm_refl. Qed.
Lemma D_28f08 : decode_any W_28f08 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f0c : bv 32 := 0x00c84633.
Lemma F_28f0c : fetch_word Ubsan.M.loaded_segments (0x28f0c : word) = Some W_28f0c.
Proof. vm_refl. Qed.
Lemma D_28f0c : decode_any W_28f0c = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f10 : bv 32 := 0x00061463.
Lemma F_28f10 : fetch_word Ubsan.M.loaded_segments (0x28f10 : word) = Some W_28f10.
Proof. vm_refl. Qed.
Lemma D_28f10 : decode_any W_28f10 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f14 : bv 32 := 0x0950106f.
Lemma F_28f14 : fetch_word Ubsan.M.loaded_segments (0x28f14 : word) = Some W_28f14.
Proof. vm_refl. Qed.
Lemma D_28f14 : decode_any W_28f14 = Some (Jal 0 6292, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f18 : bv 32 := 0x00049463.
Lemma F_28f18 : fetch_word Ubsan.M.loaded_segments (0x28f18 : word) = Some W_28f18.
Proof. vm_refl. Qed.
Lemma D_28f18 : decode_any W_28f18 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f1c : bv 32 := 0x08d0106f.
Lemma F_28f1c : fetch_word Ubsan.M.loaded_segments (0x28f1c : word) = Some W_28f1c.
Proof. vm_refl. Qed.
Lemma D_28f1c : decode_any W_28f1c = Some (Jal 0 6284, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f20 : bv 32 := 0x019f1463.
Lemma F_28f20 : fetch_word Ubsan.M.loaded_segments (0x28f20 : word) = Some W_28f20.
Proof. vm_refl. Qed.
Lemma D_28f20 : decode_any W_28f20 = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f24 : bv 32 := 0x0850106f.
Lemma F_28f24 : fetch_word Ubsan.M.loaded_segments (0x28f24 : word) = Some W_28f24.
Proof. vm_refl. Qed.
Lemma D_28f24 : decode_any W_28f24 = Some (Jal 0 6276, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f28 : bv 32 := 0x01b30633.
Lemma F_28f28 : fetch_word Ubsan.M.loaded_segments (0x28f28 : word) = Some W_28f28.
Proof. vm_refl. Qed.
Lemma D_28f28 : decode_any W_28f28 = Some (Op ALU_ADD 12 6 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f2c : bv 32 := 0x00cd7463.
Lemma F_28f2c : fetch_word Ubsan.M.loaded_segments (0x28f2c : word) = Some W_28f2c.
Proof. vm_refl. Qed.
Lemma D_28f2c : decode_any W_28f2c = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f30 : bv 32 := 0x0790106f.
Lemma F_28f30 : fetch_word Ubsan.M.loaded_segments (0x28f30 : word) = Some W_28f30.
Proof. vm_refl. Qed.
Lemma D_28f30 : decode_any W_28f30 = Some (Jal 0 6264, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f34 : bv 32 := 0x0089f463.
Lemma F_28f34 : fetch_word Ubsan.M.loaded_segments (0x28f34 : word) = Some W_28f34.
Proof. vm_refl. Qed.
Lemma D_28f34 : decode_any W_28f34 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f38 : bv 32 := 0x0710106f.
Lemma F_28f38 : fetch_word Ubsan.M.loaded_segments (0x28f38 : word) = Some W_28f38.
Proof. vm_refl. Qed.
Lemma D_28f38 : decode_any W_28f38 = Some (Jal 0 6256, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f3c : bv 32 := 0x01bc07b3.
Lemma F_28f3c : fetch_word Ubsan.M.loaded_segments (0x28f3c : word) = Some W_28f3c.
Proof. vm_refl. Qed.
Lemma D_28f3c : decode_any W_28f3c = Some (Op ALU_ADD 15 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f40 : bv 32 := 0x0127f463.
Lemma F_28f40 : fetch_word Ubsan.M.loaded_segments (0x28f40 : word) = Some W_28f40.
Proof. vm_refl. Qed.
Lemma D_28f40 : decode_any W_28f40 = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f44 : bv 32 := 0x0650106f.
Lemma F_28f44 : fetch_word Ubsan.M.loaded_segments (0x28f44 : word) = Some W_28f44.
Proof. vm_refl. Qed.
Lemma D_28f44 : decode_any W_28f44 = Some (Jal 0 6244, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f48 : bv 32 := 0x0017b793.
Lemma F_28f48 : fetch_word Ubsan.M.loaded_segments (0x28f48 : word) = Some W_28f48.
Proof. vm_refl. Qed.
Lemma D_28f48 : decode_any W_28f48 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f4c : bv 32 := 0x00fe47b3.
Lemma F_28f4c : fetch_word Ubsan.M.loaded_segments (0x28f4c : word) = Some W_28f4c.
Proof. vm_refl. Qed.
Lemma D_28f4c : decode_any W_28f4c = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f50 : bv 32 := 0x00079463.
Lemma F_28f50 : fetch_word Ubsan.M.loaded_segments (0x28f50 : word) = Some W_28f50.
Proof. vm_refl. Qed.
Lemma D_28f50 : decode_any W_28f50 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f54 : bv 32 := 0x0550106f.
Lemma F_28f54 : fetch_word Ubsan.M.loaded_segments (0x28f54 : word) = Some W_28f54.
Proof. vm_refl. Qed.
Lemma D_28f54 : decode_any W_28f54 = Some (Jal 0 6228, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f58 : bv 32 := 0x000a9463.
Lemma F_28f58 : fetch_word Ubsan.M.loaded_segments (0x28f58 : word) = Some W_28f58.
Proof. vm_refl. Qed.
Lemma D_28f58 : decode_any W_28f58 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f5c : bv 32 := 0x04d0106f.
Lemma F_28f5c : fetch_word Ubsan.M.loaded_segments (0x28f5c : word) = Some W_28f5c.
Proof. vm_refl. Qed.
Lemma D_28f5c : decode_any W_28f5c = Some (Jal 0 6220, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f60 : bv 32 := 0x00062783.
Lemma F_28f60 : fetch_word Ubsan.M.loaded_segments (0x28f60 : word) = Some W_28f60.
Proof. vm_refl. Qed.
Lemma D_28f60 : decode_any W_28f60 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f64 : bv 32 := 0x00462603.
Lemma F_28f64 : fetch_word Ubsan.M.loaded_segments (0x28f64 : word) = Some W_28f64.
Proof. vm_refl. Qed.
Lemma D_28f64 : decode_any W_28f64 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f68 : bv 32 := 0x01b908b3.
Lemma F_28f68 : fetch_word Ubsan.M.loaded_segments (0x28f68 : word) = Some W_28f68.
Proof. vm_refl. Qed.
Lemma D_28f68 : decode_any W_28f68 = Some (Op ALU_ADD 17 18 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f6c : bv 32 := 0x0008a083.
Lemma F_28f6c : fetch_word Ubsan.M.loaded_segments (0x28f6c : word) = Some W_28f6c.
Proof. vm_refl. Qed.
Lemma D_28f6c : decode_any W_28f6c = Some (Load SZ4 true 1 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f70 : bv 32 := 0x01d797bb.
Lemma F_28f70 : fetch_word Ubsan.M.loaded_segments (0x28f70 : word) = Some W_28f70.
Proof. vm_refl. Qed.
Lemma D_28f70 : decode_any W_28f70 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f74 : bv 32 := 0x0086563b.
Lemma F_28f74 : fetch_word Ubsan.M.loaded_segments (0x28f74 : word) = Some W_28f74.
Proof. vm_refl. Qed.
Lemma D_28f74 : decode_any W_28f74 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f78 : bv 32 := 0x00d7f7b3.
Lemma F_28f78 : fetch_word Ubsan.M.loaded_segments (0x28f78 : word) = Some W_28f78.
Proof. vm_refl. Qed.
Lemma D_28f78 : decode_any W_28f78 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f7c : bv 32 := 0x01f67633.
Lemma F_28f7c : fetch_word Ubsan.M.loaded_segments (0x28f7c : word) = Some W_28f7c.
Proof. vm_refl. Qed.
Lemma D_28f7c : decode_any W_28f7c = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f80 : bv 32 := 0x00f66633.
Lemma F_28f80 : fetch_word Ubsan.M.loaded_segments (0x28f80 : word) = Some W_28f80.
Proof. vm_refl. Qed.
Lemma D_28f80 : decode_any W_28f80 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f84 : bv 32 := 0x00166633.
Lemma F_28f84 : fetch_word Ubsan.M.loaded_segments (0x28f84 : word) = Some W_28f84.
Proof. vm_refl. Qed.
Lemma D_28f84 : decode_any W_28f84 = Some (Op ALU_OR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f88 : bv 32 := 0xfff64613.
Lemma F_28f88 : fetch_word Ubsan.M.loaded_segments (0x28f88 : word) = Some W_28f88.
Proof. vm_refl. Qed.
Lemma D_28f88 : decode_any W_28f88 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f8c : bv 32 := 0x004d8d93.
Lemma F_28f8c : fetch_word Ubsan.M.loaded_segments (0x28f8c : word) = Some W_28f8c.
Proof. vm_refl. Qed.
Lemma D_28f8c : decode_any W_28f8c = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f90 : bv 32 := 0x00c8a023.
Lemma F_28f90 : fetch_word Ubsan.M.loaded_segments (0x28f90 : word) = Some W_28f90.
Proof. vm_refl. Qed.
Lemma D_28f90 : decode_any W_28f90 = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f94 : bv 32 := 0xf7ba14e3.
Lemma F_28f94 : fetch_word Ubsan.M.loaded_segments (0x28f94 : word) = Some W_28f94.
Proof. vm_refl. Qed.
Lemma D_28f94 : decode_any W_28f94 = Some (Branch BC_NE 20 27 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f98 : bv 32 := 0x00590633.
Lemma F_28f98 : fetch_word Ubsan.M.loaded_segments (0x28f98 : word) = Some W_28f98.
Proof. vm_refl. Qed.
Lemma D_28f98 : decode_any W_28f98 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28f9c : bv 32 := 0x012037b3.
Lemma F_28f9c : fetch_word Ubsan.M.loaded_segments (0x28f9c : word) = Some W_28f9c.
Proof. vm_refl. Qed.
Lemma D_28f9c : decode_any W_28f9c = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fa0 : bv 32 := 0x00163813.
Lemma F_28fa0 : fetch_word Ubsan.M.loaded_segments (0x28fa0 : word) = Some W_28fa0.
Proof. vm_refl. Qed.
Lemma D_28fa0 : decode_any W_28fa0 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fa4 : bv 32 := 0x01079463.
Lemma F_28fa4 : fetch_word Ubsan.M.loaded_segments (0x28fa4 : word) = Some W_28fa4.
Proof. vm_refl. Qed.
Lemma D_28fa4 : decode_any W_28fa4 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fa8 : bv 32 := 0x0010106f.
Lemma F_28fa8 : fetch_word Ubsan.M.loaded_segments (0x28fa8 : word) = Some W_28fa8.
Proof. vm_refl. Qed.
Lemma D_28fa8 : decode_any W_28fa8 = Some (Jal 0 6144, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fac : bv 32 := 0x01263633.
Lemma F_28fac : fetch_word Ubsan.M.loaded_segments (0x28fac : word) = Some W_28fac.
Proof. vm_refl. Qed.
Lemma D_28fac : decode_any W_28fac = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fb0 : bv 32 := 0x01764633.
Lemma F_28fb0 : fetch_word Ubsan.M.loaded_segments (0x28fb0 : word) = Some W_28fb0.
Proof. vm_refl. Qed.
Lemma D_28fb0 : decode_any W_28fb0 = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fb4 : bv 32 := 0x00164613.
Lemma F_28fb4 : fetch_word Ubsan.M.loaded_segments (0x28fb4 : word) = Some W_28fb4.
Proof. vm_refl. Qed.
Lemma D_28fb4 : decode_any W_28fb4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fb8 : bv 32 := 0x00061463.
Lemma F_28fb8 : fetch_word Ubsan.M.loaded_segments (0x28fb8 : word) = Some W_28fb8.
Proof. vm_refl. Qed.
Lemma D_28fb8 : decode_any W_28fb8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fbc : bv 32 := 0x7ec0106f.
Lemma F_28fbc : fetch_word Ubsan.M.loaded_segments (0x28fbc : word) = Some W_28fbc.
Proof. vm_refl. Qed.
Lemma D_28fbc : decode_any W_28fbc = Some (Jal 0 6124, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fc0 : bv 32 := 0x00638633.
Lemma F_28fc0 : fetch_word Ubsan.M.loaded_segments (0x28fc0 : word) = Some W_28fc0.
Proof. vm_refl. Qed.
Lemma D_28fc0 : decode_any W_28fc0 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fc4 : bv 32 := 0x006037b3.
Lemma F_28fc4 : fetch_word Ubsan.M.loaded_segments (0x28fc4 : word) = Some W_28fc4.
Proof. vm_refl. Qed.
Lemma D_28fc4 : decode_any W_28fc4 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fc8 : bv 32 := 0x00163813.
Lemma F_28fc8 : fetch_word Ubsan.M.loaded_segments (0x28fc8 : word) = Some W_28fc8.
Proof. vm_refl. Qed.
Lemma D_28fc8 : decode_any W_28fc8 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fcc : bv 32 := 0x01079463.
Lemma F_28fcc : fetch_word Ubsan.M.loaded_segments (0x28fcc : word) = Some W_28fcc.
Proof. vm_refl. Qed.
Lemma D_28fcc : decode_any W_28fcc = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fd0 : bv 32 := 0x7d80106f.
Lemma F_28fd0 : fetch_word Ubsan.M.loaded_segments (0x28fd0 : word) = Some W_28fd0.
Proof. vm_refl. Qed.
Lemma D_28fd0 : decode_any W_28fd0 = Some (Jal 0 6104, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fd4 : bv 32 := 0x006637b3.
Lemma F_28fd4 : fetch_word Ubsan.M.loaded_segments (0x28fd4 : word) = Some W_28fd4.
Proof. vm_refl. Qed.
Lemma D_28fd4 : decode_any W_28fd4 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fd8 : bv 32 := 0x07813803.
Lemma F_28fd8 : fetch_word Ubsan.M.loaded_segments (0x28fd8 : word) = Some W_28fd8.
Proof. vm_refl. Qed.
Lemma D_28fd8 : decode_any W_28fd8 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fdc : bv 32 := 0x0107c7b3.
Lemma F_28fdc : fetch_word Ubsan.M.loaded_segments (0x28fdc : word) = Some W_28fdc.
Proof. vm_refl. Qed.
Lemma D_28fdc : decode_any W_28fdc = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fe0 : bv 32 := 0x0017c793.
Lemma F_28fe0 : fetch_word Ubsan.M.loaded_segments (0x28fe0 : word) = Some W_28fe0.
Proof. vm_refl. Qed.
Lemma D_28fe0 : decode_any W_28fe0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fe4 : bv 32 := 0x00079463.
Lemma F_28fe4 : fetch_word Ubsan.M.loaded_segments (0x28fe4 : word) = Some W_28fe4.
Proof. vm_refl. Qed.
Lemma D_28fe4 : decode_any W_28fe4 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fe8 : bv 32 := 0x7c00106f.
Lemma F_28fe8 : fetch_word Ubsan.M.loaded_segments (0x28fe8 : word) = Some W_28fe8.
Proof. vm_refl. Qed.
Lemma D_28fe8 : decode_any W_28fe8 = Some (Jal 0 6080, 4%Z).
Proof. vm_refl. Qed.

Definition W_28fec : bv 32 := 0x00590933.
Lemma F_28fec : fetch_word Ubsan.M.loaded_segments (0x28fec : word) = Some W_28fec.
Proof. vm_refl. Qed.
Lemma D_28fec : decode_any W_28fec = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ff0 : bv 32 := 0x0015859b.
Lemma F_28ff0 : fetch_word Ubsan.M.loaded_segments (0x28ff0 : word) = Some W_28ff0.
Proof. vm_refl. Qed.
Lemma D_28ff0 : decode_any W_28ff0 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ff4 : bv 32 := 0x005c0c33.
Lemma F_28ff4 : fetch_word Ubsan.M.loaded_segments (0x28ff4 : word) = Some W_28ff4.
Proof. vm_refl. Qed.
Lemma D_28ff4 : decode_any W_28ff4 = Some (Op ALU_ADD 24 24 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ff8 : bv 32 := 0x007b0b33.
Lemma F_28ff8 : fetch_word Ubsan.M.loaded_segments (0x28ff8 : word) = Some W_28ff8.
Proof. vm_refl. Qed.
Lemma D_28ff8 : decode_any W_28ff8 = Some (Op ALU_ADD 22 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_28ffc : bv 32 := 0x00060313.
Lemma F_28ffc : fetch_word Ubsan.M.loaded_segments (0x28ffc : word) = Some W_28ffc.
Proof. vm_refl. Qed.
Lemma D_28ffc : decode_any W_28ffc = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.
