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

Definition W_82000 : bv 32 := 0x000c2d03.
Lemma F_82000 : fetch_word Ubsan.M.loaded_segments (0x82000 : word) = Some W_82000.
Proof. vm_refl. Qed.
Lemma D_82000 : decode_any W_82000 = Some (Load SZ4 true 26 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82004 : bv 32 := 0x00032d83.
Lemma F_82004 : fetch_word Ubsan.M.loaded_segments (0x82004 : word) = Some W_82004.
Proof. vm_refl. Qed.
Lemma D_82004 : decode_any W_82004 = Some (Load SZ4 true 27 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82008 : bv 32 := 0xfffd4d13.
Lemma F_82008 : fetch_word Ubsan.M.loaded_segments (0x82008 : word) = Some W_82008.
Proof. vm_refl. Qed.
Lemma D_82008 : decode_any W_82008 = Some (OpImm ALU_XOR 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8200c : bv 32 := 0x01adfd33.
Lemma F_8200c : fetch_word Ubsan.M.loaded_segments (0x8200c : word) = Some W_8200c.
Proof. vm_refl. Qed.
Lemma D_8200c : decode_any W_8200c = Some (Op ALU_AND 26 27 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_82010 : bv 32 := 0x01ac2023.
Lemma F_82010 : fetch_word Ubsan.M.loaded_segments (0x82010 : word) = Some W_82010.
Proof. vm_refl. Qed.
Lemma D_82010 : decode_any W_82010 = Some (Store SZ4 24 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82014 : bv 32 := 0x4f846063.
Lemma F_82014 : fetch_word Ubsan.M.loaded_segments (0x82014 : word) = Some W_82014.
Proof. vm_refl. Qed.
Lemma D_82014 : decode_any W_82014 = Some (Branch BC_LTU 8 24 1248, 4%Z).
Proof. vm_refl. Qed.

Definition W_82018 : bv 32 := 0x4c646e63.
Lemma F_82018 : fetch_word Ubsan.M.loaded_segments (0x82018 : word) = Some W_82018.
Proof. vm_refl. Qed.
Lemma D_82018 : decode_any W_82018 = Some (Branch BC_LTU 8 6 1244, 4%Z).
Proof. vm_refl. Qed.

Definition W_8201c : bv 32 := 0x001b8b9b.
Lemma F_8201c : fetch_word Ubsan.M.loaded_segments (0x8201c : word) = Some W_8201c.
Proof. vm_refl. Qed.
Lemma D_8201c : decode_any W_8201c = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82020 : bv 32 := 0x00478793.
Lemma F_82020 : fetch_word Ubsan.M.loaded_segments (0x82020 : word) = Some W_82020.
Proof. vm_refl. Qed.
Lemma D_82020 : decode_any W_82020 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_82024 : bv 32 := 0xfc0b94e3.
Lemma F_82024 : fetch_word Ubsan.M.loaded_segments (0x82024 : word) = Some W_82024.
Proof. vm_refl. Qed.
Lemma D_82024 : decode_any W_82024 = Some (Branch BC_NE 23 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_82028 : bv 32 := 0x00f90933.
Lemma F_82028 : fetch_word Ubsan.M.loaded_segments (0x82028 : word) = Some W_82028.
Proof. vm_refl. Qed.
Lemma D_82028 : decode_any W_82028 = Some (Op ALU_ADD 18 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8202c : bv 32 := 0x00fb07b3.
Lemma F_8202c : fetch_word Ubsan.M.loaded_segments (0x8202c : word) = Some W_8202c.
Proof. vm_refl. Qed.
Lemma D_8202c : decode_any W_8202c = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82030 : bv 32 := 0xf0060ee3.
Lemma F_82030 : fetch_word Ubsan.M.loaded_segments (0x82030 : word) = Some W_82030.
Proof. vm_refl. Qed.
Lemma D_82030 : decode_any W_82030 = Some (Branch BC_EQ 12 0 7964, 4%Z).
Proof. vm_refl. Qed.

Definition W_82034 : bv 32 := 0x4c090063.
Lemma F_82034 : fetch_word Ubsan.M.loaded_segments (0x82034 : word) = Some W_82034.
Proof. vm_refl. Qed.
Lemma D_82034 : decode_any W_82034 = Some (Branch BC_EQ 18 0 1216, 4%Z).
Proof. vm_refl. Qed.

Definition W_82038 : bv 32 := 0x00397313.
Lemma F_82038 : fetch_word Ubsan.M.loaded_segments (0x82038 : word) = Some W_82038.
Proof. vm_refl. Qed.
Lemma D_82038 : decode_any W_82038 = Some (OpImm ALU_AND 6 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8203c : bv 32 := 0x4a031c63.
Lemma F_8203c : fetch_word Ubsan.M.loaded_segments (0x8203c : word) = Some W_8203c.
Proof. vm_refl. Qed.
Lemma D_8203c : decode_any W_8203c = Some (Branch BC_NE 6 0 1208, 4%Z).
Proof. vm_refl. Qed.

Definition W_82040 : bv 32 := 0x4a078a63.
Lemma F_82040 : fetch_word Ubsan.M.loaded_segments (0x82040 : word) = Some W_82040.
Proof. vm_refl. Qed.
Lemma D_82040 : decode_any W_82040 = Some (Branch BC_EQ 15 0 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_82044 : bv 32 := 0x0037f313.
Lemma F_82044 : fetch_word Ubsan.M.loaded_segments (0x82044 : word) = Some W_82044.
Proof. vm_refl. Qed.
Lemma D_82044 : decode_any W_82044 = Some (OpImm ALU_AND 6 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82048 : bv 32 := 0x4a031663.
Lemma F_82048 : fetch_word Ubsan.M.loaded_segments (0x82048 : word) = Some W_82048.
Proof. vm_refl. Qed.
Lemma D_82048 : decode_any W_82048 = Some (Branch BC_NE 6 0 1196, 4%Z).
Proof. vm_refl. Qed.

Definition W_8204c : bv 32 := 0x00092303.
Lemma F_8204c : fetch_word Ubsan.M.loaded_segments (0x8204c : word) = Some W_8204c.
Proof. vm_refl. Qed.
Lemma D_8204c : decode_any W_8204c = Some (Load SZ4 true 6 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82050 : bv 32 := 0x0007a783.
Lemma F_82050 : fetch_word Ubsan.M.loaded_segments (0x82050 : word) = Some W_82050.
Proof. vm_refl. Qed.
Lemma D_82050 : decode_any W_82050 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82054 : bv 32 := 0x01437b33.
Lemma F_82054 : fetch_word Ubsan.M.loaded_segments (0x82054 : word) = Some W_82054.
Proof. vm_refl. Qed.
Lemma D_82054 : decode_any W_82054 = Some (Op ALU_AND 22 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82058 : bv 32 := 0xfff34313.
Lemma F_82058 : fetch_word Ubsan.M.loaded_segments (0x82058 : word) = Some W_82058.
Proof. vm_refl. Qed.
Lemma D_82058 : decode_any W_82058 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8205c : bv 32 := 0x01c7f7b3.
Lemma F_8205c : fetch_word Ubsan.M.loaded_segments (0x8205c : word) = Some W_8205c.
Proof. vm_refl. Qed.
Lemma D_8205c : decode_any W_8205c = Some (Op ALU_AND 15 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82060 : bv 32 := 0x0067f7b3.
Lemma F_82060 : fetch_word Ubsan.M.loaded_segments (0x82060 : word) = Some W_82060.
Proof. vm_refl. Qed.
Lemma D_82060 : decode_any W_82060 = Some (Op ALU_AND 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82064 : bv 32 := 0x0167e7b3.
Lemma F_82064 : fetch_word Ubsan.M.loaded_segments (0x82064 : word) = Some W_82064.
Proof. vm_refl. Qed.
Lemma D_82064 : decode_any W_82064 = Some (Op ALU_OR 15 15 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82068 : bv 32 := 0x00f92023.
Lemma F_82068 : fetch_word Ubsan.M.loaded_segments (0x82068 : word) = Some W_82068.
Proof. vm_refl. Qed.
Lemma D_82068 : decode_any W_82068 = Some (Store SZ4 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8206c : bv 32 := 0xee1ff06f.
Lemma F_8206c : fetch_word Ubsan.M.loaded_segments (0x8206c : word) = Some W_8206c.
Proof. vm_refl. Qed.
Lemma D_8206c : decode_any W_8206c = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_82070 : bv 32 := 0x00000593.
Lemma F_82070 : fetch_word Ubsan.M.loaded_segments (0x82070 : word) = Some W_82070.
Proof. vm_refl. Qed.
Lemma D_82070 : decode_any W_82070 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82074 : bv 32 := 0x00000693.
Lemma F_82074 : fetch_word Ubsan.M.loaded_segments (0x82074 : word) = Some W_82074.
Proof. vm_refl. Qed.
Lemma D_82074 : decode_any W_82074 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82078 : bv 32 := 0x00000c93.
Lemma F_82078 : fetch_word Ubsan.M.loaded_segments (0x82078 : word) = Some W_82078.
Proof. vm_refl. Qed.
Lemma D_82078 : decode_any W_82078 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8207c : bv 32 := 0x015a07b3.
Lemma F_8207c : fetch_word Ubsan.M.loaded_segments (0x8207c : word) = Some W_8207c.
Proof. vm_refl. Qed.
Lemma D_8207c : decode_any W_8207c = Some (Op ALU_ADD 15 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_82080 : bv 32 := 0xfffe4a13.
Lemma F_82080 : fetch_word Ubsan.M.loaded_segments (0x82080 : word) = Some W_82080.
Proof. vm_refl. Qed.
Lemma D_82080 : decode_any W_82080 = Some (OpImm ALU_XOR 20 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82084 : bv 32 := 0x016b8b33.
Lemma F_82084 : fetch_word Ubsan.M.loaded_segments (0x82084 : word) = Some W_82084.
Proof. vm_refl. Qed.
Lemma D_82084 : decode_any W_82084 = Some (Op ALU_ADD 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82088 : bv 32 := 0x0039fa93.
Lemma F_82088 : fetch_word Ubsan.M.loaded_segments (0x82088 : word) = Some W_82088.
Proof. vm_refl. Qed.
Lemma D_82088 : decode_any W_82088 = Some (OpImm ALU_AND 21 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8208c : bv 32 := 0x00890433.
Lemma F_8208c : fetch_word Ubsan.M.loaded_segments (0x8208c : word) = Some W_8208c.
Proof. vm_refl. Qed.
Lemma D_8208c : decode_any W_8208c = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82090 : bv 32 := 0x43ffd313.
Lemma F_82090 : fetch_word Ubsan.M.loaded_segments (0x82090 : word) = Some W_82090.
Proof. vm_refl. Qed.
Lemma D_82090 : decode_any W_82090 = Some (ShiftImm ALU_SRA 6 31 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82094 : bv 32 := 0x01f37333.
Lemma F_82094 : fetch_word Ubsan.M.loaded_segments (0x82094 : word) = Some W_82094.
Proof. vm_refl. Qed.
Lemma D_82094 : decode_any W_82094 = Some (Op ALU_AND 6 6 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82098 : bv 32 := 0x00357f93.
Lemma F_82098 : fetch_word Ubsan.M.loaded_segments (0x82098 : word) = Some W_82098.
Proof. vm_refl. Qed.
Lemma D_82098 : decode_any W_82098 = Some (OpImm ALU_AND 31 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8209c : bv 32 := 0x41be893b.
Lemma F_8209c : fetch_word Ubsan.M.loaded_segments (0x8209c : word) = Some W_8209c.
Proof. vm_refl. Qed.
Lemma D_8209c : decode_any W_8209c = Some (Op32 ALU_SUB 18 29 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_820a0 : bv 32 := 0x41e787bb.
Lemma F_820a0 : fetch_word Ubsan.M.loaded_segments (0x820a0 : word) = Some W_820a0.
Proof. vm_refl. Qed.
Lemma D_820a0 : decode_any W_820a0 = Some (Op32 ALU_SUB 15 15 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_820a4 : bv 32 := 0x02000f13.
Lemma F_820a4 : fetch_word Ubsan.M.loaded_segments (0x820a4 : word) = Some W_820a4.
Proof. vm_refl. Qed.
Lemma D_820a4 : decode_any W_820a4 = Some (OpImm ALU_ADD 30 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_820a8 : bv 32 := 0x01650533.
Lemma F_820a8 : fetch_word Ubsan.M.loaded_segments (0x820a8 : word) = Some W_820a8.
Proof. vm_refl. Qed.
Lemma D_820a8 : decode_any W_820a8 = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_820ac : bv 32 := 0x008989b3.
Lemma F_820ac : fetch_word Ubsan.M.loaded_segments (0x820ac : word) = Some W_820ac.
Proof. vm_refl. Qed.
Lemma D_820ac : decode_any W_820ac = Some (Op ALU_ADD 19 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_820b0 : bv 32 := 0x006787b3.
Lemma F_820b0 : fetch_word Ubsan.M.loaded_segments (0x820b0 : word) = Some W_820b0.
Proof. vm_refl. Qed.
Lemma D_820b0 : decode_any W_820b0 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_820b4 : bv 32 := 0x41d787bb.
Lemma F_820b4 : fetch_word Ubsan.M.loaded_segments (0x820b4 : word) = Some W_820b4.
Proof. vm_refl. Qed.
Lemma D_820b4 : decode_any W_820b4 = Some (Op32 ALU_SUB 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_820b8 : bv 32 := 0x43f7d313.
Lemma F_820b8 : fetch_word Ubsan.M.loaded_segments (0x820b8 : word) = Some W_820b8.
Proof. vm_refl. Qed.
Lemma D_820b8 : decode_any W_820b8 = Some (ShiftImm ALU_SRA 6 15 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_820bc : bv 32 := 0x00f377b3.
Lemma F_820bc : fetch_word Ubsan.M.loaded_segments (0x820bc : word) = Some W_820bc.
Proof. vm_refl. Qed.
Lemma D_820bc : decode_any W_820bc = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_820c0 : bv 32 := 0x00f907b3.
Lemma F_820c0 : fetch_word Ubsan.M.loaded_segments (0x820c0 : word) = Some W_820c0.
Proof. vm_refl. Qed.
Lemma D_820c0 : decode_any W_820c0 = Some (Op ALU_ADD 15 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_820c4 : bv 32 := 0x0057d79b.
Lemma F_820c4 : fetch_word Ubsan.M.loaded_segments (0x820c4 : word) = Some W_820c4.
Proof. vm_refl. Qed.
Lemma D_820c4 : decode_any W_820c4 = Some (ShiftImm32 ALU_SRL 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_820c8 : bv 32 := 0x40f00eb3.
Lemma F_820c8 : fetch_word Ubsan.M.loaded_segments (0x820c8 : word) = Some W_820c8.
Proof. vm_refl. Qed.
Lemma D_820c8 : decode_any W_820c8 = Some (Op ALU_SUB 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_820cc : bv 32 := 0xffb00413.
Lemma F_820cc : fetch_word Ubsan.M.loaded_segments (0x820cc : word) = Some W_820cc.
Proof. vm_refl. Qed.
Lemma D_820cc : decode_any W_820cc = Some (OpImm ALU_ADD 8 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_820d0 : bv 32 := 0x05813083.
Lemma F_820d0 : fetch_word Ubsan.M.loaded_segments (0x820d0 : word) = Some W_820d0.
Proof. vm_refl. Qed.
Lemma D_820d0 : decode_any W_820d0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_820d4 : bv 32 := 0x01c0006f.
Lemma F_820d4 : fetch_word Ubsan.M.loaded_segments (0x820d4 : word) = Some W_820d4.
Proof. vm_refl. Qed.
Lemma D_820d4 : decode_any W_820d4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_820d8 : bv 32 := 0x001c8c9b.
Lemma F_820d8 : fetch_word Ubsan.M.loaded_segments (0x820d8 : word) = Some W_820d8.
Proof. vm_refl. Qed.
Lemma D_820d8 : decode_any W_820d8 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_820dc : bv 32 := 0x00e686bb.
Lemma F_820dc : fetch_word Ubsan.M.loaded_segments (0x820dc : word) = Some W_820dc.
Proof. vm_refl. Qed.
Lemma D_820dc : decode_any W_820dc = Some (Op32 ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_820e0 : bv 32 := 0x001585bb.
Lemma F_820e0 : fetch_word Ubsan.M.loaded_segments (0x820e0 : word) = Some W_820e0.
Proof. vm_refl. Qed.
Lemma D_820e0 : decode_any W_820e0 = Some (Op32 ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_820e4 : bv 32 := 0x08013783.
Lemma F_820e4 : fetch_word Ubsan.M.loaded_segments (0x820e4 : word) = Some W_820e4.
Proof. vm_refl. Qed.
Lemma D_820e4 : decode_any W_820e4 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_820e8 : bv 32 := 0x00fc9463.
Lemma F_820e8 : fetch_word Ubsan.M.loaded_segments (0x820e8 : word) = Some W_820e8.
Proof. vm_refl. Qed.
Lemma D_820e8 : decode_any W_820e8 = Some (Branch BC_NE 25 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_820ec : bv 32 := 0x4cc0506f.
Lemma F_820ec : fetch_word Ubsan.M.loaded_segments (0x820ec : word) = Some W_820ec.
Proof. vm_refl. Qed.
Lemma D_820ec : decode_any W_820ec = Some (Jal 0 21708, 4%Z).
Proof. vm_refl. Qed.

Definition W_820f0 : bv 32 := 0x021c8333.
Lemma F_820f0 : fetch_word Ubsan.M.loaded_segments (0x820f0 : word) = Some W_820f0.
Proof. vm_refl. Qed.
Lemma D_820f0 : decode_any W_820f0 = Some (Mul M_MUL 6 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_820f4 : bv 32 := 0x021c87bb.
Lemma F_820f4 : fetch_word Ubsan.M.loaded_segments (0x820f4 : word) = Some W_820f4.
Proof. vm_refl. Qed.
Lemma D_820f4 : decode_any W_820f4 = Some (Mul32 M_MUL 15 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_820f8 : bv 32 := 0x3e679e63.
Lemma F_820f8 : fetch_word Ubsan.M.loaded_segments (0x820f8 : word) = Some W_820f8.
Proof. vm_refl. Qed.
Lemma D_820f8 : decode_any W_820f8 = Some (Branch BC_NE 15 6 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_820fc : bv 32 := 0x0003031b.
Lemma F_820fc : fetch_word Ubsan.M.loaded_segments (0x820fc : word) = Some W_820fc.
Proof. vm_refl. Qed.
Lemma D_820fc : decode_any W_820fc = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82100 : bv 32 := 0x00231793.
Lemma F_82100 : fetch_word Ubsan.M.loaded_segments (0x82100 : word) = Some W_82100.
Proof. vm_refl. Qed.
Lemma D_82100 : decode_any W_82100 = Some (ShiftImm ALU_SLL 15 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82104 : bv 32 := 0x00f887b3.
Lemma F_82104 : fetch_word Ubsan.M.loaded_segments (0x82104 : word) = Some W_82104.
Proof. vm_refl. Qed.
Lemma D_82104 : decode_any W_82104 = Some (Op ALU_ADD 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82108 : bv 32 := 0x0017b913.
Lemma F_82108 : fetch_word Ubsan.M.loaded_segments (0x82108 : word) = Some W_82108.
Proof. vm_refl. Qed.
Lemma D_82108 : decode_any W_82108 = Some (OpImm ALU_SLTU 18 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8210c : bv 32 := 0x3f280463.
Lemma F_8210c : fetch_word Ubsan.M.loaded_segments (0x8210c : word) = Some W_8210c.
Proof. vm_refl. Qed.
Lemma D_8210c : decode_any W_8210c = Some (Branch BC_EQ 16 18 1000, 4%Z).
Proof. vm_refl. Qed.

Definition W_82110 : bv 32 := 0x0117b933.
Lemma F_82110 : fetch_word Ubsan.M.loaded_segments (0x82110 : word) = Some W_82110.
Proof. vm_refl. Qed.
Lemma D_82110 : decode_any W_82110 = Some (Op ALU_SLTU 18 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82114 : bv 32 := 0x00032313.
Lemma F_82114 : fetch_word Ubsan.M.loaded_segments (0x82114 : word) = Some W_82114.
Proof. vm_refl. Qed.
Lemma D_82114 : decode_any W_82114 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82118 : bv 32 := 0x00694333.
Lemma F_82118 : fetch_word Ubsan.M.loaded_segments (0x82118 : word) = Some W_82118.
Proof. vm_refl. Qed.
Lemma D_82118 : decode_any W_82118 = Some (Op ALU_XOR 6 18 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8211c : bv 32 := 0x00134313.
Lemma F_8211c : fetch_word Ubsan.M.loaded_segments (0x8211c : word) = Some W_8211c.
Proof. vm_refl. Qed.
Lemma D_8211c : decode_any W_8211c = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82120 : bv 32 := 0x3c030a63.
Lemma F_82120 : fetch_word Ubsan.M.loaded_segments (0x82120 : word) = Some W_82120.
Proof. vm_refl. Qed.
Lemma D_82120 : decode_any W_82120 = Some (Branch BC_EQ 6 0 980, 4%Z).
Proof. vm_refl. Qed.

Definition W_82124 : bv 32 := 0x02ec8333.
Lemma F_82124 : fetch_word Ubsan.M.loaded_segments (0x82124 : word) = Some W_82124.
Proof. vm_refl. Qed.
Lemma D_82124 : decode_any W_82124 = Some (Mul M_MUL 6 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82128 : bv 32 := 0x02ec893b.
Lemma F_82128 : fetch_word Ubsan.M.loaded_segments (0x82128 : word) = Some W_82128.
Proof. vm_refl. Qed.
Lemma D_82128 : decode_any W_82128 = Some (Mul32 M_MUL 18 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8212c : bv 32 := 0x3c691463.
Lemma F_8212c : fetch_word Ubsan.M.loaded_segments (0x8212c : word) = Some W_8212c.
Proof. vm_refl. Qed.
Lemma D_8212c : decode_any W_8212c = Some (Branch BC_NE 18 6 968, 4%Z).
Proof. vm_refl. Qed.

Definition W_82130 : bv 32 := 0x0003031b.
Lemma F_82130 : fetch_word Ubsan.M.loaded_segments (0x82130 : word) = Some W_82130.
Proof. vm_refl. Qed.
Lemma D_82130 : decode_any W_82130 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82134 : bv 32 := 0x00231913.
Lemma F_82134 : fetch_word Ubsan.M.loaded_segments (0x82134 : word) = Some W_82134.
Proof. vm_refl. Qed.
Lemma D_82134 : decode_any W_82134 = Some (ShiftImm ALU_SLL 18 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82138 : bv 32 := 0x00790933.
Lemma F_82138 : fetch_word Ubsan.M.loaded_segments (0x82138 : word) = Some W_82138.
Proof. vm_refl. Qed.
Lemma D_82138 : decode_any W_82138 = Some (Op ALU_ADD 18 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8213c : bv 32 := 0x00193b13.
Lemma F_8213c : fetch_word Ubsan.M.loaded_segments (0x8213c : word) = Some W_8213c.
Proof. vm_refl. Qed.
Lemma D_8213c : decode_any W_8213c = Some (OpImm ALU_SLTU 22 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82140 : bv 32 := 0x3b628a63.
Lemma F_82140 : fetch_word Ubsan.M.loaded_segments (0x82140 : word) = Some W_82140.
Proof. vm_refl. Qed.
Lemma D_82140 : decode_any W_82140 = Some (Branch BC_EQ 5 22 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_82144 : bv 32 := 0x00793b33.
Lemma F_82144 : fetch_word Ubsan.M.loaded_segments (0x82144 : word) = Some W_82144.
Proof. vm_refl. Qed.
Lemma D_82144 : decode_any W_82144 = Some (Op ALU_SLTU 22 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82148 : bv 32 := 0x00032313.
Lemma F_82148 : fetch_word Ubsan.M.loaded_segments (0x82148 : word) = Some W_82148.
Proof. vm_refl. Qed.
Lemma D_82148 : decode_any W_82148 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8214c : bv 32 := 0x006b4333.
Lemma F_8214c : fetch_word Ubsan.M.loaded_segments (0x8214c : word) = Some W_8214c.
Proof. vm_refl. Qed.
Lemma D_8214c : decode_any W_8214c = Some (Op ALU_XOR 6 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82150 : bv 32 := 0x00134313.
Lemma F_82150 : fetch_word Ubsan.M.loaded_segments (0x82150 : word) = Some W_82150.
Proof. vm_refl. Qed.
Lemma D_82150 : decode_any W_82150 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82154 : bv 32 := 0x3a030063.
Lemma F_82154 : fetch_word Ubsan.M.loaded_segments (0x82154 : word) = Some W_82154.
Proof. vm_refl. Qed.
Lemma D_82154 : decode_any W_82154 = Some (Branch BC_EQ 6 0 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_82158 : bv 32 := 0x07e4e063.
Lemma F_82158 : fetch_word Ubsan.M.loaded_segments (0x82158 : word) = Some W_82158.
Proof. vm_refl. Qed.
Lemma D_82158 : decode_any W_82158 = Some (Branch BC_LTU 9 30 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8215c : bv 32 := 0x380a9c63.
Lemma F_8215c : fetch_word Ubsan.M.loaded_segments (0x8215c : word) = Some W_8215c.
Proof. vm_refl. Qed.
Lemma D_8215c : decode_any W_8215c = Some (Branch BC_NE 21 0 920, 4%Z).
Proof. vm_refl. Qed.

Definition W_82160 : bv 32 := 0x00000793.
Lemma F_82160 : fetch_word Ubsan.M.loaded_segments (0x82160 : word) = Some W_82160.
Proof. vm_refl. Qed.
Lemma D_82160 : decode_any W_82160 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82164 : bv 32 := 0x00269913.
Lemma F_82164 : fetch_word Ubsan.M.loaded_segments (0x82164 : word) = Some W_82164.
Proof. vm_refl. Qed.
Lemma D_82164 : decode_any W_82164 = Some (ShiftImm ALU_SLL 18 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82168 : bv 32 := 0x00259b13.
Lemma F_82168 : fetch_word Ubsan.M.loaded_segments (0x82168 : word) = Some W_82168.
Proof. vm_refl. Qed.
Lemma D_82168 : decode_any W_82168 = Some (ShiftImm ALU_SLL 22 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8216c : bv 32 := 0x01250933.
Lemma F_8216c : fetch_word Ubsan.M.loaded_segments (0x8216c : word) = Some W_8216c.
Proof. vm_refl. Qed.
Lemma D_8216c : decode_any W_8216c = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82170 : bv 32 := 0x01698b33.
Lemma F_82170 : fetch_word Ubsan.M.loaded_segments (0x82170 : word) = Some W_82170.
Proof. vm_refl. Qed.
Lemma D_82170 : decode_any W_82170 = Some (Op ALU_ADD 22 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82174 : bv 32 := 0x000e8b93.
Lemma F_82174 : fetch_word Ubsan.M.loaded_segments (0x82174 : word) = Some W_82174.
Proof. vm_refl. Qed.
Lemma D_82174 : decode_any W_82174 = Some (OpImm ALU_ADD 23 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82178 : bv 32 := 0x00fb0333.
Lemma F_82178 : fetch_word Ubsan.M.loaded_segments (0x82178 : word) = Some W_82178.
Proof. vm_refl. Qed.
Lemma D_82178 : decode_any W_82178 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8217c : bv 32 := 0x36030c63.
Lemma F_8217c : fetch_word Ubsan.M.loaded_segments (0x8217c : word) = Some W_8217c.
Proof. vm_refl. Qed.
Lemma D_8217c : decode_any W_8217c = Some (Branch BC_EQ 6 0 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_82180 : bv 32 := 0x360f9a63.
Lemma F_82180 : fetch_word Ubsan.M.loaded_segments (0x82180 : word) = Some W_82180.
Proof. vm_refl. Qed.
Lemma D_82180 : decode_any W_82180 = Some (Branch BC_NE 31 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_82184 : bv 32 := 0x00f90c33.
Lemma F_82184 : fetch_word Ubsan.M.loaded_segments (0x82184 : word) = Some W_82184.
Proof. vm_refl. Qed.
Lemma D_82184 : decode_any W_82184 = Some (Op ALU_ADD 24 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82188 : bv 32 := 0x360c0663.
Lemma F_82188 : fetch_word Ubsan.M.loaded_segments (0x82188 : word) = Some W_82188.
Proof. vm_refl. Qed.
Lemma D_82188 : decode_any W_82188 = Some (Branch BC_EQ 24 0 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_8218c : bv 32 := 0x00032d03.
Lemma F_8218c : fetch_word Ubsan.M.loaded_segments (0x8218c : word) = Some W_8218c.
Proof. vm_refl. Qed.
Lemma D_8218c : decode_any W_8218c = Some (Load SZ4 true 26 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82190 : bv 32 := 0x000c2d83.
Lemma F_82190 : fetch_word Ubsan.M.loaded_segments (0x82190 : word) = Some W_82190.
Proof. vm_refl. Qed.
Lemma D_82190 : decode_any W_82190 = Some (Load SZ4 true 27 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82194 : bv 32 := 0x01adcd33.
Lemma F_82194 : fetch_word Ubsan.M.loaded_segments (0x82194 : word) = Some W_82194.
Proof. vm_refl. Qed.
Lemma D_82194 : decode_any W_82194 = Some (Op ALU_XOR 26 27 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_82198 : bv 32 := 0x01ac2023.
Lemma F_82198 : fetch_word Ubsan.M.loaded_segments (0x82198 : word) = Some W_82198.
Proof. vm_refl. Qed.
Lemma D_82198 : decode_any W_82198 = Some (Store SZ4 24 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8219c : bv 32 := 0x35846c63.
Lemma F_8219c : fetch_word Ubsan.M.loaded_segments (0x8219c : word) = Some W_8219c.
Proof. vm_refl. Qed.
Lemma D_8219c : decode_any W_8219c = Some (Branch BC_LTU 8 24 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_821a0 : bv 32 := 0x34646a63.
Lemma F_821a0 : fetch_word Ubsan.M.loaded_segments (0x821a0 : word) = Some W_821a0.
Proof. vm_refl. Qed.
Lemma D_821a0 : decode_any W_821a0 = Some (Branch BC_LTU 8 6 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_821a4 : bv 32 := 0x001b8b9b.
Lemma F_821a4 : fetch_word Ubsan.M.loaded_segments (0x821a4 : word) = Some W_821a4.
Proof. vm_refl. Qed.
Lemma D_821a4 : decode_any W_821a4 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_821a8 : bv 32 := 0x00478793.
Lemma F_821a8 : fetch_word Ubsan.M.loaded_segments (0x821a8 : word) = Some W_821a8.
Proof. vm_refl. Qed.
Lemma D_821a8 : decode_any W_821a8 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_821ac : bv 32 := 0xfc0b96e3.
Lemma F_821ac : fetch_word Ubsan.M.loaded_segments (0x821ac : word) = Some W_821ac.
Proof. vm_refl. Qed.
Lemma D_821ac : decode_any W_821ac = Some (Branch BC_NE 23 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_821b0 : bv 32 := 0x00f90933.
Lemma F_821b0 : fetch_word Ubsan.M.loaded_segments (0x821b0 : word) = Some W_821b0.
Proof. vm_refl. Qed.
Lemma D_821b0 : decode_any W_821b0 = Some (Op ALU_ADD 18 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_821b4 : bv 32 := 0x00fb07b3.
Lemma F_821b4 : fetch_word Ubsan.M.loaded_segments (0x821b4 : word) = Some W_821b4.
Proof. vm_refl. Qed.
Lemma D_821b4 : decode_any W_821b4 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_821b8 : bv 32 := 0xf20600e3.
Lemma F_821b8 : fetch_word Ubsan.M.loaded_segments (0x821b8 : word) = Some W_821b8.
Proof. vm_refl. Qed.
Lemma D_821b8 : decode_any W_821b8 = Some (Branch BC_EQ 12 0 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_821bc : bv 32 := 0x32090c63.
Lemma F_821bc : fetch_word Ubsan.M.loaded_segments (0x821bc : word) = Some W_821bc.
Proof. vm_refl. Qed.
Lemma D_821bc : decode_any W_821bc = Some (Branch BC_EQ 18 0 824, 4%Z).
Proof. vm_refl. Qed.

Definition W_821c0 : bv 32 := 0x00397313.
Lemma F_821c0 : fetch_word Ubsan.M.loaded_segments (0x821c0 : word) = Some W_821c0.
Proof. vm_refl. Qed.
Lemma D_821c0 : decode_any W_821c0 = Some (OpImm ALU_AND 6 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_821c4 : bv 32 := 0x32031863.
Lemma F_821c4 : fetch_word Ubsan.M.loaded_segments (0x821c4 : word) = Some W_821c4.
Proof. vm_refl. Qed.
Lemma D_821c4 : decode_any W_821c4 = Some (Branch BC_NE 6 0 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_821c8 : bv 32 := 0x32078663.
Lemma F_821c8 : fetch_word Ubsan.M.loaded_segments (0x821c8 : word) = Some W_821c8.
Proof. vm_refl. Qed.
Lemma D_821c8 : decode_any W_821c8 = Some (Branch BC_EQ 15 0 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_821cc : bv 32 := 0x0037f313.
Lemma F_821cc : fetch_word Ubsan.M.loaded_segments (0x821cc : word) = Some W_821cc.
Proof. vm_refl. Qed.
Lemma D_821cc : decode_any W_821cc = Some (OpImm ALU_AND 6 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_821d0 : bv 32 := 0x32031263.
Lemma F_821d0 : fetch_word Ubsan.M.loaded_segments (0x821d0 : word) = Some W_821d0.
Proof. vm_refl. Qed.
Lemma D_821d0 : decode_any W_821d0 = Some (Branch BC_NE 6 0 804, 4%Z).
Proof. vm_refl. Qed.

Definition W_821d4 : bv 32 := 0x00092303.
Lemma F_821d4 : fetch_word Ubsan.M.loaded_segments (0x821d4 : word) = Some W_821d4.
Proof. vm_refl. Qed.
Lemma D_821d4 : decode_any W_821d4 = Some (Load SZ4 true 6 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821d8 : bv 32 := 0x0007a783.
Lemma F_821d8 : fetch_word Ubsan.M.loaded_segments (0x821d8 : word) = Some W_821d8.
Proof. vm_refl. Qed.
Lemma D_821d8 : decode_any W_821d8 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821dc : bv 32 := 0x01437b33.
Lemma F_821dc : fetch_word Ubsan.M.loaded_segments (0x821dc : word) = Some W_821dc.
Proof. vm_refl. Qed.
Lemma D_821dc : decode_any W_821dc = Some (Op ALU_AND 22 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_821e0 : bv 32 := 0x0067c7b3.
Lemma F_821e0 : fetch_word Ubsan.M.loaded_segments (0x821e0 : word) = Some W_821e0.
Proof. vm_refl. Qed.
Lemma D_821e0 : decode_any W_821e0 = Some (Op ALU_XOR 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_821e4 : bv 32 := 0x01c7f7b3.
Lemma F_821e4 : fetch_word Ubsan.M.loaded_segments (0x821e4 : word) = Some W_821e4.
Proof. vm_refl. Qed.
Lemma D_821e4 : decode_any W_821e4 = Some (Op ALU_AND 15 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_821e8 : bv 32 := 0x0167e7b3.
Lemma F_821e8 : fetch_word Ubsan.M.loaded_segments (0x821e8 : word) = Some W_821e8.
Proof. vm_refl. Qed.
Lemma D_821e8 : decode_any W_821e8 = Some (Op ALU_OR 15 15 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_821ec : bv 32 := 0x00f92023.
Lemma F_821ec : fetch_word Ubsan.M.loaded_segments (0x821ec : word) = Some W_821ec.
Proof. vm_refl. Qed.
Lemma D_821ec : decode_any W_821ec = Some (Store SZ4 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f0 : bv 32 := 0xee9ff06f.
Lemma F_821f0 : fetch_word Ubsan.M.loaded_segments (0x821f0 : word) = Some W_821f0.
Proof. vm_refl. Qed.
Lemma D_821f0 : decode_any W_821f0 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f4 : bv 32 := 0x00000593.
Lemma F_821f4 : fetch_word Ubsan.M.loaded_segments (0x821f4 : word) = Some W_821f4.
Proof. vm_refl. Qed.
Lemma D_821f4 : decode_any W_821f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f8 : bv 32 := 0x00000693.
Lemma F_821f8 : fetch_word Ubsan.M.loaded_segments (0x821f8 : word) = Some W_821f8.
Proof. vm_refl. Qed.
Lemma D_821f8 : decode_any W_821f8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821fc : bv 32 := 0x00000c93.
Lemma F_821fc : fetch_word Ubsan.M.loaded_segments (0x821fc : word) = Some W_821fc.
Proof. vm_refl. Qed.
Lemma D_821fc : decode_any W_821fc = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82200 : bv 32 := 0x015a07b3.
Lemma F_82200 : fetch_word Ubsan.M.loaded_segments (0x82200 : word) = Some W_82200.
Proof. vm_refl. Qed.
Lemma D_82200 : decode_any W_82200 = Some (Op ALU_ADD 15 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_82204 : bv 32 := 0xfffe4a13.
Lemma F_82204 : fetch_word Ubsan.M.loaded_segments (0x82204 : word) = Some W_82204.
Proof. vm_refl. Qed.
Lemma D_82204 : decode_any W_82204 = Some (OpImm ALU_XOR 20 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82208 : bv 32 := 0x016b8b33.
Lemma F_82208 : fetch_word Ubsan.M.loaded_segments (0x82208 : word) = Some W_82208.
Proof. vm_refl. Qed.
Lemma D_82208 : decode_any W_82208 = Some (Op ALU_ADD 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8220c : bv 32 := 0x0039fa93.
Lemma F_8220c : fetch_word Ubsan.M.loaded_segments (0x8220c : word) = Some W_8220c.
Proof. vm_refl. Qed.
Lemma D_8220c : decode_any W_8220c = Some (OpImm ALU_AND 21 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82210 : bv 32 := 0x00890433.
Lemma F_82210 : fetch_word Ubsan.M.loaded_segments (0x82210 : word) = Some W_82210.
Proof. vm_refl. Qed.
Lemma D_82210 : decode_any W_82210 = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82214 : bv 32 := 0x43ffd313.
Lemma F_82214 : fetch_word Ubsan.M.loaded_segments (0x82214 : word) = Some W_82214.
Proof. vm_refl. Qed.
Lemma D_82214 : decode_any W_82214 = Some (ShiftImm ALU_SRA 6 31 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82218 : bv 32 := 0x01f37333.
Lemma F_82218 : fetch_word Ubsan.M.loaded_segments (0x82218 : word) = Some W_82218.
Proof. vm_refl. Qed.
Lemma D_82218 : decode_any W_82218 = Some (Op ALU_AND 6 6 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_8221c : bv 32 := 0x00357f93.
Lemma F_8221c : fetch_word Ubsan.M.loaded_segments (0x8221c : word) = Some W_8221c.
Proof. vm_refl. Qed.
Lemma D_8221c : decode_any W_8221c = Some (OpImm ALU_AND 31 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82220 : bv 32 := 0x41be893b.
Lemma F_82220 : fetch_word Ubsan.M.loaded_segments (0x82220 : word) = Some W_82220.
Proof. vm_refl. Qed.
Lemma D_82220 : decode_any W_82220 = Some (Op32 ALU_SUB 18 29 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_82224 : bv 32 := 0x41e787bb.
Lemma F_82224 : fetch_word Ubsan.M.loaded_segments (0x82224 : word) = Some W_82224.
Proof. vm_refl. Qed.
Lemma D_82224 : decode_any W_82224 = Some (Op32 ALU_SUB 15 15 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_82228 : bv 32 := 0x02000f13.
Lemma F_82228 : fetch_word Ubsan.M.loaded_segments (0x82228 : word) = Some W_82228.
Proof. vm_refl. Qed.
Lemma D_82228 : decode_any W_82228 = Some (OpImm ALU_ADD 30 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8222c : bv 32 := 0x01650533.
Lemma F_8222c : fetch_word Ubsan.M.loaded_segments (0x8222c : word) = Some W_8222c.
Proof. vm_refl. Qed.
Lemma D_8222c : decode_any W_8222c = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82230 : bv 32 := 0x008989b3.
Lemma F_82230 : fetch_word Ubsan.M.loaded_segments (0x82230 : word) = Some W_82230.
Proof. vm_refl. Qed.
Lemma D_82230 : decode_any W_82230 = Some (Op ALU_ADD 19 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82234 : bv 32 := 0x006787b3.
Lemma F_82234 : fetch_word Ubsan.M.loaded_segments (0x82234 : word) = Some W_82234.
Proof. vm_refl. Qed.
Lemma D_82234 : decode_any W_82234 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82238 : bv 32 := 0x41d787bb.
Lemma F_82238 : fetch_word Ubsan.M.loaded_segments (0x82238 : word) = Some W_82238.
Proof. vm_refl. Qed.
Lemma D_82238 : decode_any W_82238 = Some (Op32 ALU_SUB 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_8223c : bv 32 := 0x43f7d313.
Lemma F_8223c : fetch_word Ubsan.M.loaded_segments (0x8223c : word) = Some W_8223c.
Proof. vm_refl. Qed.
Lemma D_8223c : decode_any W_8223c = Some (ShiftImm ALU_SRA 6 15 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82240 : bv 32 := 0x00f377b3.
Lemma F_82240 : fetch_word Ubsan.M.loaded_segments (0x82240 : word) = Some W_82240.
Proof. vm_refl. Qed.
Lemma D_82240 : decode_any W_82240 = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82244 : bv 32 := 0x00f907b3.
Lemma F_82244 : fetch_word Ubsan.M.loaded_segments (0x82244 : word) = Some W_82244.
Proof. vm_refl. Qed.
Lemma D_82244 : decode_any W_82244 = Some (Op ALU_ADD 15 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82248 : bv 32 := 0x0057d79b.
Lemma F_82248 : fetch_word Ubsan.M.loaded_segments (0x82248 : word) = Some W_82248.
Proof. vm_refl. Qed.
Lemma D_82248 : decode_any W_82248 = Some (ShiftImm32 ALU_SRL 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8224c : bv 32 := 0x40f00eb3.
Lemma F_8224c : fetch_word Ubsan.M.loaded_segments (0x8224c : word) = Some W_8224c.
Proof. vm_refl. Qed.
Lemma D_8224c : decode_any W_8224c = Some (Op ALU_SUB 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82250 : bv 32 := 0xffb00413.
Lemma F_82250 : fetch_word Ubsan.M.loaded_segments (0x82250 : word) = Some W_82250.
Proof. vm_refl. Qed.
Lemma D_82250 : decode_any W_82250 = Some (OpImm ALU_ADD 8 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_82254 : bv 32 := 0x05813d83.
Lemma F_82254 : fetch_word Ubsan.M.loaded_segments (0x82254 : word) = Some W_82254.
Proof. vm_refl. Qed.
Lemma D_82254 : decode_any W_82254 = Some (Load SZ8 true 27 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82258 : bv 32 := 0x0340006f.
Lemma F_82258 : fetch_word Ubsan.M.loaded_segments (0x82258 : word) = Some W_82258.
Proof. vm_refl. Qed.
Lemma D_82258 : decode_any W_82258 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_8225c : bv 32 := 0x00092303.
Lemma F_8225c : fetch_word Ubsan.M.loaded_segments (0x8225c : word) = Some W_8225c.
Proof. vm_refl. Qed.
Lemma D_8225c : decode_any W_8225c = Some (Load SZ4 true 6 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82260 : bv 32 := 0x0007a783.
Lemma F_82260 : fetch_word Ubsan.M.loaded_segments (0x82260 : word) = Some W_82260.
Proof. vm_refl. Qed.
Lemma D_82260 : decode_any W_82260 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82264 : bv 32 := 0x01437333.
Lemma F_82264 : fetch_word Ubsan.M.loaded_segments (0x82264 : word) = Some W_82264.
Proof. vm_refl. Qed.
Lemma D_82264 : decode_any W_82264 = Some (Op ALU_AND 6 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82268 : bv 32 := 0x01c7f7b3.
Lemma F_82268 : fetch_word Ubsan.M.loaded_segments (0x82268 : word) = Some W_82268.
Proof. vm_refl. Qed.
Lemma D_82268 : decode_any W_82268 = Some (Op ALU_AND 15 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8226c : bv 32 := 0x0067e7b3.
Lemma F_8226c : fetch_word Ubsan.M.loaded_segments (0x8226c : word) = Some W_8226c.
Proof. vm_refl. Qed.
Lemma D_8226c : decode_any W_8226c = Some (Op ALU_OR 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82270 : bv 32 := 0x00f92023.
Lemma F_82270 : fetch_word Ubsan.M.loaded_segments (0x82270 : word) = Some W_82270.
Proof. vm_refl. Qed.
Lemma D_82270 : decode_any W_82270 = Some (Store SZ4 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82274 : bv 32 := 0x001c8c9b.
Lemma F_82274 : fetch_word Ubsan.M.loaded_segments (0x82274 : word) = Some W_82274.
Proof. vm_refl. Qed.
Lemma D_82274 : decode_any W_82274 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82278 : bv 32 := 0x00e686bb.
Lemma F_82278 : fetch_word Ubsan.M.loaded_segments (0x82278 : word) = Some W_82278.
Proof. vm_refl. Qed.
Lemma D_82278 : decode_any W_82278 = Some (Op32 ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8227c : bv 32 := 0x01b585bb.
Lemma F_8227c : fetch_word Ubsan.M.loaded_segments (0x8227c : word) = Some W_8227c.
Proof. vm_refl. Qed.
Lemma D_8227c : decode_any W_8227c = Some (Op32 ALU_ADD 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_82280 : bv 32 := 0x08013783.
Lemma F_82280 : fetch_word Ubsan.M.loaded_segments (0x82280 : word) = Some W_82280.
Proof. vm_refl. Qed.
Lemma D_82280 : decode_any W_82280 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_82284 : bv 32 := 0x00fc9463.
Lemma F_82284 : fetch_word Ubsan.M.loaded_segments (0x82284 : word) = Some W_82284.
Proof. vm_refl. Qed.
Lemma D_82284 : decode_any W_82284 = Some (Branch BC_NE 25 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82288 : bv 32 := 0x3300506f.
Lemma F_82288 : fetch_word Ubsan.M.loaded_segments (0x82288 : word) = Some W_82288.
Proof. vm_refl. Qed.
Lemma D_82288 : decode_any W_82288 = Some (Jal 0 21296, 4%Z).
Proof. vm_refl. Qed.

Definition W_8228c : bv 32 := 0x03bc8333.
Lemma F_8228c : fetch_word Ubsan.M.loaded_segments (0x8228c : word) = Some W_8228c.
Proof. vm_refl. Qed.
Lemma D_8228c : decode_any W_8228c = Some (Mul M_MUL 6 25 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_82290 : bv 32 := 0x03bc87bb.
Lemma F_82290 : fetch_word Ubsan.M.loaded_segments (0x82290 : word) = Some W_82290.
Proof. vm_refl. Qed.
Lemma D_82290 : decode_any W_82290 = Some (Mul32 M_MUL 15 25 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_82294 : bv 32 := 0x26679063.
Lemma F_82294 : fetch_word Ubsan.M.loaded_segments (0x82294 : word) = Some W_82294.
Proof. vm_refl. Qed.
Lemma D_82294 : decode_any W_82294 = Some (Branch BC_NE 15 6 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_82298 : bv 32 := 0x0003031b.
Lemma F_82298 : fetch_word Ubsan.M.loaded_segments (0x82298 : word) = Some W_82298.
Proof. vm_refl. Qed.
Lemma D_82298 : decode_any W_82298 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8229c : bv 32 := 0x00231793.
Lemma F_8229c : fetch_word Ubsan.M.loaded_segments (0x8229c : word) = Some W_8229c.
Proof. vm_refl. Qed.
Lemma D_8229c : decode_any W_8229c = Some (ShiftImm ALU_SLL 15 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_822a0 : bv 32 := 0x00f887b3.
Lemma F_822a0 : fetch_word Ubsan.M.loaded_segments (0x822a0 : word) = Some W_822a0.
Proof. vm_refl. Qed.
Lemma D_822a0 : decode_any W_822a0 = Some (Op ALU_ADD 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_822a4 : bv 32 := 0x0017b913.
Lemma F_822a4 : fetch_word Ubsan.M.loaded_segments (0x822a4 : word) = Some W_822a4.
Proof. vm_refl. Qed.
Lemma D_822a4 : decode_any W_822a4 = Some (OpImm ALU_SLTU 18 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_822a8 : bv 32 := 0x25280663.
Lemma F_822a8 : fetch_word Ubsan.M.loaded_segments (0x822a8 : word) = Some W_822a8.
Proof. vm_refl. Qed.
Lemma D_822a8 : decode_any W_822a8 = Some (Branch BC_EQ 16 18 588, 4%Z).
Proof. vm_refl. Qed.

Definition W_822ac : bv 32 := 0x0117b933.
Lemma F_822ac : fetch_word Ubsan.M.loaded_segments (0x822ac : word) = Some W_822ac.
Proof. vm_refl. Qed.
Lemma D_822ac : decode_any W_822ac = Some (Op ALU_SLTU 18 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_822b0 : bv 32 := 0x00032313.
Lemma F_822b0 : fetch_word Ubsan.M.loaded_segments (0x822b0 : word) = Some W_822b0.
Proof. vm_refl. Qed.
Lemma D_822b0 : decode_any W_822b0 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_822b4 : bv 32 := 0x00694333.
Lemma F_822b4 : fetch_word Ubsan.M.loaded_segments (0x822b4 : word) = Some W_822b4.
Proof. vm_refl. Qed.
Lemma D_822b4 : decode_any W_822b4 = Some (Op ALU_XOR 6 18 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_822b8 : bv 32 := 0x00134313.
Lemma F_822b8 : fetch_word Ubsan.M.loaded_segments (0x822b8 : word) = Some W_822b8.
Proof. vm_refl. Qed.
Lemma D_822b8 : decode_any W_822b8 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_822bc : bv 32 := 0x22030c63.
Lemma F_822bc : fetch_word Ubsan.M.loaded_segments (0x822bc : word) = Some W_822bc.
Proof. vm_refl. Qed.
Lemma D_822bc : decode_any W_822bc = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_822c0 : bv 32 := 0x02ec8333.
Lemma F_822c0 : fetch_word Ubsan.M.loaded_segments (0x822c0 : word) = Some W_822c0.
Proof. vm_refl. Qed.
Lemma D_822c0 : decode_any W_822c0 = Some (Mul M_MUL 6 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_822c4 : bv 32 := 0x02ec893b.
Lemma F_822c4 : fetch_word Ubsan.M.loaded_segments (0x822c4 : word) = Some W_822c4.
Proof. vm_refl. Qed.
Lemma D_822c4 : decode_any W_822c4 = Some (Mul32 M_MUL 18 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_822c8 : bv 32 := 0x22691663.
Lemma F_822c8 : fetch_word Ubsan.M.loaded_segments (0x822c8 : word) = Some W_822c8.
Proof. vm_refl. Qed.
Lemma D_822c8 : decode_any W_822c8 = Some (Branch BC_NE 18 6 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_822cc : bv 32 := 0x0003031b.
Lemma F_822cc : fetch_word Ubsan.M.loaded_segments (0x822cc : word) = Some W_822cc.
Proof. vm_refl. Qed.
Lemma D_822cc : decode_any W_822cc = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_822d0 : bv 32 := 0x00231913.
Lemma F_822d0 : fetch_word Ubsan.M.loaded_segments (0x822d0 : word) = Some W_822d0.
Proof. vm_refl. Qed.
Lemma D_822d0 : decode_any W_822d0 = Some (ShiftImm ALU_SLL 18 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_822d4 : bv 32 := 0x00790933.
Lemma F_822d4 : fetch_word Ubsan.M.loaded_segments (0x822d4 : word) = Some W_822d4.
Proof. vm_refl. Qed.
Lemma D_822d4 : decode_any W_822d4 = Some (Op ALU_ADD 18 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_822d8 : bv 32 := 0x00193b13.
Lemma F_822d8 : fetch_word Ubsan.M.loaded_segments (0x822d8 : word) = Some W_822d8.
Proof. vm_refl. Qed.
Lemma D_822d8 : decode_any W_822d8 = Some (OpImm ALU_SLTU 22 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_822dc : bv 32 := 0x21628c63.
Lemma F_822dc : fetch_word Ubsan.M.loaded_segments (0x822dc : word) = Some W_822dc.
Proof. vm_refl. Qed.
Lemma D_822dc : decode_any W_822dc = Some (Branch BC_EQ 5 22 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_822e0 : bv 32 := 0x00793b33.
Lemma F_822e0 : fetch_word Ubsan.M.loaded_segments (0x822e0 : word) = Some W_822e0.
Proof. vm_refl. Qed.
Lemma D_822e0 : decode_any W_822e0 = Some (Op ALU_SLTU 22 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_822e4 : bv 32 := 0x00032313.
Lemma F_822e4 : fetch_word Ubsan.M.loaded_segments (0x822e4 : word) = Some W_822e4.
Proof. vm_refl. Qed.
Lemma D_822e4 : decode_any W_822e4 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_822e8 : bv 32 := 0x006b4333.
Lemma F_822e8 : fetch_word Ubsan.M.loaded_segments (0x822e8 : word) = Some W_822e8.
Proof. vm_refl. Qed.
Lemma D_822e8 : decode_any W_822e8 = Some (Op ALU_XOR 6 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_822ec : bv 32 := 0x00134313.
Lemma F_822ec : fetch_word Ubsan.M.loaded_segments (0x822ec : word) = Some W_822ec.
Proof. vm_refl. Qed.
Lemma D_822ec : decode_any W_822ec = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_822f0 : bv 32 := 0x20030263.
Lemma F_822f0 : fetch_word Ubsan.M.loaded_segments (0x822f0 : word) = Some W_822f0.
Proof. vm_refl. Qed.
Lemma D_822f0 : decode_any W_822f0 = Some (Branch BC_EQ 6 0 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_822f4 : bv 32 := 0x05e4ec63.
Lemma F_822f4 : fetch_word Ubsan.M.loaded_segments (0x822f4 : word) = Some W_822f4.
Proof. vm_refl. Qed.
Lemma D_822f4 : decode_any W_822f4 = Some (Branch BC_LTU 9 30 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_822f8 : bv 32 := 0x1e0a9e63.
Lemma F_822f8 : fetch_word Ubsan.M.loaded_segments (0x822f8 : word) = Some W_822f8.
Proof. vm_refl. Qed.
Lemma D_822f8 : decode_any W_822f8 = Some (Branch BC_NE 21 0 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_822fc : bv 32 := 0x00000793.
Lemma F_822fc : fetch_word Ubsan.M.loaded_segments (0x822fc : word) = Some W_822fc.
Proof. vm_refl. Qed.
Lemma D_822fc : decode_any W_822fc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82300 : bv 32 := 0x00269913.
Lemma F_82300 : fetch_word Ubsan.M.loaded_segments (0x82300 : word) = Some W_82300.
Proof. vm_refl. Qed.
Lemma D_82300 : decode_any W_82300 = Some (ShiftImm ALU_SLL 18 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82304 : bv 32 := 0x00259b13.
Lemma F_82304 : fetch_word Ubsan.M.loaded_segments (0x82304 : word) = Some W_82304.
Proof. vm_refl. Qed.
Lemma D_82304 : decode_any W_82304 = Some (ShiftImm ALU_SLL 22 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82308 : bv 32 := 0x01250933.
Lemma F_82308 : fetch_word Ubsan.M.loaded_segments (0x82308 : word) = Some W_82308.
Proof. vm_refl. Qed.
Lemma D_82308 : decode_any W_82308 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8230c : bv 32 := 0x01698b33.
Lemma F_8230c : fetch_word Ubsan.M.loaded_segments (0x8230c : word) = Some W_8230c.
Proof. vm_refl. Qed.
Lemma D_8230c : decode_any W_8230c = Some (Op ALU_ADD 22 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82310 : bv 32 := 0x000e8b93.
Lemma F_82310 : fetch_word Ubsan.M.loaded_segments (0x82310 : word) = Some W_82310.
Proof. vm_refl. Qed.
Lemma D_82310 : decode_any W_82310 = Some (OpImm ALU_ADD 23 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82314 : bv 32 := 0x00fb0333.
Lemma F_82314 : fetch_word Ubsan.M.loaded_segments (0x82314 : word) = Some W_82314.
Proof. vm_refl. Qed.
Lemma D_82314 : decode_any W_82314 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82318 : bv 32 := 0x1c030e63.
Lemma F_82318 : fetch_word Ubsan.M.loaded_segments (0x82318 : word) = Some W_82318.
Proof. vm_refl. Qed.
Lemma D_82318 : decode_any W_82318 = Some (Branch BC_EQ 6 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_8231c : bv 32 := 0x1c0f9c63.
Lemma F_8231c : fetch_word Ubsan.M.loaded_segments (0x8231c : word) = Some W_8231c.
Proof. vm_refl. Qed.
Lemma D_8231c : decode_any W_8231c = Some (Branch BC_NE 31 0 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_82320 : bv 32 := 0x00f90c33.
Lemma F_82320 : fetch_word Ubsan.M.loaded_segments (0x82320 : word) = Some W_82320.
Proof. vm_refl. Qed.
Lemma D_82320 : decode_any W_82320 = Some (Op ALU_ADD 24 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82324 : bv 32 := 0x1c0c0863.
Lemma F_82324 : fetch_word Ubsan.M.loaded_segments (0x82324 : word) = Some W_82324.
Proof. vm_refl. Qed.
Lemma D_82324 : decode_any W_82324 = Some (Branch BC_EQ 24 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_82328 : bv 32 := 0x00032d03.
Lemma F_82328 : fetch_word Ubsan.M.loaded_segments (0x82328 : word) = Some W_82328.
Proof. vm_refl. Qed.
Lemma D_82328 : decode_any W_82328 = Some (Load SZ4 true 26 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8232c : bv 32 := 0x01ac2023.
Lemma F_8232c : fetch_word Ubsan.M.loaded_segments (0x8232c : word) = Some W_8232c.
Proof. vm_refl. Qed.
Lemma D_8232c : decode_any W_8232c = Some (Store SZ4 24 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82330 : bv 32 := 0x1d846263.
Lemma F_82330 : fetch_word Ubsan.M.loaded_segments (0x82330 : word) = Some W_82330.
Proof. vm_refl. Qed.
Lemma D_82330 : decode_any W_82330 = Some (Branch BC_LTU 8 24 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_82334 : bv 32 := 0x1c646063.
Lemma F_82334 : fetch_word Ubsan.M.loaded_segments (0x82334 : word) = Some W_82334.
Proof. vm_refl. Qed.
Lemma D_82334 : decode_any W_82334 = Some (Branch BC_LTU 8 6 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_82338 : bv 32 := 0x001b8b9b.
Lemma F_82338 : fetch_word Ubsan.M.loaded_segments (0x82338 : word) = Some W_82338.
Proof. vm_refl. Qed.
Lemma D_82338 : decode_any W_82338 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8233c : bv 32 := 0x00478793.
Lemma F_8233c : fetch_word Ubsan.M.loaded_segments (0x8233c : word) = Some W_8233c.
Proof. vm_refl. Qed.
Lemma D_8233c : decode_any W_8233c = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_82340 : bv 32 := 0xfc0b9ae3.
Lemma F_82340 : fetch_word Ubsan.M.loaded_segments (0x82340 : word) = Some W_82340.
Proof. vm_refl. Qed.
Lemma D_82340 : decode_any W_82340 = Some (Branch BC_NE 23 0 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_82344 : bv 32 := 0x00f90933.
Lemma F_82344 : fetch_word Ubsan.M.loaded_segments (0x82344 : word) = Some W_82344.
Proof. vm_refl. Qed.
Lemma D_82344 : decode_any W_82344 = Some (Op ALU_ADD 18 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82348 : bv 32 := 0x00fb07b3.
Lemma F_82348 : fetch_word Ubsan.M.loaded_segments (0x82348 : word) = Some W_82348.
Proof. vm_refl. Qed.
Lemma D_82348 : decode_any W_82348 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8234c : bv 32 := 0xf20604e3.
Lemma F_8234c : fetch_word Ubsan.M.loaded_segments (0x8234c : word) = Some W_8234c.
Proof. vm_refl. Qed.
Lemma D_8234c : decode_any W_8234c = Some (Branch BC_EQ 12 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_82350 : bv 32 := 0x1a090263.
Lemma F_82350 : fetch_word Ubsan.M.loaded_segments (0x82350 : word) = Some W_82350.
Proof. vm_refl. Qed.
Lemma D_82350 : decode_any W_82350 = Some (Branch BC_EQ 18 0 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_82354 : bv 32 := 0x00397313.
Lemma F_82354 : fetch_word Ubsan.M.loaded_segments (0x82354 : word) = Some W_82354.
Proof. vm_refl. Qed.
Lemma D_82354 : decode_any W_82354 = Some (OpImm ALU_AND 6 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82358 : bv 32 := 0x18031e63.
Lemma F_82358 : fetch_word Ubsan.M.loaded_segments (0x82358 : word) = Some W_82358.
Proof. vm_refl. Qed.
Lemma D_82358 : decode_any W_82358 = Some (Branch BC_NE 6 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_8235c : bv 32 := 0x18078c63.
Lemma F_8235c : fetch_word Ubsan.M.loaded_segments (0x8235c : word) = Some W_8235c.
Proof. vm_refl. Qed.
Lemma D_8235c : decode_any W_8235c = Some (Branch BC_EQ 15 0 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_82360 : bv 32 := 0x0037f313.
Lemma F_82360 : fetch_word Ubsan.M.loaded_segments (0x82360 : word) = Some W_82360.
Proof. vm_refl. Qed.
Lemma D_82360 : decode_any W_82360 = Some (OpImm ALU_AND 6 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82364 : bv 32 := 0xee030ce3.
Lemma F_82364 : fetch_word Ubsan.M.loaded_segments (0x82364 : word) = Some W_82364.
Proof. vm_refl. Qed.
Lemma D_82364 : decode_any W_82364 = Some (Branch BC_EQ 6 0 7928, 4%Z).
Proof. vm_refl. Qed.

Definition W_82368 : bv 32 := 0x18c0006f.
Lemma F_82368 : fetch_word Ubsan.M.loaded_segments (0x82368 : word) = Some W_82368.
Proof. vm_refl. Qed.
Lemma D_82368 : decode_any W_82368 = Some (Jal 0 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_8236c : bv 32 := 0x00000593.
Lemma F_8236c : fetch_word Ubsan.M.loaded_segments (0x8236c : word) = Some W_8236c.
Proof. vm_refl. Qed.
Lemma D_8236c : decode_any W_8236c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82370 : bv 32 := 0x00000693.
Lemma F_82370 : fetch_word Ubsan.M.loaded_segments (0x82370 : word) = Some W_82370.
Proof. vm_refl. Qed.
Lemma D_82370 : decode_any W_82370 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82374 : bv 32 := 0x00000c93.
Lemma F_82374 : fetch_word Ubsan.M.loaded_segments (0x82374 : word) = Some W_82374.
Proof. vm_refl. Qed.
Lemma D_82374 : decode_any W_82374 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82378 : bv 32 := 0x015a07b3.
Lemma F_82378 : fetch_word Ubsan.M.loaded_segments (0x82378 : word) = Some W_82378.
Proof. vm_refl. Qed.
Lemma D_82378 : decode_any W_82378 = Some (Op ALU_ADD 15 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_8237c : bv 32 := 0xfffe4a13.
Lemma F_8237c : fetch_word Ubsan.M.loaded_segments (0x8237c : word) = Some W_8237c.
Proof. vm_refl. Qed.
Lemma D_8237c : decode_any W_8237c = Some (OpImm ALU_XOR 20 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82380 : bv 32 := 0x016b8b33.
Lemma F_82380 : fetch_word Ubsan.M.loaded_segments (0x82380 : word) = Some W_82380.
Proof. vm_refl. Qed.
Lemma D_82380 : decode_any W_82380 = Some (Op ALU_ADD 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82384 : bv 32 := 0x0039fa93.
Lemma F_82384 : fetch_word Ubsan.M.loaded_segments (0x82384 : word) = Some W_82384.
Proof. vm_refl. Qed.
Lemma D_82384 : decode_any W_82384 = Some (OpImm ALU_AND 21 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82388 : bv 32 := 0x00890433.
Lemma F_82388 : fetch_word Ubsan.M.loaded_segments (0x82388 : word) = Some W_82388.
Proof. vm_refl. Qed.
Lemma D_82388 : decode_any W_82388 = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8238c : bv 32 := 0x43ffd313.
Lemma F_8238c : fetch_word Ubsan.M.loaded_segments (0x8238c : word) = Some W_8238c.
Proof. vm_refl. Qed.
Lemma D_8238c : decode_any W_8238c = Some (ShiftImm ALU_SRA 6 31 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82390 : bv 32 := 0x01f37333.
Lemma F_82390 : fetch_word Ubsan.M.loaded_segments (0x82390 : word) = Some W_82390.
Proof. vm_refl. Qed.
Lemma D_82390 : decode_any W_82390 = Some (Op ALU_AND 6 6 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82394 : bv 32 := 0x00357f93.
Lemma F_82394 : fetch_word Ubsan.M.loaded_segments (0x82394 : word) = Some W_82394.
Proof. vm_refl. Qed.
Lemma D_82394 : decode_any W_82394 = Some (OpImm ALU_AND 31 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82398 : bv 32 := 0x41be893b.
Lemma F_82398 : fetch_word Ubsan.M.loaded_segments (0x82398 : word) = Some W_82398.
Proof. vm_refl. Qed.
Lemma D_82398 : decode_any W_82398 = Some (Op32 ALU_SUB 18 29 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8239c : bv 32 := 0x41e787bb.
Lemma F_8239c : fetch_word Ubsan.M.loaded_segments (0x8239c : word) = Some W_8239c.
Proof. vm_refl. Qed.
Lemma D_8239c : decode_any W_8239c = Some (Op32 ALU_SUB 15 15 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a0 : bv 32 := 0x02000f13.
Lemma F_823a0 : fetch_word Ubsan.M.loaded_segments (0x823a0 : word) = Some W_823a0.
Proof. vm_refl. Qed.
Lemma D_823a0 : decode_any W_823a0 = Some (OpImm ALU_ADD 30 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a4 : bv 32 := 0x01650533.
Lemma F_823a4 : fetch_word Ubsan.M.loaded_segments (0x823a4 : word) = Some W_823a4.
Proof. vm_refl. Qed.
Lemma D_823a4 : decode_any W_823a4 = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a8 : bv 32 := 0x008989b3.
Lemma F_823a8 : fetch_word Ubsan.M.loaded_segments (0x823a8 : word) = Some W_823a8.
Proof. vm_refl. Qed.
Lemma D_823a8 : decode_any W_823a8 = Some (Op ALU_ADD 19 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_823ac : bv 32 := 0x006787b3.
Lemma F_823ac : fetch_word Ubsan.M.loaded_segments (0x823ac : word) = Some W_823ac.
Proof. vm_refl. Qed.
Lemma D_823ac : decode_any W_823ac = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b0 : bv 32 := 0x41d787bb.
Lemma F_823b0 : fetch_word Ubsan.M.loaded_segments (0x823b0 : word) = Some W_823b0.
Proof. vm_refl. Qed.
Lemma D_823b0 : decode_any W_823b0 = Some (Op32 ALU_SUB 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b4 : bv 32 := 0x43f7d313.
Lemma F_823b4 : fetch_word Ubsan.M.loaded_segments (0x823b4 : word) = Some W_823b4.
Proof. vm_refl. Qed.
Lemma D_823b4 : decode_any W_823b4 = Some (ShiftImm ALU_SRA 6 15 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b8 : bv 32 := 0x00f377b3.
Lemma F_823b8 : fetch_word Ubsan.M.loaded_segments (0x823b8 : word) = Some W_823b8.
Proof. vm_refl. Qed.
Lemma D_823b8 : decode_any W_823b8 = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_823bc : bv 32 := 0x00f907b3.
Lemma F_823bc : fetch_word Ubsan.M.loaded_segments (0x823bc : word) = Some W_823bc.
Proof. vm_refl. Qed.
Lemma D_823bc : decode_any W_823bc = Some (Op ALU_ADD 15 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c0 : bv 32 := 0x0057d79b.
Lemma F_823c0 : fetch_word Ubsan.M.loaded_segments (0x823c0 : word) = Some W_823c0.
Proof. vm_refl. Qed.
Lemma D_823c0 : decode_any W_823c0 = Some (ShiftImm32 ALU_SRL 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c4 : bv 32 := 0x40f00eb3.
Lemma F_823c4 : fetch_word Ubsan.M.loaded_segments (0x823c4 : word) = Some W_823c4.
Proof. vm_refl. Qed.
Lemma D_823c4 : decode_any W_823c4 = Some (Op ALU_SUB 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c8 : bv 32 := 0xffb00413.
Lemma F_823c8 : fetch_word Ubsan.M.loaded_segments (0x823c8 : word) = Some W_823c8.
Proof. vm_refl. Qed.
Lemma D_823c8 : decode_any W_823c8 = Some (OpImm ALU_ADD 8 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_823cc : bv 32 := 0x05813083.
Lemma F_823cc : fetch_word Ubsan.M.loaded_segments (0x823cc : word) = Some W_823cc.
Proof. vm_refl. Qed.
Lemma D_823cc : decode_any W_823cc = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d0 : bv 32 := 0x03c0006f.
Lemma F_823d0 : fetch_word Ubsan.M.loaded_segments (0x823d0 : word) = Some W_823d0.
Proof. vm_refl. Qed.
Lemma D_823d0 : decode_any W_823d0 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d4 : bv 32 := 0x00092303.
Lemma F_823d4 : fetch_word Ubsan.M.loaded_segments (0x823d4 : word) = Some W_823d4.
Proof. vm_refl. Qed.
Lemma D_823d4 : decode_any W_823d4 = Some (Load SZ4 true 6 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d8 : bv 32 := 0x0007a783.
Lemma F_823d8 : fetch_word Ubsan.M.loaded_segments (0x823d8 : word) = Some W_823d8.
Proof. vm_refl. Qed.
Lemma D_823d8 : decode_any W_823d8 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823dc : bv 32 := 0x01437b33.
Lemma F_823dc : fetch_word Ubsan.M.loaded_segments (0x823dc : word) = Some W_823dc.
Proof. vm_refl. Qed.
Lemma D_823dc : decode_any W_823dc = Some (Op ALU_AND 22 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e0 : bv 32 := 0xfff7c793.
Lemma F_823e0 : fetch_word Ubsan.M.loaded_segments (0x823e0 : word) = Some W_823e0.
Proof. vm_refl. Qed.
Lemma D_823e0 : decode_any W_823e0 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e4 : bv 32 := 0x00f367b3.
Lemma F_823e4 : fetch_word Ubsan.M.loaded_segments (0x823e4 : word) = Some W_823e4.
Proof. vm_refl. Qed.
Lemma D_823e4 : decode_any W_823e4 = Some (Op ALU_OR 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e8 : bv 32 := 0x01c7f7b3.
Lemma F_823e8 : fetch_word Ubsan.M.loaded_segments (0x823e8 : word) = Some W_823e8.
Proof. vm_refl. Qed.
Lemma D_823e8 : decode_any W_823e8 = Some (Op ALU_AND 15 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_823ec : bv 32 := 0x0167e7b3.
Lemma F_823ec : fetch_word Ubsan.M.loaded_segments (0x823ec : word) = Some W_823ec.
Proof. vm_refl. Qed.
Lemma D_823ec : decode_any W_823ec = Some (Op ALU_OR 15 15 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f0 : bv 32 := 0x00f92023.
Lemma F_823f0 : fetch_word Ubsan.M.loaded_segments (0x823f0 : word) = Some W_823f0.
Proof. vm_refl. Qed.
Lemma D_823f0 : decode_any W_823f0 = Some (Store SZ4 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f4 : bv 32 := 0x001c8c9b.
Lemma F_823f4 : fetch_word Ubsan.M.loaded_segments (0x823f4 : word) = Some W_823f4.
Proof. vm_refl. Qed.
Lemma D_823f4 : decode_any W_823f4 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f8 : bv 32 := 0x00e686bb.
Lemma F_823f8 : fetch_word Ubsan.M.loaded_segments (0x823f8 : word) = Some W_823f8.
Proof. vm_refl. Qed.
Lemma D_823f8 : decode_any W_823f8 = Some (Op32 ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_823fc : bv 32 := 0x001585bb.
Lemma F_823fc : fetch_word Ubsan.M.loaded_segments (0x823fc : word) = Some W_823fc.
Proof. vm_refl. Qed.
Lemma D_823fc : decode_any W_823fc = Some (Op32 ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82400 : bv 32 := 0x08013783.
Lemma F_82400 : fetch_word Ubsan.M.loaded_segments (0x82400 : word) = Some W_82400.
Proof. vm_refl. Qed.
Lemma D_82400 : decode_any W_82400 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_82404 : bv 32 := 0x00fc9463.
Lemma F_82404 : fetch_word Ubsan.M.loaded_segments (0x82404 : word) = Some W_82404.
Proof. vm_refl. Qed.
Lemma D_82404 : decode_any W_82404 = Some (Branch BC_NE 25 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82408 : bv 32 := 0x1b00506f.
Lemma F_82408 : fetch_word Ubsan.M.loaded_segments (0x82408 : word) = Some W_82408.
Proof. vm_refl. Qed.
Lemma D_82408 : decode_any W_82408 = Some (Jal 0 20912, 4%Z).
Proof. vm_refl. Qed.

Definition W_8240c : bv 32 := 0x021c8333.
Lemma F_8240c : fetch_word Ubsan.M.loaded_segments (0x8240c : word) = Some W_8240c.
Proof. vm_refl. Qed.
Lemma D_8240c : decode_any W_8240c = Some (Mul M_MUL 6 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82410 : bv 32 := 0x021c87bb.
Lemma F_82410 : fetch_word Ubsan.M.loaded_segments (0x82410 : word) = Some W_82410.
Proof. vm_refl. Qed.
Lemma D_82410 : decode_any W_82410 = Some (Mul32 M_MUL 15 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82414 : bv 32 := 0x0e679063.
Lemma F_82414 : fetch_word Ubsan.M.loaded_segments (0x82414 : word) = Some W_82414.
Proof. vm_refl. Qed.
Lemma D_82414 : decode_any W_82414 = Some (Branch BC_NE 15 6 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_82418 : bv 32 := 0x0003031b.
Lemma F_82418 : fetch_word Ubsan.M.loaded_segments (0x82418 : word) = Some W_82418.
Proof. vm_refl. Qed.
Lemma D_82418 : decode_any W_82418 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8241c : bv 32 := 0x00231793.
Lemma F_8241c : fetch_word Ubsan.M.loaded_segments (0x8241c : word) = Some W_8241c.
Proof. vm_refl. Qed.
Lemma D_8241c : decode_any W_8241c = Some (ShiftImm ALU_SLL 15 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82420 : bv 32 := 0x00f887b3.
Lemma F_82420 : fetch_word Ubsan.M.loaded_segments (0x82420 : word) = Some W_82420.
Proof. vm_refl. Qed.
Lemma D_82420 : decode_any W_82420 = Some (Op ALU_ADD 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82424 : bv 32 := 0x0017b913.
Lemma F_82424 : fetch_word Ubsan.M.loaded_segments (0x82424 : word) = Some W_82424.
Proof. vm_refl. Qed.
Lemma D_82424 : decode_any W_82424 = Some (OpImm ALU_SLTU 18 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82428 : bv 32 := 0x0d280663.
Lemma F_82428 : fetch_word Ubsan.M.loaded_segments (0x82428 : word) = Some W_82428.
Proof. vm_refl. Qed.
Lemma D_82428 : decode_any W_82428 = Some (Branch BC_EQ 16 18 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_8242c : bv 32 := 0x0117b933.
Lemma F_8242c : fetch_word Ubsan.M.loaded_segments (0x8242c : word) = Some W_8242c.
Proof. vm_refl. Qed.
Lemma D_8242c : decode_any W_8242c = Some (Op ALU_SLTU 18 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82430 : bv 32 := 0x00032313.
Lemma F_82430 : fetch_word Ubsan.M.loaded_segments (0x82430 : word) = Some W_82430.
Proof. vm_refl. Qed.
Lemma D_82430 : decode_any W_82430 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82434 : bv 32 := 0x00694333.
Lemma F_82434 : fetch_word Ubsan.M.loaded_segments (0x82434 : word) = Some W_82434.
Proof. vm_refl. Qed.
Lemma D_82434 : decode_any W_82434 = Some (Op ALU_XOR 6 18 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82438 : bv 32 := 0x00134313.
Lemma F_82438 : fetch_word Ubsan.M.loaded_segments (0x82438 : word) = Some W_82438.
Proof. vm_refl. Qed.
Lemma D_82438 : decode_any W_82438 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8243c : bv 32 := 0x0a030c63.
Lemma F_8243c : fetch_word Ubsan.M.loaded_segments (0x8243c : word) = Some W_8243c.
Proof. vm_refl. Qed.
Lemma D_8243c : decode_any W_8243c = Some (Branch BC_EQ 6 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_82440 : bv 32 := 0x02ec8333.
Lemma F_82440 : fetch_word Ubsan.M.loaded_segments (0x82440 : word) = Some W_82440.
Proof. vm_refl. Qed.
Lemma D_82440 : decode_any W_82440 = Some (Mul M_MUL 6 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82444 : bv 32 := 0x02ec893b.
Lemma F_82444 : fetch_word Ubsan.M.loaded_segments (0x82444 : word) = Some W_82444.
Proof. vm_refl. Qed.
Lemma D_82444 : decode_any W_82444 = Some (Mul32 M_MUL 18 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82448 : bv 32 := 0x0a691663.
Lemma F_82448 : fetch_word Ubsan.M.loaded_segments (0x82448 : word) = Some W_82448.
Proof. vm_refl. Qed.
Lemma D_82448 : decode_any W_82448 = Some (Branch BC_NE 18 6 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_8244c : bv 32 := 0x0003031b.
Lemma F_8244c : fetch_word Ubsan.M.loaded_segments (0x8244c : word) = Some W_8244c.
Proof. vm_refl. Qed.
Lemma D_8244c : decode_any W_8244c = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82450 : bv 32 := 0x00231913.
Lemma F_82450 : fetch_word Ubsan.M.loaded_segments (0x82450 : word) = Some W_82450.
Proof. vm_refl. Qed.
Lemma D_82450 : decode_any W_82450 = Some (ShiftImm ALU_SLL 18 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82454 : bv 32 := 0x00790933.
Lemma F_82454 : fetch_word Ubsan.M.loaded_segments (0x82454 : word) = Some W_82454.
Proof. vm_refl. Qed.
Lemma D_82454 : decode_any W_82454 = Some (Op ALU_ADD 18 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82458 : bv 32 := 0x00193b13.
Lemma F_82458 : fetch_word Ubsan.M.loaded_segments (0x82458 : word) = Some W_82458.
Proof. vm_refl. Qed.
Lemma D_82458 : decode_any W_82458 = Some (OpImm ALU_SLTU 22 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8245c : bv 32 := 0x09628c63.
Lemma F_8245c : fetch_word Ubsan.M.loaded_segments (0x8245c : word) = Some W_8245c.
Proof. vm_refl. Qed.
Lemma D_8245c : decode_any W_8245c = Some (Branch BC_EQ 5 22 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_82460 : bv 32 := 0x00793b33.
Lemma F_82460 : fetch_word Ubsan.M.loaded_segments (0x82460 : word) = Some W_82460.
Proof. vm_refl. Qed.
Lemma D_82460 : decode_any W_82460 = Some (Op ALU_SLTU 22 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82464 : bv 32 := 0x00032313.
Lemma F_82464 : fetch_word Ubsan.M.loaded_segments (0x82464 : word) = Some W_82464.
Proof. vm_refl. Qed.
Lemma D_82464 : decode_any W_82464 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82468 : bv 32 := 0x006b4333.
Lemma F_82468 : fetch_word Ubsan.M.loaded_segments (0x82468 : word) = Some W_82468.
Proof. vm_refl. Qed.
Lemma D_82468 : decode_any W_82468 = Some (Op ALU_XOR 6 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8246c : bv 32 := 0x00134313.
Lemma F_8246c : fetch_word Ubsan.M.loaded_segments (0x8246c : word) = Some W_8246c.
Proof. vm_refl. Qed.
Lemma D_8246c : decode_any W_8246c = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82470 : bv 32 := 0x08030263.
Lemma F_82470 : fetch_word Ubsan.M.loaded_segments (0x82470 : word) = Some W_82470.
Proof. vm_refl. Qed.
Lemma D_82470 : decode_any W_82470 = Some (Branch BC_EQ 6 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_82474 : bv 32 := 0x07e4e263.
Lemma F_82474 : fetch_word Ubsan.M.loaded_segments (0x82474 : word) = Some W_82474.
Proof. vm_refl. Qed.
Lemma D_82474 : decode_any W_82474 = Some (Branch BC_LTU 9 30 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_82478 : bv 32 := 0x060a9e63.
Lemma F_82478 : fetch_word Ubsan.M.loaded_segments (0x82478 : word) = Some W_82478.
Proof. vm_refl. Qed.
Lemma D_82478 : decode_any W_82478 = Some (Branch BC_NE 21 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_8247c : bv 32 := 0x00000793.
Lemma F_8247c : fetch_word Ubsan.M.loaded_segments (0x8247c : word) = Some W_8247c.
Proof. vm_refl. Qed.
Lemma D_8247c : decode_any W_8247c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82480 : bv 32 := 0x00269913.
Lemma F_82480 : fetch_word Ubsan.M.loaded_segments (0x82480 : word) = Some W_82480.
Proof. vm_refl. Qed.
Lemma D_82480 : decode_any W_82480 = Some (ShiftImm ALU_SLL 18 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82484 : bv 32 := 0x00259b13.
Lemma F_82484 : fetch_word Ubsan.M.loaded_segments (0x82484 : word) = Some W_82484.
Proof. vm_refl. Qed.
Lemma D_82484 : decode_any W_82484 = Some (ShiftImm ALU_SLL 22 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82488 : bv 32 := 0x01250933.
Lemma F_82488 : fetch_word Ubsan.M.loaded_segments (0x82488 : word) = Some W_82488.
Proof. vm_refl. Qed.
Lemma D_82488 : decode_any W_82488 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8248c : bv 32 := 0x01698b33.
Lemma F_8248c : fetch_word Ubsan.M.loaded_segments (0x8248c : word) = Some W_8248c.
Proof. vm_refl. Qed.
Lemma D_8248c : decode_any W_8248c = Some (Op ALU_ADD 22 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_82490 : bv 32 := 0x000e8b93.
Lemma F_82490 : fetch_word Ubsan.M.loaded_segments (0x82490 : word) = Some W_82490.
Proof. vm_refl. Qed.
Lemma D_82490 : decode_any W_82490 = Some (OpImm ALU_ADD 23 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82494 : bv 32 := 0x00fb0333.
Lemma F_82494 : fetch_word Ubsan.M.loaded_segments (0x82494 : word) = Some W_82494.
Proof. vm_refl. Qed.
Lemma D_82494 : decode_any W_82494 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82498 : bv 32 := 0x04030e63.
Lemma F_82498 : fetch_word Ubsan.M.loaded_segments (0x82498 : word) = Some W_82498.
Proof. vm_refl. Qed.
Lemma D_82498 : decode_any W_82498 = Some (Branch BC_EQ 6 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_8249c : bv 32 := 0x040f9c63.
Lemma F_8249c : fetch_word Ubsan.M.loaded_segments (0x8249c : word) = Some W_8249c.
Proof. vm_refl. Qed.
Lemma D_8249c : decode_any W_8249c = Some (Branch BC_NE 31 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a0 : bv 32 := 0x00f90c33.
Lemma F_824a0 : fetch_word Ubsan.M.loaded_segments (0x824a0 : word) = Some W_824a0.
Proof. vm_refl. Qed.
Lemma D_824a0 : decode_any W_824a0 = Some (Op ALU_ADD 24 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a4 : bv 32 := 0x040c0863.
Lemma F_824a4 : fetch_word Ubsan.M.loaded_segments (0x824a4 : word) = Some W_824a4.
Proof. vm_refl. Qed.
Lemma D_824a4 : decode_any W_824a4 = Some (Branch BC_EQ 24 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a8 : bv 32 := 0x00032d03.
Lemma F_824a8 : fetch_word Ubsan.M.loaded_segments (0x824a8 : word) = Some W_824a8.
Proof. vm_refl. Qed.
Lemma D_824a8 : decode_any W_824a8 = Some (Load SZ4 true 26 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_824ac : bv 32 := 0x000c2d83.
Lemma F_824ac : fetch_word Ubsan.M.loaded_segments (0x824ac : word) = Some W_824ac.
Proof. vm_refl. Qed.
Lemma D_824ac : decode_any W_824ac = Some (Load SZ4 true 27 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_824b0 : bv 32 := 0xfffd4d13.
Lemma F_824b0 : fetch_word Ubsan.M.loaded_segments (0x824b0 : word) = Some W_824b0.
Proof. vm_refl. Qed.
Lemma D_824b0 : decode_any W_824b0 = Some (OpImm ALU_XOR 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_824b4 : bv 32 := 0x01aded33.
Lemma F_824b4 : fetch_word Ubsan.M.loaded_segments (0x824b4 : word) = Some W_824b4.
Proof. vm_refl. Qed.
Lemma D_824b4 : decode_any W_824b4 = Some (Op ALU_OR 26 27 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_824b8 : bv 32 := 0x01ac2023.
Lemma F_824b8 : fetch_word Ubsan.M.loaded_segments (0x824b8 : word) = Some W_824b8.
Proof. vm_refl. Qed.
Lemma D_824b8 : decode_any W_824b8 = Some (Store SZ4 24 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_824bc : bv 32 := 0x03846c63.
Lemma F_824bc : fetch_word Ubsan.M.loaded_segments (0x824bc : word) = Some W_824bc.
Proof. vm_refl. Qed.
Lemma D_824bc : decode_any W_824bc = Some (Branch BC_LTU 8 24 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_824c0 : bv 32 := 0x02646a63.
Lemma F_824c0 : fetch_word Ubsan.M.loaded_segments (0x824c0 : word) = Some W_824c0.
Proof. vm_refl. Qed.
Lemma D_824c0 : decode_any W_824c0 = Some (Branch BC_LTU 8 6 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_824c4 : bv 32 := 0x001b8b9b.
Lemma F_824c4 : fetch_word Ubsan.M.loaded_segments (0x824c4 : word) = Some W_824c4.
Proof. vm_refl. Qed.
Lemma D_824c4 : decode_any W_824c4 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_824c8 : bv 32 := 0x00478793.
Lemma F_824c8 : fetch_word Ubsan.M.loaded_segments (0x824c8 : word) = Some W_824c8.
Proof. vm_refl. Qed.
Lemma D_824c8 : decode_any W_824c8 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_824cc : bv 32 := 0xfc0b94e3.
Lemma F_824cc : fetch_word Ubsan.M.loaded_segments (0x824cc : word) = Some W_824cc.
Proof. vm_refl. Qed.
Lemma D_824cc : decode_any W_824cc = Some (Branch BC_NE 23 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_824d0 : bv 32 := 0x00f90933.
Lemma F_824d0 : fetch_word Ubsan.M.loaded_segments (0x824d0 : word) = Some W_824d0.
Proof. vm_refl. Qed.
Lemma D_824d0 : decode_any W_824d0 = Some (Op ALU_ADD 18 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_824d4 : bv 32 := 0x00fb07b3.
Lemma F_824d4 : fetch_word Ubsan.M.loaded_segments (0x824d4 : word) = Some W_824d4.
Proof. vm_refl. Qed.
Lemma D_824d4 : decode_any W_824d4 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_824d8 : bv 32 := 0xf0060ee3.
Lemma F_824d8 : fetch_word Ubsan.M.loaded_segments (0x824d8 : word) = Some W_824d8.
Proof. vm_refl. Qed.
Lemma D_824d8 : decode_any W_824d8 = Some (Branch BC_EQ 12 0 7964, 4%Z).
Proof. vm_refl. Qed.

Definition W_824dc : bv 32 := 0x00090c63.
Lemma F_824dc : fetch_word Ubsan.M.loaded_segments (0x824dc : word) = Some W_824dc.
Proof. vm_refl. Qed.
Lemma D_824dc : decode_any W_824dc = Some (Branch BC_EQ 18 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_824e0 : bv 32 := 0x00397313.
Lemma F_824e0 : fetch_word Ubsan.M.loaded_segments (0x824e0 : word) = Some W_824e0.
Proof. vm_refl. Qed.
Lemma D_824e0 : decode_any W_824e0 = Some (OpImm ALU_AND 6 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_824e4 : bv 32 := 0x00031863.
Lemma F_824e4 : fetch_word Ubsan.M.loaded_segments (0x824e4 : word) = Some W_824e4.
Proof. vm_refl. Qed.
Lemma D_824e4 : decode_any W_824e4 = Some (Branch BC_NE 6 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_824e8 : bv 32 := 0x00078663.
Lemma F_824e8 : fetch_word Ubsan.M.loaded_segments (0x824e8 : word) = Some W_824e8.
Proof. vm_refl. Qed.
Lemma D_824e8 : decode_any W_824e8 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_824ec : bv 32 := 0x0037f313.
Lemma F_824ec : fetch_word Ubsan.M.loaded_segments (0x824ec : word) = Some W_824ec.
Proof. vm_refl. Qed.
Lemma D_824ec : decode_any W_824ec = Some (OpImm ALU_AND 6 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_824f0 : bv 32 := 0xee0302e3.
Lemma F_824f0 : fetch_word Ubsan.M.loaded_segments (0x824f0 : word) = Some W_824f0.
Proof. vm_refl. Qed.
Lemma D_824f0 : decode_any W_824f0 = Some (Branch BC_EQ 6 0 7908, 4%Z).
Proof. vm_refl. Qed.

Definition W_824f4 : bv 32 := 0xc0001073.
Lemma F_824f4 : fetch_word Ubsan.M.loaded_segments (0x824f4 : word) = Some W_824f4.
Proof. vm_refl. Qed.
Lemma D_824f4 : decode_any W_824f4 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_824f8 : bv 32 := 0x0e008263.
Lemma F_824f8 : fetch_word Ubsan.M.loaded_segments (0x824f8 : word) = Some W_824f8.
Proof. vm_refl. Qed.
Lemma D_824f8 : decode_any W_824f8 = Some (Branch BC_EQ 1 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_824fc : bv 32 := 0x003a7593.
Lemma F_824fc : fetch_word Ubsan.M.loaded_segments (0x824fc : word) = Some W_824fc.
Proof. vm_refl. Qed.
Lemma D_824fc : decode_any W_824fc = Some (OpImm ALU_AND 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82500 : bv 32 := 0xfe059ae3.
Lemma F_82500 : fetch_word Ubsan.M.loaded_segments (0x82500 : word) = Some W_82500.
Proof. vm_refl. Qed.
Lemma D_82500 : decode_any W_82500 = Some (Branch BC_NE 11 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_82504 : bv 32 := 0xfffbc613.
Lemma F_82504 : fetch_word Ubsan.M.loaded_segments (0x82504 : word) = Some W_82504.
Proof. vm_refl. Qed.
Lemma D_82504 : decode_any W_82504 = Some (OpImm ALU_XOR 12 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82508 : bv 32 := 0x00271693.
Lemma F_82508 : fetch_word Ubsan.M.loaded_segments (0x82508 : word) = Some W_82508.
Proof. vm_refl. Qed.
Lemma D_82508 : decode_any W_82508 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8250c : bv 32 := 0x05813983.
Lemma F_8250c : fetch_word Ubsan.M.loaded_segments (0x8250c : word) = Some W_8250c.
Proof. vm_refl. Qed.
Lemma D_8250c : decode_any W_8250c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82510 : bv 32 := 0x00299893.
Lemma F_82510 : fetch_word Ubsan.M.loaded_segments (0x82510 : word) = Some W_82510.
Proof. vm_refl. Qed.
Lemma D_82510 : decode_any W_82510 = Some (ShiftImm ALU_SLL 17 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82514 : bv 32 := 0x003af293.
Lemma F_82514 : fetch_word Ubsan.M.loaded_segments (0x82514 : word) = Some W_82514.
Proof. vm_refl. Qed.
Lemma D_82514 : decode_any W_82514 = Some (OpImm ALU_AND 5 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82518 : bv 32 := 0x05013e03.
Lemma F_82518 : fetch_word Ubsan.M.loaded_segments (0x82518 : word) = Some W_82518.
Proof. vm_refl. Qed.
Lemma D_82518 : decode_any W_82518 = Some (Load SZ8 true 28 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8251c : bv 32 := 0x02813783.
Lemma F_8251c : fetch_word Ubsan.M.loaded_segments (0x8251c : word) = Some W_8251c.
Proof. vm_refl. Qed.
Lemma D_8251c : decode_any W_8251c = Some (Load SZ8 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82520 : bv 32 := 0x41c7833b.
Lemma F_82520 : fetch_word Ubsan.M.loaded_segments (0x82520 : word) = Some W_82520.
Proof. vm_refl. Qed.
Lemma D_82520 : decode_any W_82520 = Some (Op32 ALU_SUB 6 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82524 : bv 32 := 0x03813803.
Lemma F_82524 : fetch_word Ubsan.M.loaded_segments (0x82524 : word) = Some W_82524.
Proof. vm_refl. Qed.
Lemma D_82524 : decode_any W_82524 = Some (Load SZ8 true 16 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82528 : bv 32 := 0x03013783.
Lemma F_82528 : fetch_word Ubsan.M.loaded_segments (0x82528 : word) = Some W_82528.
Proof. vm_refl. Qed.
Lemma D_82528 : decode_any W_82528 = Some (Load SZ8 true 15 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8252c : bv 32 := 0x01078833.
Lemma F_8252c : fetch_word Ubsan.M.loaded_segments (0x8252c : word) = Some W_8252c.
Proof. vm_refl. Qed.
Lemma D_8252c : decode_any W_8252c = Some (Op ALU_ADD 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82530 : bv 32 := 0x04813c03.
Lemma F_82530 : fetch_word Ubsan.M.loaded_segments (0x82530 : word) = Some W_82530.
Proof. vm_refl. Qed.
Lemma D_82530 : decode_any W_82530 = Some (Load SZ8 true 24 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82534 : bv 32 := 0x43fc5393.
Lemma F_82534 : fetch_word Ubsan.M.loaded_segments (0x82534 : word) = Some W_82534.
Proof. vm_refl. Qed.
Lemma D_82534 : decode_any W_82534 = Some (ShiftImm ALU_SRA 7 24 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82538 : bv 32 := 0x00072793.
Lemma F_82538 : fetch_word Ubsan.M.loaded_segments (0x82538 : word) = Some W_82538.
Proof. vm_refl. Qed.
Lemma D_82538 : decode_any W_82538 = Some (OpImm ALU_SLT 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8253c : bv 32 := 0x0183f3b3.
Lemma F_8253c : fetch_word Ubsan.M.loaded_segments (0x8253c : word) = Some W_8253c.
Proof. vm_refl. Qed.
Lemma D_8253c : decode_any W_8253c = Some (Op ALU_AND 7 7 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82540 : bv 32 := 0x41c80e3b.
Lemma F_82540 : fetch_word Ubsan.M.loaded_segments (0x82540 : word) = Some W_82540.
Proof. vm_refl. Qed.
Lemma D_82540 : decode_any W_82540 = Some (Op32 ALU_SUB 28 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82544 : bv 32 := 0x011a8833.
Lemma F_82544 : fetch_word Ubsan.M.loaded_segments (0x82544 : word) = Some W_82544.
Proof. vm_refl. Qed.
Lemma D_82544 : decode_any W_82544 = Some (Op ALU_ADD 16 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82548 : bv 32 := 0x04013c03.
Lemma F_82548 : fetch_word Ubsan.M.loaded_segments (0x82548 : word) = Some W_82548.
Proof. vm_refl. Qed.
Lemma D_82548 : decode_any W_82548 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8254c : bv 32 := 0x418e0e3b.
Lemma F_8254c : fetch_word Ubsan.M.loaded_segments (0x8254c : word) = Some W_8254c.
Proof. vm_refl. Qed.
Lemma D_8254c : decode_any W_8254c = Some (Op32 ALU_SUB 28 28 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82550 : bv 32 := 0x007e03bb.
Lemma F_82550 : fetch_word Ubsan.M.loaded_segments (0x82550 : word) = Some W_82550.
Proof. vm_refl. Qed.
Lemma D_82550 : decode_any W_82550 = Some (Op32 ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82554 : bv 32 := 0x43f3de13.
Lemma F_82554 : fetch_word Ubsan.M.loaded_segments (0x82554 : word) = Some W_82554.
Proof. vm_refl. Qed.
Lemma D_82554 : decode_any W_82554 = Some (ShiftImm ALU_SRA 28 7 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82558 : bv 32 := 0x007e73b3.
Lemma F_82558 : fetch_word Ubsan.M.loaded_segments (0x82558 : word) = Some W_82558.
Proof. vm_refl. Qed.
Lemma D_82558 : decode_any W_82558 = Some (Op ALU_AND 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8255c : bv 32 := 0x407303bb.
Lemma F_8255c : fetch_word Ubsan.M.loaded_segments (0x8255c : word) = Some W_8255c.
Proof. vm_refl. Qed.
Lemma D_8255c : decode_any W_8255c = Some (Op32 ALU_SUB 7 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82560 : bv 32 := 0x0009ae13.
Lemma F_82560 : fetch_word Ubsan.M.loaded_segments (0x82560 : word) = Some W_82560.
Proof. vm_refl. Qed.
Lemma D_82560 : decode_any W_82560 = Some (OpImm ALU_SLT 28 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82564 : bv 32 := 0x000a0993.
Lemma F_82564 : fetch_word Ubsan.M.loaded_segments (0x82564 : word) = Some W_82564.
Proof. vm_refl. Qed.
Lemma D_82564 : decode_any W_82564 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82568 : bv 32 := 0xf80a06e3.
Lemma F_82568 : fetch_word Ubsan.M.loaded_segments (0x82568 : word) = Some W_82568.
Proof. vm_refl. Qed.
Lemma D_82568 : decode_any W_82568 = Some (Branch BC_EQ 20 0 8076, 4%Z).
Proof. vm_refl. Qed.

Definition W_8256c : bv 32 := 0xf80294e3.
Lemma F_8256c : fetch_word Ubsan.M.loaded_segments (0x8256c : word) = Some W_8256c.
Proof. vm_refl. Qed.
Lemma D_8256c : decode_any W_8256c = Some (Branch BC_NE 5 0 8072, 4%Z).
Proof. vm_refl. Qed.

Definition W_82570 : bv 32 := 0x00ba8c33.
Lemma F_82570 : fetch_word Ubsan.M.loaded_segments (0x82570 : word) = Some W_82570.
Proof. vm_refl. Qed.
Lemma D_82570 : decode_any W_82570 = Some (Op ALU_ADD 24 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82574 : bv 32 := 0xf80c00e3.
Lemma F_82574 : fetch_word Ubsan.M.loaded_segments (0x82574 : word) = Some W_82574.
Proof. vm_refl. Qed.
Lemma D_82574 : decode_any W_82574 = Some (Branch BC_EQ 24 0 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_82578 : bv 32 := 0x000a2303.
Lemma F_82578 : fetch_word Ubsan.M.loaded_segments (0x82578 : word) = Some W_82578.
Proof. vm_refl. Qed.
Lemma D_82578 : decode_any W_82578 = Some (Load SZ4 true 6 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8257c : bv 32 := 0x000c2c83.
Lemma F_8257c : fetch_word Ubsan.M.loaded_segments (0x8257c : word) = Some W_8257c.
Proof. vm_refl. Qed.
Lemma D_8257c : decode_any W_8257c = Some (Load SZ4 true 25 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82580 : bv 32 := 0x00c37d33.
Lemma F_82580 : fetch_word Ubsan.M.loaded_segments (0x82580 : word) = Some W_82580.
Proof. vm_refl. Qed.
Lemma D_82580 : decode_any W_82580 = Some (Op ALU_AND 26 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82584 : bv 32 := 0xfff34313.
Lemma F_82584 : fetch_word Ubsan.M.loaded_segments (0x82584 : word) = Some W_82584.
Proof. vm_refl. Qed.
Lemma D_82584 : decode_any W_82584 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82588 : bv 32 := 0x006ce333.
Lemma F_82588 : fetch_word Ubsan.M.loaded_segments (0x82588 : word) = Some W_82588.
Proof. vm_refl. Qed.
Lemma D_82588 : decode_any W_82588 = Some (Op ALU_OR 6 25 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8258c : bv 32 := 0x01737333.
Lemma F_8258c : fetch_word Ubsan.M.loaded_segments (0x8258c : word) = Some W_8258c.
Proof. vm_refl. Qed.
Lemma D_8258c : decode_any W_8258c = Some (Op ALU_AND 6 6 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_82590 : bv 32 := 0x01a36333.
Lemma F_82590 : fetch_word Ubsan.M.loaded_segments (0x82590 : word) = Some W_82590.
Proof. vm_refl. Qed.
Lemma D_82590 : decode_any W_82590 = Some (Op ALU_OR 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_82594 : bv 32 := 0x01368cb3.
Lemma F_82594 : fetch_word Ubsan.M.loaded_segments (0x82594 : word) = Some W_82594.
Proof. vm_refl. Qed.
Lemma D_82594 : decode_any W_82594 = Some (Op ALU_ADD 25 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82598 : bv 32 := 0x006a2023.
Lemma F_82598 : fetch_word Ubsan.M.loaded_segments (0x82598 : word) = Some W_82598.
Proof. vm_refl. Qed.
Lemma D_82598 : decode_any W_82598 = Some (Store SZ4 20 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8259c : bv 32 := 0xf40c8ce3.
Lemma F_8259c : fetch_word Ubsan.M.loaded_segments (0x8259c : word) = Some W_8259c.
Proof. vm_refl. Qed.
Lemma D_8259c : decode_any W_8259c = Some (Branch BC_EQ 25 0 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_825a0 : bv 32 := 0x013cb333.
Lemma F_825a0 : fetch_word Ubsan.M.loaded_segments (0x825a0 : word) = Some W_825a0.
Proof. vm_refl. Qed.
Lemma D_825a0 : decode_any W_825a0 = Some (Op ALU_SLTU 6 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_825a4 : bv 32 := 0x00f34333.
Lemma F_825a4 : fetch_word Ubsan.M.loaded_segments (0x825a4 : word) = Some W_825a4.
Proof. vm_refl. Qed.
Lemma D_825a4 : decode_any W_825a4 = Some (Op ALU_XOR 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_825a8 : bv 32 := 0x00134313.
Lemma F_825a8 : fetch_word Ubsan.M.loaded_segments (0x825a8 : word) = Some W_825a8.
Proof. vm_refl. Qed.
Lemma D_825a8 : decode_any W_825a8 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_825ac : bv 32 := 0xf40304e3.
Lemma F_825ac : fetch_word Ubsan.M.loaded_segments (0x825ac : word) = Some W_825ac.
Proof. vm_refl. Qed.
Lemma D_825ac : decode_any W_825ac = Some (Branch BC_EQ 6 0 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_825b0 : bv 32 := 0x00b80333.
Lemma F_825b0 : fetch_word Ubsan.M.loaded_segments (0x825b0 : word) = Some W_825b0.
Proof. vm_refl. Qed.
Lemma D_825b0 : decode_any W_825b0 = Some (Op ALU_ADD 6 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_825b4 : bv 32 := 0xf40300e3.
Lemma F_825b4 : fetch_word Ubsan.M.loaded_segments (0x825b4 : word) = Some W_825b4.
Proof. vm_refl. Qed.
Lemma D_825b4 : decode_any W_825b4 = Some (Branch BC_EQ 6 0 8000, 4%Z).
Proof. vm_refl. Qed.

Definition W_825b8 : bv 32 := 0x01833333.
Lemma F_825b8 : fetch_word Ubsan.M.loaded_segments (0x825b8 : word) = Some W_825b8.
Proof. vm_refl. Qed.
Lemma D_825b8 : decode_any W_825b8 = Some (Op ALU_SLTU 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_825bc : bv 32 := 0x01c34333.
Lemma F_825bc : fetch_word Ubsan.M.loaded_segments (0x825bc : word) = Some W_825bc.
Proof. vm_refl. Qed.
Lemma D_825bc : decode_any W_825bc = Some (Op ALU_XOR 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_825c0 : bv 32 := 0x00134313.
Lemma F_825c0 : fetch_word Ubsan.M.loaded_segments (0x825c0 : word) = Some W_825c0.
Proof. vm_refl. Qed.
Lemma D_825c0 : decode_any W_825c0 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_825c4 : bv 32 := 0xf20308e3.
Lemma F_825c4 : fetch_word Ubsan.M.loaded_segments (0x825c4 : word) = Some W_825c4.
Proof. vm_refl. Qed.
Lemma D_825c4 : decode_any W_825c4 = Some (Branch BC_EQ 6 0 7984, 4%Z).
Proof. vm_refl. Qed.

Definition W_825c8 : bv 32 := 0x0013839b.
Lemma F_825c8 : fetch_word Ubsan.M.loaded_segments (0x825c8 : word) = Some W_825c8.
Proof. vm_refl. Qed.
Lemma D_825c8 : decode_any W_825c8 = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_825cc : bv 32 := 0x011585b3.
Lemma F_825cc : fetch_word Ubsan.M.loaded_segments (0x825cc : word) = Some W_825cc.
Proof. vm_refl. Qed.
Lemma D_825cc : decode_any W_825cc = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_825d0 : bv 32 := 0x00da0a33.
Lemma F_825d0 : fetch_word Ubsan.M.loaded_segments (0x825d0 : word) = Some W_825d0.
Proof. vm_refl. Qed.
Lemma D_825d0 : decode_any W_825d0 = Some (Op ALU_ADD 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_825d4 : bv 32 := 0x000c8993.
Lemma F_825d4 : fetch_word Ubsan.M.loaded_segments (0x825d4 : word) = Some W_825d4.
Proof. vm_refl. Qed.
Lemma D_825d4 : decode_any W_825d4 = Some (OpImm ALU_ADD 19 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_825d8 : bv 32 := 0xf80398e3.
Lemma F_825d8 : fetch_word Ubsan.M.loaded_segments (0x825d8 : word) = Some W_825d8.
Proof. vm_refl. Qed.
Lemma D_825d8 : decode_any W_825d8 = Some (Branch BC_NE 7 0 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_825dc : bv 32 := 0x100b1063.
Lemma F_825dc : fetch_word Ubsan.M.loaded_segments (0x825dc : word) = Some W_825dc.
Proof. vm_refl. Qed.
Lemma D_825dc : decode_any W_825dc = Some (Branch BC_NE 22 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_825e0 : bv 32 := 0x00000593.
Lemma F_825e0 : fetch_word Ubsan.M.loaded_segments (0x825e0 : word) = Some W_825e0.
Proof. vm_refl. Qed.
Lemma D_825e0 : decode_any W_825e0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_825e4 : bv 32 := 0x00271613.
Lemma F_825e4 : fetch_word Ubsan.M.loaded_segments (0x825e4 : word) = Some W_825e4.
Proof. vm_refl. Qed.
Lemma D_825e4 : decode_any W_825e4 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_825e8 : bv 32 := 0x05813303.
Lemma F_825e8 : fetch_word Ubsan.M.loaded_segments (0x825e8 : word) = Some W_825e8.
Proof. vm_refl. Qed.
Lemma D_825e8 : decode_any W_825e8 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_825ec : bv 32 := 0x00231693.
Lemma F_825ec : fetch_word Ubsan.M.loaded_segments (0x825ec : word) = Some W_825ec.
Proof. vm_refl. Qed.
Lemma D_825ec : decode_any W_825ec = Some (ShiftImm ALU_SLL 13 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_825f0 : bv 32 := 0x00397793.
Lemma F_825f0 : fetch_word Ubsan.M.loaded_segments (0x825f0 : word) = Some W_825f0.
Proof. vm_refl. Qed.
Lemma D_825f0 : decode_any W_825f0 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_825f4 : bv 32 := 0x00347813.
Lemma F_825f4 : fetch_word Ubsan.M.loaded_segments (0x825f4 : word) = Some W_825f4.
Proof. vm_refl. Qed.
Lemma D_825f4 : decode_any W_825f4 = Some (OpImm ALU_AND 16 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_825f8 : bv 32 := 0x002f9893.
Lemma F_825f8 : fetch_word Ubsan.M.loaded_segments (0x825f8 : word) = Some W_825f8.
Proof. vm_refl. Qed.
Lemma D_825f8 : decode_any W_825f8 = Some (ShiftImm ALU_SLL 17 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_825fc : bv 32 := 0x00072293.
Lemma F_825fc : fetch_word Ubsan.M.loaded_segments (0x825fc : word) = Some W_825fc.
Proof. vm_refl. Qed.
Lemma D_825fc : decode_any W_825fc = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82600 : bv 32 := 0x00032393.
Lemma F_82600 : fetch_word Ubsan.M.loaded_segments (0x82600 : word) = Some W_82600.
Proof. vm_refl. Qed.
Lemma D_82600 : decode_any W_82600 = Some (OpImm ALU_SLT 7 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82604 : bv 32 := 0x00183993.
Lemma F_82604 : fetch_word Ubsan.M.loaded_segments (0x82604 : word) = Some W_82604.
Proof. vm_refl. Qed.
Lemma D_82604 : decode_any W_82604 = Some (OpImm ALU_SLTU 19 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82608 : bv 32 := 0x0017ba13.
Lemma F_82608 : fetch_word Ubsan.M.loaded_segments (0x82608 : word) = Some W_82608.
Proof. vm_refl. Qed.
Lemma D_82608 : decode_any W_82608 = Some (OpImm ALU_SLTU 20 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8260c : bv 32 := 0x00090a93.
Lemma F_8260c : fetch_word Ubsan.M.loaded_segments (0x8260c : word) = Some W_8260c.
Proof. vm_refl. Qed.
Lemma D_8260c : decode_any W_8260c = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82610 : bv 32 := 0x00040b13.
Lemma F_82610 : fetch_word Ubsan.M.loaded_segments (0x82610 : word) = Some W_82610.
Proof. vm_refl. Qed.
Lemma D_82610 : decode_any W_82610 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82614 : bv 32 := 0x060f8663.
Lemma F_82614 : fetch_word Ubsan.M.loaded_segments (0x82614 : word) = Some W_82614.
Proof. vm_refl. Qed.
Lemma D_82614 : decode_any W_82614 = Some (Branch BC_EQ 31 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_82618 : bv 32 := 0x00000793.
Lemma F_82618 : fetch_word Ubsan.M.loaded_segments (0x82618 : word) = Some W_82618.
Proof. vm_refl. Qed.
Lemma D_82618 : decode_any W_82618 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8261c : bv 32 := 0x01203833.
Lemma F_8261c : fetch_word Ubsan.M.loaded_segments (0x8261c : word) = Some W_8261c.
Proof. vm_refl. Qed.
Lemma D_8261c : decode_any W_8261c = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82620 : bv 32 := 0x00803e33.
Lemma F_82620 : fetch_word Ubsan.M.loaded_segments (0x82620 : word) = Some W_82620.
Proof. vm_refl. Qed.
Lemma D_82620 : decode_any W_82620 = Some (Op ALU_SLTU 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82624 : bv 32 := 0x010a7bb3.
Lemma F_82624 : fetch_word Ubsan.M.loaded_segments (0x82624 : word) = Some W_82624.
Proof. vm_refl. Qed.
Lemma D_82624 : decode_any W_82624 = Some (Op ALU_AND 23 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82628 : bv 32 := 0x01c9fc33.
Lemma F_82628 : fetch_word Ubsan.M.loaded_segments (0x82628 : word) = Some W_82628.
Proof. vm_refl. Qed.
Lemma D_82628 : decode_any W_82628 = Some (Op ALU_AND 24 19 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8262c : bv 32 := 0x00fa8333.
Lemma F_8262c : fetch_word Ubsan.M.loaded_segments (0x8262c : word) = Some W_8262c.
Proof. vm_refl. Qed.
Lemma D_8262c : decode_any W_8262c = Some (Op ALU_ADD 6 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82630 : bv 32 := 0xed2362e3.
Lemma F_82630 : fetch_word Ubsan.M.loaded_segments (0x82630 : word) = Some W_82630.
Proof. vm_refl. Qed.
Lemma D_82630 : decode_any W_82630 = Some (Branch BC_LTU 6 18 7876, 4%Z).
Proof. vm_refl. Qed.

Definition W_82634 : bv 32 := 0x00133313.
Lemma F_82634 : fetch_word Ubsan.M.loaded_segments (0x82634 : word) = Some W_82634.
Proof. vm_refl. Qed.
Lemma D_82634 : decode_any W_82634 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82638 : bv 32 := 0x00684333.
Lemma F_82638 : fetch_word Ubsan.M.loaded_segments (0x82638 : word) = Some W_82638.
Proof. vm_refl. Qed.
Lemma D_82638 : decode_any W_82638 = Some (Op ALU_XOR 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8263c : bv 32 := 0xea030ce3.
Lemma F_8263c : fetch_word Ubsan.M.loaded_segments (0x8263c : word) = Some W_8263c.
Proof. vm_refl. Qed.
Lemma D_8263c : decode_any W_8263c = Some (Branch BC_EQ 6 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_82640 : bv 32 := 0xea0b8ae3.
Lemma F_82640 : fetch_word Ubsan.M.loaded_segments (0x82640 : word) = Some W_82640.
Proof. vm_refl. Qed.
Lemma D_82640 : decode_any W_82640 = Some (Branch BC_EQ 23 0 7860, 4%Z).
Proof. vm_refl. Qed.

Definition W_82644 : bv 32 := 0x00fb0333.
Lemma F_82644 : fetch_word Ubsan.M.loaded_segments (0x82644 : word) = Some W_82644.
Proof. vm_refl. Qed.
Lemma D_82644 : decode_any W_82644 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82648 : bv 32 := 0xea8366e3.
Lemma F_82648 : fetch_word Ubsan.M.loaded_segments (0x82648 : word) = Some W_82648.
Proof. vm_refl. Qed.
Lemma D_82648 : decode_any W_82648 = Some (Branch BC_LTU 6 8 7852, 4%Z).
Proof. vm_refl. Qed.

Definition W_8264c : bv 32 := 0x00133313.
Lemma F_8264c : fetch_word Ubsan.M.loaded_segments (0x8264c : word) = Some W_8264c.
Proof. vm_refl. Qed.
Lemma D_8264c : decode_any W_8264c = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82650 : bv 32 := 0x006e4333.
Lemma F_82650 : fetch_word Ubsan.M.loaded_segments (0x82650 : word) = Some W_82650.
Proof. vm_refl. Qed.
Lemma D_82650 : decode_any W_82650 = Some (Op ALU_XOR 6 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82654 : bv 32 := 0xea0300e3.
Lemma F_82654 : fetch_word Ubsan.M.loaded_segments (0x82654 : word) = Some W_82654.
Proof. vm_refl. Qed.
Lemma D_82654 : decode_any W_82654 = Some (Branch BC_EQ 6 0 7840, 4%Z).
Proof. vm_refl. Qed.

Definition W_82658 : bv 32 := 0xe80c0ee3.
Lemma F_82658 : fetch_word Ubsan.M.loaded_segments (0x82658 : word) = Some W_82658.
Proof. vm_refl. Qed.
Lemma D_82658 : decode_any W_82658 = Some (Branch BC_EQ 24 0 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_8265c : bv 32 := 0x00f90333.
Lemma F_8265c : fetch_word Ubsan.M.loaded_segments (0x8265c : word) = Some W_8265c.
Proof. vm_refl. Qed.
Lemma D_8265c : decode_any W_8265c = Some (Op ALU_ADD 6 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82660 : bv 32 := 0x00f40cb3.
Lemma F_82660 : fetch_word Ubsan.M.loaded_segments (0x82660 : word) = Some W_82660.
Proof. vm_refl. Qed.
Lemma D_82660 : decode_any W_82660 = Some (Op ALU_ADD 25 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82664 : bv 32 := 0x000cad03.
Lemma F_82664 : fetch_word Ubsan.M.loaded_segments (0x82664 : word) = Some W_82664.
Proof. vm_refl. Qed.
Lemma D_82664 : decode_any W_82664 = Some (Load SZ4 true 26 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82668 : bv 32 := 0x00032303.
Lemma F_82668 : fetch_word Ubsan.M.loaded_segments (0x82668 : word) = Some W_82668.
Proof. vm_refl. Qed.
Lemma D_82668 : decode_any W_82668 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8266c : bv 32 := 0xfffd4d13.
Lemma F_8266c : fetch_word Ubsan.M.loaded_segments (0x8266c : word) = Some W_8266c.
Proof. vm_refl. Qed.
Lemma D_8266c : decode_any W_8266c = Some (OpImm ALU_XOR 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82670 : bv 32 := 0x01a36333.
Lemma F_82670 : fetch_word Ubsan.M.loaded_segments (0x82670 : word) = Some W_82670.
Proof. vm_refl. Qed.
Lemma D_82670 : decode_any W_82670 = Some (Op ALU_OR 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_82674 : bv 32 := 0x00478793.
Lemma F_82674 : fetch_word Ubsan.M.loaded_segments (0x82674 : word) = Some W_82674.
Proof. vm_refl. Qed.
Lemma D_82674 : decode_any W_82674 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_82678 : bv 32 := 0x006ca023.
Lemma F_82678 : fetch_word Ubsan.M.loaded_segments (0x82678 : word) = Some W_82678.
Proof. vm_refl. Qed.
Lemma D_82678 : decode_any W_82678 = Some (Store SZ4 25 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8267c : bv 32 := 0xfaf898e3.
Lemma F_8267c : fetch_word Ubsan.M.loaded_segments (0x8267c : word) = Some W_8267c.
Proof. vm_refl. Qed.
Lemma D_8267c : decode_any W_8267c = Some (Branch BC_NE 17 15 8112, 4%Z).
Proof. vm_refl. Qed.

Definition W_82680 : bv 32 := 0x00c407b3.
Lemma F_82680 : fetch_word Ubsan.M.loaded_segments (0x82680 : word) = Some W_82680.
Proof. vm_refl. Qed.
Lemma D_82680 : decode_any W_82680 = Some (Op ALU_ADD 15 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82684 : bv 32 := 0x00803833.
Lemma F_82684 : fetch_word Ubsan.M.loaded_segments (0x82684 : word) = Some W_82684.
Proof. vm_refl. Qed.
Lemma D_82684 : decode_any W_82684 = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82688 : bv 32 := 0x0017b313.
Lemma F_82688 : fetch_word Ubsan.M.loaded_segments (0x82688 : word) = Some W_82688.
Proof. vm_refl. Qed.
Lemma D_82688 : decode_any W_82688 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8268c : bv 32 := 0xe66804e3.
Lemma F_8268c : fetch_word Ubsan.M.loaded_segments (0x8268c : word) = Some W_8268c.
Proof. vm_refl. Qed.
Lemma D_8268c : decode_any W_8268c = Some (Branch BC_EQ 16 6 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_82690 : bv 32 := 0x0087b7b3.
Lemma F_82690 : fetch_word Ubsan.M.loaded_segments (0x82690 : word) = Some W_82690.
Proof. vm_refl. Qed.
Lemma D_82690 : decode_any W_82690 = Some (Op ALU_SLTU 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82694 : bv 32 := 0x0057c7b3.
Lemma F_82694 : fetch_word Ubsan.M.loaded_segments (0x82694 : word) = Some W_82694.
Proof. vm_refl. Qed.
Lemma D_82694 : decode_any W_82694 = Some (Op ALU_XOR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82698 : bv 32 := 0x0017c793.
Lemma F_82698 : fetch_word Ubsan.M.loaded_segments (0x82698 : word) = Some W_82698.
Proof. vm_refl. Qed.
Lemma D_82698 : decode_any W_82698 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8269c : bv 32 := 0xe4078ce3.
Lemma F_8269c : fetch_word Ubsan.M.loaded_segments (0x8269c : word) = Some W_8269c.
Proof. vm_refl. Qed.
Lemma D_8269c : decode_any W_8269c = Some (Branch BC_EQ 15 0 7768, 4%Z).
Proof. vm_refl. Qed.

Definition W_826a0 : bv 32 := 0x012687b3.
Lemma F_826a0 : fetch_word Ubsan.M.loaded_segments (0x826a0 : word) = Some W_826a0.
Proof. vm_refl. Qed.
Lemma D_826a0 : decode_any W_826a0 = Some (Op ALU_ADD 15 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_826a4 : bv 32 := 0x01203833.
Lemma F_826a4 : fetch_word Ubsan.M.loaded_segments (0x826a4 : word) = Some W_826a4.
Proof. vm_refl. Qed.
Lemma D_826a4 : decode_any W_826a4 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_826a8 : bv 32 := 0x0017b313.
Lemma F_826a8 : fetch_word Ubsan.M.loaded_segments (0x826a8 : word) = Some W_826a8.
Proof. vm_refl. Qed.
Lemma D_826a8 : decode_any W_826a8 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_826ac : bv 32 := 0xe46804e3.
Lemma F_826ac : fetch_word Ubsan.M.loaded_segments (0x826ac : word) = Some W_826ac.
Proof. vm_refl. Qed.
Lemma D_826ac : decode_any W_826ac = Some (Branch BC_EQ 16 6 7752, 4%Z).
Proof. vm_refl. Qed.

Definition W_826b0 : bv 32 := 0x0127b833.
Lemma F_826b0 : fetch_word Ubsan.M.loaded_segments (0x826b0 : word) = Some W_826b0.
Proof. vm_refl. Qed.
Lemma D_826b0 : decode_any W_826b0 = Some (Op ALU_SLTU 16 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_826b4 : bv 32 := 0x00784833.
Lemma F_826b4 : fetch_word Ubsan.M.loaded_segments (0x826b4 : word) = Some W_826b4.
Proof. vm_refl. Qed.
Lemma D_826b4 : decode_any W_826b4 = Some (Op ALU_XOR 16 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_826b8 : bv 32 := 0x00184813.
Lemma F_826b8 : fetch_word Ubsan.M.loaded_segments (0x826b8 : word) = Some W_826b8.
Proof. vm_refl. Qed.
Lemma D_826b8 : decode_any W_826b8 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_826bc : bv 32 := 0xe2080ce3.
Lemma F_826bc : fetch_word Ubsan.M.loaded_segments (0x826bc : word) = Some W_826bc.
Proof. vm_refl. Qed.
Lemma D_826bc : decode_any W_826bc = Some (Branch BC_EQ 16 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_826c0 : bv 32 := 0x00c40433.
Lemma F_826c0 : fetch_word Ubsan.M.loaded_segments (0x826c0 : word) = Some W_826c0.
Proof. vm_refl. Qed.
Lemma D_826c0 : decode_any W_826c0 = Some (Op ALU_ADD 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_826c4 : bv 32 := 0x0015859b.
Lemma F_826c4 : fetch_word Ubsan.M.loaded_segments (0x826c4 : word) = Some W_826c4.
Proof. vm_refl. Qed.
Lemma D_826c4 : decode_any W_826c4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_826c8 : bv 32 := 0x00cb0b33.
Lemma F_826c8 : fetch_word Ubsan.M.loaded_segments (0x826c8 : word) = Some W_826c8.
Proof. vm_refl. Qed.
Lemma D_826c8 : decode_any W_826c8 = Some (Op ALU_ADD 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_826cc : bv 32 := 0x00da8ab3.
Lemma F_826cc : fetch_word Ubsan.M.loaded_segments (0x826cc : word) = Some W_826cc.
Proof. vm_refl. Qed.
Lemma D_826cc : decode_any W_826cc = Some (Op ALU_ADD 21 21 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_826d0 : bv 32 := 0x00078913.
Lemma F_826d0 : fetch_word Ubsan.M.loaded_segments (0x826d0 : word) = Some W_826d0.
Proof. vm_refl. Qed.
Lemma D_826d0 : decode_any W_826d0 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_826d4 : bv 32 := 0x08013783.
Lemma F_826d4 : fetch_word Ubsan.M.loaded_segments (0x826d4 : word) = Some W_826d4.
Proof. vm_refl. Qed.
Lemma D_826d4 : decode_any W_826d4 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_826d8 : bv 32 := 0xf2f59ee3.
Lemma F_826d8 : fetch_word Ubsan.M.loaded_segments (0x826d8 : word) = Some W_826d8.
Proof. vm_refl. Qed.
Lemma D_826d8 : decode_any W_826d8 = Some (Branch BC_NE 11 15 7996, 4%Z).
Proof. vm_refl. Qed.

Definition W_826dc : bv 32 := 0x00048463.
Lemma F_826dc : fetch_word Ubsan.M.loaded_segments (0x826dc : word) = Some W_826dc.
Proof. vm_refl. Qed.
Lemma D_826dc : decode_any W_826dc = Some (Branch BC_EQ 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_826e0 : bv 32 := 0x6d90406f.
Lemma F_826e0 : fetch_word Ubsan.M.loaded_segments (0x826e0 : word) = Some W_826e0.
Proof. vm_refl. Qed.
Lemma D_826e0 : decode_any W_826e0 = Some (Jal 0 20184, 4%Z).
Proof. vm_refl. Qed.

Definition W_826e4 : bv 32 := 0x00357593.
Lemma F_826e4 : fetch_word Ubsan.M.loaded_segments (0x826e4 : word) = Some W_826e4.
Proof. vm_refl. Qed.
Lemma D_826e4 : decode_any W_826e4 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_826e8 : bv 32 := 0xe00596e3.
Lemma F_826e8 : fetch_word Ubsan.M.loaded_segments (0x826e8 : word) = Some W_826e8.
Proof. vm_refl. Qed.
Lemma D_826e8 : decode_any W_826e8 = Some (Branch BC_NE 11 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_826ec : bv 32 := 0xfffec613.
Lemma F_826ec : fetch_word Ubsan.M.loaded_segments (0x826ec : word) = Some W_826ec.
Proof. vm_refl. Qed.
Lemma D_826ec : decode_any W_826ec = Some (OpImm ALU_XOR 12 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_826f0 : bv 32 := 0x00271693.
Lemma F_826f0 : fetch_word Ubsan.M.loaded_segments (0x826f0 : word) = Some W_826f0.
Proof. vm_refl. Qed.
Lemma D_826f0 : decode_any W_826f0 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_826f4 : bv 32 := 0x05813e03.
Lemma F_826f4 : fetch_word Ubsan.M.loaded_segments (0x826f4 : word) = Some W_826f4.
Proof. vm_refl. Qed.
Lemma D_826f4 : decode_any W_826f4 = Some (Load SZ8 true 28 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_826f8 : bv 32 := 0x002e1793.
Lemma F_826f8 : fetch_word Ubsan.M.loaded_segments (0x826f8 : word) = Some W_826f8.
Proof. vm_refl. Qed.
Lemma D_826f8 : decode_any W_826f8 = Some (ShiftImm ALU_SLL 15 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_826fc : bv 32 := 0x03813883.
Lemma F_826fc : fetch_word Ubsan.M.loaded_segments (0x826fc : word) = Some W_826fc.
Proof. vm_refl. Qed.
Lemma D_826fc : decode_any W_826fc = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82700 : bv 32 := 0x03013803.
Lemma F_82700 : fetch_word Ubsan.M.loaded_segments (0x82700 : word) = Some W_82700.
Proof. vm_refl. Qed.
Lemma D_82700 : decode_any W_82700 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82704 : bv 32 := 0x011808b3.
Lemma F_82704 : fetch_word Ubsan.M.loaded_segments (0x82704 : word) = Some W_82704.
Proof. vm_refl. Qed.
Lemma D_82704 : decode_any W_82704 = Some (Op ALU_ADD 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82708 : bv 32 := 0x04813283.
Lemma F_82708 : fetch_word Ubsan.M.loaded_segments (0x82708 : word) = Some W_82708.
Proof. vm_refl. Qed.
Lemma D_82708 : decode_any W_82708 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8270c : bv 32 := 0x43f2d813.
Lemma F_8270c : fetch_word Ubsan.M.loaded_segments (0x8270c : word) = Some W_8270c.
Proof. vm_refl. Qed.
Lemma D_8270c : decode_any W_8270c = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82710 : bv 32 := 0x005872b3.
Lemma F_82710 : fetch_word Ubsan.M.loaded_segments (0x82710 : word) = Some W_82710.
Proof. vm_refl. Qed.
Lemma D_82710 : decode_any W_82710 = Some (Op ALU_AND 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82714 : bv 32 := 0x003f7813.
Lemma F_82714 : fetch_word Ubsan.M.loaded_segments (0x82714 : word) = Some W_82714.
Proof. vm_refl. Qed.
Lemma D_82714 : decode_any W_82714 = Some (OpImm ALU_AND 16 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82718 : bv 32 := 0x05013383.
Lemma F_82718 : fetch_word Ubsan.M.loaded_segments (0x82718 : word) = Some W_82718.
Proof. vm_refl. Qed.
Lemma D_82718 : decode_any W_82718 = Some (Load SZ8 true 7 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8271c : bv 32 := 0x02813303.
Lemma F_8271c : fetch_word Ubsan.M.loaded_segments (0x8271c : word) = Some W_8271c.
Proof. vm_refl. Qed.
Lemma D_8271c : decode_any W_8271c = Some (Load SZ8 true 6 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82720 : bv 32 := 0x4073033b.
Lemma F_82720 : fetch_word Ubsan.M.loaded_segments (0x82720 : word) = Some W_82720.
Proof. vm_refl. Qed.
Lemma D_82720 : decode_any W_82720 = Some (Op32 ALU_SUB 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82724 : bv 32 := 0x00072713.
Lemma F_82724 : fetch_word Ubsan.M.loaded_segments (0x82724 : word) = Some W_82724.
Proof. vm_refl. Qed.
Lemma D_82724 : decode_any W_82724 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82728 : bv 32 := 0x005882b3.
Lemma F_82728 : fetch_word Ubsan.M.loaded_segments (0x82728 : word) = Some W_82728.
Proof. vm_refl. Qed.
Lemma D_82728 : decode_any W_82728 = Some (Op ALU_ADD 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8272c : bv 32 := 0x00ff08b3.
Lemma F_8272c : fetch_word Ubsan.M.loaded_segments (0x8272c : word) = Some W_8272c.
Proof. vm_refl. Qed.
Lemma D_8272c : decode_any W_8272c = Some (Op ALU_ADD 17 30 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82730 : bv 32 := 0x407282bb.
Lemma F_82730 : fetch_word Ubsan.M.loaded_segments (0x82730 : word) = Some W_82730.
Proof. vm_refl. Qed.
Lemma D_82730 : decode_any W_82730 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82734 : bv 32 := 0x04013383.
Lemma F_82734 : fetch_word Ubsan.M.loaded_segments (0x82734 : word) = Some W_82734.
Proof. vm_refl. Qed.
Lemma D_82734 : decode_any W_82734 = Some (Load SZ8 true 7 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82738 : bv 32 := 0x407282bb.
Lemma F_82738 : fetch_word Ubsan.M.loaded_segments (0x82738 : word) = Some W_82738.
Proof. vm_refl. Qed.
Lemma D_82738 : decode_any W_82738 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8273c : bv 32 := 0x43f2d393.
Lemma F_8273c : fetch_word Ubsan.M.loaded_segments (0x8273c : word) = Some W_8273c.
Proof. vm_refl. Qed.
Lemma D_8273c : decode_any W_8273c = Some (ShiftImm ALU_SRA 7 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82740 : bv 32 := 0x0053f2b3.
Lemma F_82740 : fetch_word Ubsan.M.loaded_segments (0x82740 : word) = Some W_82740.
Proof. vm_refl. Qed.
Lemma D_82740 : decode_any W_82740 = Some (Op ALU_AND 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82744 : bv 32 := 0x405302bb.
Lemma F_82744 : fetch_word Ubsan.M.loaded_segments (0x82744 : word) = Some W_82744.
Proof. vm_refl. Qed.
Lemma D_82744 : decode_any W_82744 = Some (Op32 ALU_SUB 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82748 : bv 32 := 0x000e2313.
Lemma F_82748 : fetch_word Ubsan.M.loaded_segments (0x82748 : word) = Some W_82748.
Proof. vm_refl. Qed.
Lemma D_82748 : decode_any W_82748 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8274c : bv 32 := 0x00050393.
Lemma F_8274c : fetch_word Ubsan.M.loaded_segments (0x8274c : word) = Some W_8274c.
Proof. vm_refl. Qed.
Lemma D_8274c : decode_any W_8274c = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82750 : bv 32 := 0xda0502e3.
Lemma F_82750 : fetch_word Ubsan.M.loaded_segments (0x82750 : word) = Some W_82750.
Proof. vm_refl. Qed.
Lemma D_82750 : decode_any W_82750 = Some (Branch BC_EQ 10 0 7588, 4%Z).
Proof. vm_refl. Qed.

Definition W_82754 : bv 32 := 0xda0810e3.
Lemma F_82754 : fetch_word Ubsan.M.loaded_segments (0x82754 : word) = Some W_82754.
Proof. vm_refl. Qed.
Lemma D_82754 : decode_any W_82754 = Some (Branch BC_NE 16 0 7584, 4%Z).
Proof. vm_refl. Qed.

Definition W_82758 : bv 32 := 0x00bf0e33.
Lemma F_82758 : fetch_word Ubsan.M.loaded_segments (0x82758 : word) = Some W_82758.
Proof. vm_refl. Qed.
Lemma D_82758 : decode_any W_82758 = Some (Op ALU_ADD 28 30 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8275c : bv 32 := 0xd80e0ce3.
Lemma F_8275c : fetch_word Ubsan.M.loaded_segments (0x8275c : word) = Some W_8275c.
Proof. vm_refl. Qed.
Lemma D_8275c : decode_any W_8275c = Some (Branch BC_EQ 28 0 7576, 4%Z).
Proof. vm_refl. Qed.

Definition W_82760 : bv 32 := 0x00052f83.
Lemma F_82760 : fetch_word Ubsan.M.loaded_segments (0x82760 : word) = Some W_82760.
Proof. vm_refl. Qed.
Lemma D_82760 : decode_any W_82760 = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82764 : bv 32 := 0x000e2403.
Lemma F_82764 : fetch_word Ubsan.M.loaded_segments (0x82764 : word) = Some W_82764.
Proof. vm_refl. Qed.
Lemma D_82764 : decode_any W_82764 = Some (Load SZ4 true 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82768 : bv 32 := 0x00cff4b3.
Lemma F_82768 : fetch_word Ubsan.M.loaded_segments (0x82768 : word) = Some W_82768.
Proof. vm_refl. Qed.
Lemma D_82768 : decode_any W_82768 = Some (Op ALU_AND 9 31 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8276c : bv 32 := 0xffffcf93.
Lemma F_8276c : fetch_word Ubsan.M.loaded_segments (0x8276c : word) = Some W_8276c.
Proof. vm_refl. Qed.
Lemma D_8276c : decode_any W_8276c = Some (OpImm ALU_XOR 31 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82770 : bv 32 := 0x01f46fb3.
Lemma F_82770 : fetch_word Ubsan.M.loaded_segments (0x82770 : word) = Some W_82770.
Proof. vm_refl. Qed.
Lemma D_82770 : decode_any W_82770 = Some (Op ALU_OR 31 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82774 : bv 32 := 0x01dfffb3.
Lemma F_82774 : fetch_word Ubsan.M.loaded_segments (0x82774 : word) = Some W_82774.
Proof. vm_refl. Qed.
Lemma D_82774 : decode_any W_82774 = Some (Op ALU_AND 31 31 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_82778 : bv 32 := 0x009fe433.
Lemma F_82778 : fetch_word Ubsan.M.loaded_segments (0x82778 : word) = Some W_82778.
Proof. vm_refl. Qed.
Lemma D_82778 : decode_any W_82778 = Some (Op ALU_OR 8 31 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8277c : bv 32 := 0x00768fb3.
Lemma F_8277c : fetch_word Ubsan.M.loaded_segments (0x8277c : word) = Some W_8277c.
Proof. vm_refl. Qed.
Lemma D_8277c : decode_any W_8277c = Some (Op ALU_ADD 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82780 : bv 32 := 0x00852023.
Lemma F_82780 : fetch_word Ubsan.M.loaded_segments (0x82780 : word) = Some W_82780.
Proof. vm_refl. Qed.
Lemma D_82780 : decode_any W_82780 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82784 : bv 32 := 0xd60f88e3.
Lemma F_82784 : fetch_word Ubsan.M.loaded_segments (0x82784 : word) = Some W_82784.
Proof. vm_refl. Qed.
Lemma D_82784 : decode_any W_82784 = Some (Branch BC_EQ 31 0 7536, 4%Z).
Proof. vm_refl. Qed.

Definition W_82788 : bv 32 := 0x007fb3b3.
Lemma F_82788 : fetch_word Ubsan.M.loaded_segments (0x82788 : word) = Some W_82788.
Proof. vm_refl. Qed.
Lemma D_82788 : decode_any W_82788 = Some (Op ALU_SLTU 7 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8278c : bv 32 := 0x00e3c3b3.
Lemma F_8278c : fetch_word Ubsan.M.loaded_segments (0x8278c : word) = Some W_8278c.
Proof. vm_refl. Qed.
Lemma D_8278c : decode_any W_8278c = Some (Op ALU_XOR 7 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82790 : bv 32 := 0x0013c393.
Lemma F_82790 : fetch_word Ubsan.M.loaded_segments (0x82790 : word) = Some W_82790.
Proof. vm_refl. Qed.
Lemma D_82790 : decode_any W_82790 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82794 : bv 32 := 0xd60380e3.
Lemma F_82794 : fetch_word Ubsan.M.loaded_segments (0x82794 : word) = Some W_82794.
Proof. vm_refl. Qed.
Lemma D_82794 : decode_any W_82794 = Some (Branch BC_EQ 7 0 7520, 4%Z).
Proof. vm_refl. Qed.

Definition W_82798 : bv 32 := 0x00b883b3.
Lemma F_82798 : fetch_word Ubsan.M.loaded_segments (0x82798 : word) = Some W_82798.
Proof. vm_refl. Qed.
Lemma D_82798 : decode_any W_82798 = Some (Op ALU_ADD 7 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8279c : bv 32 := 0xd4038ce3.
Lemma F_8279c : fetch_word Ubsan.M.loaded_segments (0x8279c : word) = Some W_8279c.
Proof. vm_refl. Qed.
Lemma D_8279c : decode_any W_8279c = Some (Branch BC_EQ 7 0 7512, 4%Z).
Proof. vm_refl. Qed.

Definition W_827a0 : bv 32 := 0x01c3b3b3.
Lemma F_827a0 : fetch_word Ubsan.M.loaded_segments (0x827a0 : word) = Some W_827a0.
Proof. vm_refl. Qed.
Lemma D_827a0 : decode_any W_827a0 = Some (Op ALU_SLTU 7 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_827a4 : bv 32 := 0x0063c3b3.
Lemma F_827a4 : fetch_word Ubsan.M.loaded_segments (0x827a4 : word) = Some W_827a4.
Proof. vm_refl. Qed.
Lemma D_827a4 : decode_any W_827a4 = Some (Op ALU_XOR 7 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_827a8 : bv 32 := 0x0013c393.
Lemma F_827a8 : fetch_word Ubsan.M.loaded_segments (0x827a8 : word) = Some W_827a8.
Proof. vm_refl. Qed.
Lemma D_827a8 : decode_any W_827a8 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_827ac : bv 32 := 0xd40384e3.
Lemma F_827ac : fetch_word Ubsan.M.loaded_segments (0x827ac : word) = Some W_827ac.
Proof. vm_refl. Qed.
Lemma D_827ac : decode_any W_827ac = Some (Branch BC_EQ 7 0 7496, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b0 : bv 32 := 0x0012829b.
Lemma F_827b0 : fetch_word Ubsan.M.loaded_segments (0x827b0 : word) = Some W_827b0.
Proof. vm_refl. Qed.
Lemma D_827b0 : decode_any W_827b0 = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b4 : bv 32 := 0x00f585b3.
Lemma F_827b4 : fetch_word Ubsan.M.loaded_segments (0x827b4 : word) = Some W_827b4.
Proof. vm_refl. Qed.
Lemma D_827b4 : decode_any W_827b4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b8 : bv 32 := 0x00d50533.
Lemma F_827b8 : fetch_word Ubsan.M.loaded_segments (0x827b8 : word) = Some W_827b8.
Proof. vm_refl. Qed.
Lemma D_827b8 : decode_any W_827b8 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_827bc : bv 32 := 0x000f8393.
Lemma F_827bc : fetch_word Ubsan.M.loaded_segments (0x827bc : word) = Some W_827bc.
Proof. vm_refl. Qed.
Lemma D_827bc : decode_any W_827bc = Some (OpImm ALU_ADD 7 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c0 : bv 32 := 0xf80298e3.
Lemma F_827c0 : fetch_word Ubsan.M.loaded_segments (0x827c0 : word) = Some W_827c0.
Proof. vm_refl. Qed.
Lemma D_827c0 : decode_any W_827c0 = Some (Branch BC_NE 5 0 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c4 : bv 32 := 0x5f50406f.
Lemma F_827c4 : fetch_word Ubsan.M.loaded_segments (0x827c4 : word) = Some W_827c4.
Proof. vm_refl. Qed.
Lemma D_827c4 : decode_any W_827c4 = Some (Jal 0 19956, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c8 : bv 32 := 0x0e008063.
Lemma F_827c8 : fetch_word Ubsan.M.loaded_segments (0x827c8 : word) = Some W_827c8.
Proof. vm_refl. Qed.
Lemma D_827c8 : decode_any W_827c8 = Some (Branch BC_EQ 1 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_827cc : bv 32 := 0x003a7593.
Lemma F_827cc : fetch_word Ubsan.M.loaded_segments (0x827cc : word) = Some W_827cc.
Proof. vm_refl. Qed.
Lemma D_827cc : decode_any W_827cc = Some (OpImm ALU_AND 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d0 : bv 32 := 0xd20592e3.
Lemma F_827d0 : fetch_word Ubsan.M.loaded_segments (0x827d0 : word) = Some W_827d0.
Proof. vm_refl. Qed.
Lemma D_827d0 : decode_any W_827d0 = Some (Branch BC_NE 11 0 7460, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d4 : bv 32 := 0xfffbc613.
Lemma F_827d4 : fetch_word Ubsan.M.loaded_segments (0x827d4 : word) = Some W_827d4.
Proof. vm_refl. Qed.
Lemma D_827d4 : decode_any W_827d4 = Some (OpImm ALU_XOR 12 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d8 : bv 32 := 0x00271693.
Lemma F_827d8 : fetch_word Ubsan.M.loaded_segments (0x827d8 : word) = Some W_827d8.
Proof. vm_refl. Qed.
Lemma D_827d8 : decode_any W_827d8 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_827dc : bv 32 := 0x05813983.
Lemma F_827dc : fetch_word Ubsan.M.loaded_segments (0x827dc : word) = Some W_827dc.
Proof. vm_refl. Qed.
Lemma D_827dc : decode_any W_827dc = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e0 : bv 32 := 0x00299893.
Lemma F_827e0 : fetch_word Ubsan.M.loaded_segments (0x827e0 : word) = Some W_827e0.
Proof. vm_refl. Qed.
Lemma D_827e0 : decode_any W_827e0 = Some (ShiftImm ALU_SLL 17 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e4 : bv 32 := 0x003af293.
Lemma F_827e4 : fetch_word Ubsan.M.loaded_segments (0x827e4 : word) = Some W_827e4.
Proof. vm_refl. Qed.
Lemma D_827e4 : decode_any W_827e4 = Some (OpImm ALU_AND 5 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e8 : bv 32 := 0x05013e03.
Lemma F_827e8 : fetch_word Ubsan.M.loaded_segments (0x827e8 : word) = Some W_827e8.
Proof. vm_refl. Qed.
Lemma D_827e8 : decode_any W_827e8 = Some (Load SZ8 true 28 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_827ec : bv 32 := 0x02813783.
Lemma F_827ec : fetch_word Ubsan.M.loaded_segments (0x827ec : word) = Some W_827ec.
Proof. vm_refl. Qed.
Lemma D_827ec : decode_any W_827ec = Some (Load SZ8 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f0 : bv 32 := 0x41c7833b.
Lemma F_827f0 : fetch_word Ubsan.M.loaded_segments (0x827f0 : word) = Some W_827f0.
Proof. vm_refl. Qed.
Lemma D_827f0 : decode_any W_827f0 = Some (Op32 ALU_SUB 6 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f4 : bv 32 := 0x03813803.
Lemma F_827f4 : fetch_word Ubsan.M.loaded_segments (0x827f4 : word) = Some W_827f4.
Proof. vm_refl. Qed.
Lemma D_827f4 : decode_any W_827f4 = Some (Load SZ8 true 16 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f8 : bv 32 := 0x03013783.
Lemma F_827f8 : fetch_word Ubsan.M.loaded_segments (0x827f8 : word) = Some W_827f8.
Proof. vm_refl. Qed.
Lemma D_827f8 : decode_any W_827f8 = Some (Load SZ8 true 15 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_827fc : bv 32 := 0x01078833.
Lemma F_827fc : fetch_word Ubsan.M.loaded_segments (0x827fc : word) = Some W_827fc.
Proof. vm_refl. Qed.
Lemma D_827fc : decode_any W_827fc = Some (Op ALU_ADD 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82800 : bv 32 := 0x04813c03.
Lemma F_82800 : fetch_word Ubsan.M.loaded_segments (0x82800 : word) = Some W_82800.
Proof. vm_refl. Qed.
Lemma D_82800 : decode_any W_82800 = Some (Load SZ8 true 24 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82804 : bv 32 := 0x43fc5393.
Lemma F_82804 : fetch_word Ubsan.M.loaded_segments (0x82804 : word) = Some W_82804.
Proof. vm_refl. Qed.
Lemma D_82804 : decode_any W_82804 = Some (ShiftImm ALU_SRA 7 24 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82808 : bv 32 := 0x00072793.
Lemma F_82808 : fetch_word Ubsan.M.loaded_segments (0x82808 : word) = Some W_82808.
Proof. vm_refl. Qed.
Lemma D_82808 : decode_any W_82808 = Some (OpImm ALU_SLT 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8280c : bv 32 := 0x0183f3b3.
Lemma F_8280c : fetch_word Ubsan.M.loaded_segments (0x8280c : word) = Some W_8280c.
Proof. vm_refl. Qed.
Lemma D_8280c : decode_any W_8280c = Some (Op ALU_AND 7 7 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82810 : bv 32 := 0x41c80e3b.
Lemma F_82810 : fetch_word Ubsan.M.loaded_segments (0x82810 : word) = Some W_82810.
Proof. vm_refl. Qed.
Lemma D_82810 : decode_any W_82810 = Some (Op32 ALU_SUB 28 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82814 : bv 32 := 0x011a8833.
Lemma F_82814 : fetch_word Ubsan.M.loaded_segments (0x82814 : word) = Some W_82814.
Proof. vm_refl. Qed.
Lemma D_82814 : decode_any W_82814 = Some (Op ALU_ADD 16 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82818 : bv 32 := 0x04013c03.
Lemma F_82818 : fetch_word Ubsan.M.loaded_segments (0x82818 : word) = Some W_82818.
Proof. vm_refl. Qed.
Lemma D_82818 : decode_any W_82818 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8281c : bv 32 := 0x418e0e3b.
Lemma F_8281c : fetch_word Ubsan.M.loaded_segments (0x8281c : word) = Some W_8281c.
Proof. vm_refl. Qed.
Lemma D_8281c : decode_any W_8281c = Some (Op32 ALU_SUB 28 28 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82820 : bv 32 := 0x007e03bb.
Lemma F_82820 : fetch_word Ubsan.M.loaded_segments (0x82820 : word) = Some W_82820.
Proof. vm_refl. Qed.
Lemma D_82820 : decode_any W_82820 = Some (Op32 ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82824 : bv 32 := 0x43f3de13.
Lemma F_82824 : fetch_word Ubsan.M.loaded_segments (0x82824 : word) = Some W_82824.
Proof. vm_refl. Qed.
Lemma D_82824 : decode_any W_82824 = Some (ShiftImm ALU_SRA 28 7 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82828 : bv 32 := 0x007e73b3.
Lemma F_82828 : fetch_word Ubsan.M.loaded_segments (0x82828 : word) = Some W_82828.
Proof. vm_refl. Qed.
Lemma D_82828 : decode_any W_82828 = Some (Op ALU_AND 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8282c : bv 32 := 0x407303bb.
Lemma F_8282c : fetch_word Ubsan.M.loaded_segments (0x8282c : word) = Some W_8282c.
Proof. vm_refl. Qed.
Lemma D_8282c : decode_any W_8282c = Some (Op32 ALU_SUB 7 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82830 : bv 32 := 0x0009ae13.
Lemma F_82830 : fetch_word Ubsan.M.loaded_segments (0x82830 : word) = Some W_82830.
Proof. vm_refl. Qed.
Lemma D_82830 : decode_any W_82830 = Some (OpImm ALU_SLT 28 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82834 : bv 32 := 0x000a0993.
Lemma F_82834 : fetch_word Ubsan.M.loaded_segments (0x82834 : word) = Some W_82834.
Proof. vm_refl. Qed.
Lemma D_82834 : decode_any W_82834 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82838 : bv 32 := 0xca0a0ee3.
Lemma F_82838 : fetch_word Ubsan.M.loaded_segments (0x82838 : word) = Some W_82838.
Proof. vm_refl. Qed.
Lemma D_82838 : decode_any W_82838 = Some (Branch BC_EQ 20 0 7356, 4%Z).
Proof. vm_refl. Qed.

Definition W_8283c : bv 32 := 0xca029ce3.
Lemma F_8283c : fetch_word Ubsan.M.loaded_segments (0x8283c : word) = Some W_8283c.
Proof. vm_refl. Qed.
Lemma D_8283c : decode_any W_8283c = Some (Branch BC_NE 5 0 7352, 4%Z).
Proof. vm_refl. Qed.

Definition W_82840 : bv 32 := 0x00ba8c33.
Lemma F_82840 : fetch_word Ubsan.M.loaded_segments (0x82840 : word) = Some W_82840.
Proof. vm_refl. Qed.
Lemma D_82840 : decode_any W_82840 = Some (Op ALU_ADD 24 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82844 : bv 32 := 0xca0c08e3.
Lemma F_82844 : fetch_word Ubsan.M.loaded_segments (0x82844 : word) = Some W_82844.
Proof. vm_refl. Qed.
Lemma D_82844 : decode_any W_82844 = Some (Branch BC_EQ 24 0 7344, 4%Z).
Proof. vm_refl. Qed.

Definition W_82848 : bv 32 := 0x000a2303.
Lemma F_82848 : fetch_word Ubsan.M.loaded_segments (0x82848 : word) = Some W_82848.
Proof. vm_refl. Qed.
Lemma D_82848 : decode_any W_82848 = Some (Load SZ4 true 6 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8284c : bv 32 := 0x000c2c83.
Lemma F_8284c : fetch_word Ubsan.M.loaded_segments (0x8284c : word) = Some W_8284c.
Proof. vm_refl. Qed.
Lemma D_8284c : decode_any W_8284c = Some (Load SZ4 true 25 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82850 : bv 32 := 0x00c37333.
Lemma F_82850 : fetch_word Ubsan.M.loaded_segments (0x82850 : word) = Some W_82850.
Proof. vm_refl. Qed.
Lemma D_82850 : decode_any W_82850 = Some (Op ALU_AND 6 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82854 : bv 32 := 0xfffccc93.
Lemma F_82854 : fetch_word Ubsan.M.loaded_segments (0x82854 : word) = Some W_82854.
Proof. vm_refl. Qed.
Lemma D_82854 : decode_any W_82854 = Some (OpImm ALU_XOR 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82858 : bv 32 := 0x019bfcb3.
Lemma F_82858 : fetch_word Ubsan.M.loaded_segments (0x82858 : word) = Some W_82858.
Proof. vm_refl. Qed.
Lemma D_82858 : decode_any W_82858 = Some (Op ALU_AND 25 23 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_8285c : bv 32 := 0x006ce333.
Lemma F_8285c : fetch_word Ubsan.M.loaded_segments (0x8285c : word) = Some W_8285c.
Proof. vm_refl. Qed.
Lemma D_8285c : decode_any W_8285c = Some (Op ALU_OR 6 25 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82860 : bv 32 := 0x01368cb3.
Lemma F_82860 : fetch_word Ubsan.M.loaded_segments (0x82860 : word) = Some W_82860.
Proof. vm_refl. Qed.
Lemma D_82860 : decode_any W_82860 = Some (Op ALU_ADD 25 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82864 : bv 32 := 0x006a2023.
Lemma F_82864 : fetch_word Ubsan.M.loaded_segments (0x82864 : word) = Some W_82864.
Proof. vm_refl. Qed.
Lemma D_82864 : decode_any W_82864 = Some (Store SZ4 20 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82868 : bv 32 := 0xc80c86e3.
Lemma F_82868 : fetch_word Ubsan.M.loaded_segments (0x82868 : word) = Some W_82868.
Proof. vm_refl. Qed.
Lemma D_82868 : decode_any W_82868 = Some (Branch BC_EQ 25 0 7308, 4%Z).
Proof. vm_refl. Qed.

Definition W_8286c : bv 32 := 0x013cb333.
Lemma F_8286c : fetch_word Ubsan.M.loaded_segments (0x8286c : word) = Some W_8286c.
Proof. vm_refl. Qed.
Lemma D_8286c : decode_any W_8286c = Some (Op ALU_SLTU 6 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82870 : bv 32 := 0x00f34333.
Lemma F_82870 : fetch_word Ubsan.M.loaded_segments (0x82870 : word) = Some W_82870.
Proof. vm_refl. Qed.
Lemma D_82870 : decode_any W_82870 = Some (Op ALU_XOR 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82874 : bv 32 := 0x00134313.
Lemma F_82874 : fetch_word Ubsan.M.loaded_segments (0x82874 : word) = Some W_82874.
Proof. vm_refl. Qed.
Lemma D_82874 : decode_any W_82874 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82878 : bv 32 := 0xc6030ee3.
Lemma F_82878 : fetch_word Ubsan.M.loaded_segments (0x82878 : word) = Some W_82878.
Proof. vm_refl. Qed.
Lemma D_82878 : decode_any W_82878 = Some (Branch BC_EQ 6 0 7292, 4%Z).
Proof. vm_refl. Qed.

Definition W_8287c : bv 32 := 0x00b80333.
Lemma F_8287c : fetch_word Ubsan.M.loaded_segments (0x8287c : word) = Some W_8287c.
Proof. vm_refl. Qed.
Lemma D_8287c : decode_any W_8287c = Some (Op ALU_ADD 6 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82880 : bv 32 := 0xc6030ae3.
Lemma F_82880 : fetch_word Ubsan.M.loaded_segments (0x82880 : word) = Some W_82880.
Proof. vm_refl. Qed.
Lemma D_82880 : decode_any W_82880 = Some (Branch BC_EQ 6 0 7284, 4%Z).
Proof. vm_refl. Qed.

Definition W_82884 : bv 32 := 0x01833333.
Lemma F_82884 : fetch_word Ubsan.M.loaded_segments (0x82884 : word) = Some W_82884.
Proof. vm_refl. Qed.
Lemma D_82884 : decode_any W_82884 = Some (Op ALU_SLTU 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82888 : bv 32 := 0x01c34333.
Lemma F_82888 : fetch_word Ubsan.M.loaded_segments (0x82888 : word) = Some W_82888.
Proof. vm_refl. Qed.
Lemma D_82888 : decode_any W_82888 = Some (Op ALU_XOR 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8288c : bv 32 := 0x00134313.
Lemma F_8288c : fetch_word Ubsan.M.loaded_segments (0x8288c : word) = Some W_8288c.
Proof. vm_refl. Qed.
Lemma D_8288c : decode_any W_8288c = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82890 : bv 32 := 0xc60302e3.
Lemma F_82890 : fetch_word Ubsan.M.loaded_segments (0x82890 : word) = Some W_82890.
Proof. vm_refl. Qed.
Lemma D_82890 : decode_any W_82890 = Some (Branch BC_EQ 6 0 7268, 4%Z).
Proof. vm_refl. Qed.

Definition W_82894 : bv 32 := 0x0013839b.
Lemma F_82894 : fetch_word Ubsan.M.loaded_segments (0x82894 : word) = Some W_82894.
Proof. vm_refl. Qed.
Lemma D_82894 : decode_any W_82894 = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82898 : bv 32 := 0x011585b3.
Lemma F_82898 : fetch_word Ubsan.M.loaded_segments (0x82898 : word) = Some W_82898.
Proof. vm_refl. Qed.
Lemma D_82898 : decode_any W_82898 = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8289c : bv 32 := 0x00da0a33.
Lemma F_8289c : fetch_word Ubsan.M.loaded_segments (0x8289c : word) = Some W_8289c.
Proof. vm_refl. Qed.
Lemma D_8289c : decode_any W_8289c = Some (Op ALU_ADD 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_828a0 : bv 32 := 0x000c8993.
Lemma F_828a0 : fetch_word Ubsan.M.loaded_segments (0x828a0 : word) = Some W_828a0.
Proof. vm_refl. Qed.
Lemma D_828a0 : decode_any W_828a0 = Some (OpImm ALU_ADD 19 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828a4 : bv 32 := 0xf8039ae3.
Lemma F_828a4 : fetch_word Ubsan.M.loaded_segments (0x828a4 : word) = Some W_828a4.
Proof. vm_refl. Qed.
Lemma D_828a4 : decode_any W_828a4 = Some (Branch BC_NE 7 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_828a8 : bv 32 := 0x0e0b1c63.
Lemma F_828a8 : fetch_word Ubsan.M.loaded_segments (0x828a8 : word) = Some W_828a8.
Proof. vm_refl. Qed.
Lemma D_828a8 : decode_any W_828a8 = Some (Branch BC_NE 22 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_828ac : bv 32 := 0x00000593.
Lemma F_828ac : fetch_word Ubsan.M.loaded_segments (0x828ac : word) = Some W_828ac.
Proof. vm_refl. Qed.
Lemma D_828ac : decode_any W_828ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828b0 : bv 32 := 0x00271613.
Lemma F_828b0 : fetch_word Ubsan.M.loaded_segments (0x828b0 : word) = Some W_828b0.
Proof. vm_refl. Qed.
Lemma D_828b0 : decode_any W_828b0 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_828b4 : bv 32 := 0x05813303.
Lemma F_828b4 : fetch_word Ubsan.M.loaded_segments (0x828b4 : word) = Some W_828b4.
Proof. vm_refl. Qed.
Lemma D_828b4 : decode_any W_828b4 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_828b8 : bv 32 := 0x00231693.
Lemma F_828b8 : fetch_word Ubsan.M.loaded_segments (0x828b8 : word) = Some W_828b8.
Proof. vm_refl. Qed.
Lemma D_828b8 : decode_any W_828b8 = Some (ShiftImm ALU_SLL 13 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_828bc : bv 32 := 0x00397793.
Lemma F_828bc : fetch_word Ubsan.M.loaded_segments (0x828bc : word) = Some W_828bc.
Proof. vm_refl. Qed.
Lemma D_828bc : decode_any W_828bc = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_828c0 : bv 32 := 0x00347813.
Lemma F_828c0 : fetch_word Ubsan.M.loaded_segments (0x828c0 : word) = Some W_828c0.
Proof. vm_refl. Qed.
Lemma D_828c0 : decode_any W_828c0 = Some (OpImm ALU_AND 16 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_828c4 : bv 32 := 0x002f9893.
Lemma F_828c4 : fetch_word Ubsan.M.loaded_segments (0x828c4 : word) = Some W_828c4.
Proof. vm_refl. Qed.
Lemma D_828c4 : decode_any W_828c4 = Some (ShiftImm ALU_SLL 17 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_828c8 : bv 32 := 0x00072293.
Lemma F_828c8 : fetch_word Ubsan.M.loaded_segments (0x828c8 : word) = Some W_828c8.
Proof. vm_refl. Qed.
Lemma D_828c8 : decode_any W_828c8 = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828cc : bv 32 := 0x00032393.
Lemma F_828cc : fetch_word Ubsan.M.loaded_segments (0x828cc : word) = Some W_828cc.
Proof. vm_refl. Qed.
Lemma D_828cc : decode_any W_828cc = Some (OpImm ALU_SLT 7 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828d0 : bv 32 := 0x00183993.
Lemma F_828d0 : fetch_word Ubsan.M.loaded_segments (0x828d0 : word) = Some W_828d0.
Proof. vm_refl. Qed.
Lemma D_828d0 : decode_any W_828d0 = Some (OpImm ALU_SLTU 19 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_828d4 : bv 32 := 0x0017ba13.
Lemma F_828d4 : fetch_word Ubsan.M.loaded_segments (0x828d4 : word) = Some W_828d4.
Proof. vm_refl. Qed.
Lemma D_828d4 : decode_any W_828d4 = Some (OpImm ALU_SLTU 20 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_828d8 : bv 32 := 0x00090a93.
Lemma F_828d8 : fetch_word Ubsan.M.loaded_segments (0x828d8 : word) = Some W_828d8.
Proof. vm_refl. Qed.
Lemma D_828d8 : decode_any W_828d8 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828dc : bv 32 := 0x00040b13.
Lemma F_828dc : fetch_word Ubsan.M.loaded_segments (0x828dc : word) = Some W_828dc.
Proof. vm_refl. Qed.
Lemma D_828dc : decode_any W_828dc = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828e0 : bv 32 := 0x060f8263.
Lemma F_828e0 : fetch_word Ubsan.M.loaded_segments (0x828e0 : word) = Some W_828e0.
Proof. vm_refl. Qed.
Lemma D_828e0 : decode_any W_828e0 = Some (Branch BC_EQ 31 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_828e4 : bv 32 := 0x00000793.
Lemma F_828e4 : fetch_word Ubsan.M.loaded_segments (0x828e4 : word) = Some W_828e4.
Proof. vm_refl. Qed.
Lemma D_828e4 : decode_any W_828e4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828e8 : bv 32 := 0x01203833.
Lemma F_828e8 : fetch_word Ubsan.M.loaded_segments (0x828e8 : word) = Some W_828e8.
Proof. vm_refl. Qed.
Lemma D_828e8 : decode_any W_828e8 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_828ec : bv 32 := 0x00803e33.
Lemma F_828ec : fetch_word Ubsan.M.loaded_segments (0x828ec : word) = Some W_828ec.
Proof. vm_refl. Qed.
Lemma D_828ec : decode_any W_828ec = Some (Op ALU_SLTU 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_828f0 : bv 32 := 0x010a7bb3.
Lemma F_828f0 : fetch_word Ubsan.M.loaded_segments (0x828f0 : word) = Some W_828f0.
Proof. vm_refl. Qed.
Lemma D_828f0 : decode_any W_828f0 = Some (Op ALU_AND 23 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_828f4 : bv 32 := 0x01c9fc33.
Lemma F_828f4 : fetch_word Ubsan.M.loaded_segments (0x828f4 : word) = Some W_828f4.
Proof. vm_refl. Qed.
Lemma D_828f4 : decode_any W_828f4 = Some (Op ALU_AND 24 19 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_828f8 : bv 32 := 0x00fa8333.
Lemma F_828f8 : fetch_word Ubsan.M.loaded_segments (0x828f8 : word) = Some W_828f8.
Proof. vm_refl. Qed.
Lemma D_828f8 : decode_any W_828f8 = Some (Op ALU_ADD 6 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_828fc : bv 32 := 0xbf236ce3.
Lemma F_828fc : fetch_word Ubsan.M.loaded_segments (0x828fc : word) = Some W_828fc.
Proof. vm_refl. Qed.
Lemma D_828fc : decode_any W_828fc = Some (Branch BC_LTU 6 18 7160, 4%Z).
Proof. vm_refl. Qed.

Definition W_82900 : bv 32 := 0x00133313.
Lemma F_82900 : fetch_word Ubsan.M.loaded_segments (0x82900 : word) = Some W_82900.
Proof. vm_refl. Qed.
Lemma D_82900 : decode_any W_82900 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82904 : bv 32 := 0x00684333.
Lemma F_82904 : fetch_word Ubsan.M.loaded_segments (0x82904 : word) = Some W_82904.
Proof. vm_refl. Qed.
Lemma D_82904 : decode_any W_82904 = Some (Op ALU_XOR 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82908 : bv 32 := 0xbe0306e3.
Lemma F_82908 : fetch_word Ubsan.M.loaded_segments (0x82908 : word) = Some W_82908.
Proof. vm_refl. Qed.
Lemma D_82908 : decode_any W_82908 = Some (Branch BC_EQ 6 0 7148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8290c : bv 32 := 0xbe0b84e3.
Lemma F_8290c : fetch_word Ubsan.M.loaded_segments (0x8290c : word) = Some W_8290c.
Proof. vm_refl. Qed.
Lemma D_8290c : decode_any W_8290c = Some (Branch BC_EQ 23 0 7144, 4%Z).
Proof. vm_refl. Qed.

Definition W_82910 : bv 32 := 0x00fb0333.
Lemma F_82910 : fetch_word Ubsan.M.loaded_segments (0x82910 : word) = Some W_82910.
Proof. vm_refl. Qed.
Lemma D_82910 : decode_any W_82910 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82914 : bv 32 := 0xbe8360e3.
Lemma F_82914 : fetch_word Ubsan.M.loaded_segments (0x82914 : word) = Some W_82914.
Proof. vm_refl. Qed.
Lemma D_82914 : decode_any W_82914 = Some (Branch BC_LTU 6 8 7136, 4%Z).
Proof. vm_refl. Qed.

Definition W_82918 : bv 32 := 0x00133313.
Lemma F_82918 : fetch_word Ubsan.M.loaded_segments (0x82918 : word) = Some W_82918.
Proof. vm_refl. Qed.
Lemma D_82918 : decode_any W_82918 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8291c : bv 32 := 0x006e4333.
Lemma F_8291c : fetch_word Ubsan.M.loaded_segments (0x8291c : word) = Some W_8291c.
Proof. vm_refl. Qed.
Lemma D_8291c : decode_any W_8291c = Some (Op ALU_XOR 6 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82920 : bv 32 := 0xbc030ae3.
Lemma F_82920 : fetch_word Ubsan.M.loaded_segments (0x82920 : word) = Some W_82920.
Proof. vm_refl. Qed.
Lemma D_82920 : decode_any W_82920 = Some (Branch BC_EQ 6 0 7124, 4%Z).
Proof. vm_refl. Qed.

Definition W_82924 : bv 32 := 0xbc0c08e3.
Lemma F_82924 : fetch_word Ubsan.M.loaded_segments (0x82924 : word) = Some W_82924.
Proof. vm_refl. Qed.
Lemma D_82924 : decode_any W_82924 = Some (Branch BC_EQ 24 0 7120, 4%Z).
Proof. vm_refl. Qed.

Definition W_82928 : bv 32 := 0x00f90333.
Lemma F_82928 : fetch_word Ubsan.M.loaded_segments (0x82928 : word) = Some W_82928.
Proof. vm_refl. Qed.
Lemma D_82928 : decode_any W_82928 = Some (Op ALU_ADD 6 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8292c : bv 32 := 0x00032303.
Lemma F_8292c : fetch_word Ubsan.M.loaded_segments (0x8292c : word) = Some W_8292c.
Proof. vm_refl. Qed.
Lemma D_8292c : decode_any W_8292c = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82930 : bv 32 := 0x00f40cb3.
Lemma F_82930 : fetch_word Ubsan.M.loaded_segments (0x82930 : word) = Some W_82930.
Proof. vm_refl. Qed.
Lemma D_82930 : decode_any W_82930 = Some (Op ALU_ADD 25 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82934 : bv 32 := 0xfff34313.
Lemma F_82934 : fetch_word Ubsan.M.loaded_segments (0x82934 : word) = Some W_82934.
Proof. vm_refl. Qed.
Lemma D_82934 : decode_any W_82934 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82938 : bv 32 := 0x00478793.
Lemma F_82938 : fetch_word Ubsan.M.loaded_segments (0x82938 : word) = Some W_82938.
Proof. vm_refl. Qed.
Lemma D_82938 : decode_any W_82938 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8293c : bv 32 := 0x006ca023.
Lemma F_8293c : fetch_word Ubsan.M.loaded_segments (0x8293c : word) = Some W_8293c.
Proof. vm_refl. Qed.
Lemma D_8293c : decode_any W_8293c = Some (Store SZ4 25 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82940 : bv 32 := 0xfaf89ce3.
Lemma F_82940 : fetch_word Ubsan.M.loaded_segments (0x82940 : word) = Some W_82940.
Proof. vm_refl. Qed.
Lemma D_82940 : decode_any W_82940 = Some (Branch BC_NE 17 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_82944 : bv 32 := 0x00c407b3.
Lemma F_82944 : fetch_word Ubsan.M.loaded_segments (0x82944 : word) = Some W_82944.
Proof. vm_refl. Qed.
Lemma D_82944 : decode_any W_82944 = Some (Op ALU_ADD 15 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82948 : bv 32 := 0x00803833.
Lemma F_82948 : fetch_word Ubsan.M.loaded_segments (0x82948 : word) = Some W_82948.
Proof. vm_refl. Qed.
Lemma D_82948 : decode_any W_82948 = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8294c : bv 32 := 0x0017b313.
Lemma F_8294c : fetch_word Ubsan.M.loaded_segments (0x8294c : word) = Some W_8294c.
Proof. vm_refl. Qed.
Lemma D_8294c : decode_any W_8294c = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82950 : bv 32 := 0xba6802e3.
Lemma F_82950 : fetch_word Ubsan.M.loaded_segments (0x82950 : word) = Some W_82950.
Proof. vm_refl. Qed.
Lemma D_82950 : decode_any W_82950 = Some (Branch BC_EQ 16 6 7076, 4%Z).
Proof. vm_refl. Qed.

Definition W_82954 : bv 32 := 0x0087b7b3.
Lemma F_82954 : fetch_word Ubsan.M.loaded_segments (0x82954 : word) = Some W_82954.
Proof. vm_refl. Qed.
Lemma D_82954 : decode_any W_82954 = Some (Op ALU_SLTU 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82958 : bv 32 := 0x0057c7b3.
Lemma F_82958 : fetch_word Ubsan.M.loaded_segments (0x82958 : word) = Some W_82958.
Proof. vm_refl. Qed.
Lemma D_82958 : decode_any W_82958 = Some (Op ALU_XOR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8295c : bv 32 := 0x0017c793.
Lemma F_8295c : fetch_word Ubsan.M.loaded_segments (0x8295c : word) = Some W_8295c.
Proof. vm_refl. Qed.
Lemma D_8295c : decode_any W_8295c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82960 : bv 32 := 0xb8078ae3.
Lemma F_82960 : fetch_word Ubsan.M.loaded_segments (0x82960 : word) = Some W_82960.
Proof. vm_refl. Qed.
Lemma D_82960 : decode_any W_82960 = Some (Branch BC_EQ 15 0 7060, 4%Z).
Proof. vm_refl. Qed.

Definition W_82964 : bv 32 := 0x012687b3.
Lemma F_82964 : fetch_word Ubsan.M.loaded_segments (0x82964 : word) = Some W_82964.
Proof. vm_refl. Qed.
Lemma D_82964 : decode_any W_82964 = Some (Op ALU_ADD 15 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82968 : bv 32 := 0x01203833.
Lemma F_82968 : fetch_word Ubsan.M.loaded_segments (0x82968 : word) = Some W_82968.
Proof. vm_refl. Qed.
Lemma D_82968 : decode_any W_82968 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8296c : bv 32 := 0x0017b313.
Lemma F_8296c : fetch_word Ubsan.M.loaded_segments (0x8296c : word) = Some W_8296c.
Proof. vm_refl. Qed.
Lemma D_8296c : decode_any W_8296c = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82970 : bv 32 := 0xb86802e3.
Lemma F_82970 : fetch_word Ubsan.M.loaded_segments (0x82970 : word) = Some W_82970.
Proof. vm_refl. Qed.
Lemma D_82970 : decode_any W_82970 = Some (Branch BC_EQ 16 6 7044, 4%Z).
Proof. vm_refl. Qed.

Definition W_82974 : bv 32 := 0x0127b833.
Lemma F_82974 : fetch_word Ubsan.M.loaded_segments (0x82974 : word) = Some W_82974.
Proof. vm_refl. Qed.
Lemma D_82974 : decode_any W_82974 = Some (Op ALU_SLTU 16 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82978 : bv 32 := 0x00784833.
Lemma F_82978 : fetch_word Ubsan.M.loaded_segments (0x82978 : word) = Some W_82978.
Proof. vm_refl. Qed.
Lemma D_82978 : decode_any W_82978 = Some (Op ALU_XOR 16 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8297c : bv 32 := 0x00184813.
Lemma F_8297c : fetch_word Ubsan.M.loaded_segments (0x8297c : word) = Some W_8297c.
Proof. vm_refl. Qed.
Lemma D_8297c : decode_any W_8297c = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82980 : bv 32 := 0xb6080ae3.
Lemma F_82980 : fetch_word Ubsan.M.loaded_segments (0x82980 : word) = Some W_82980.
Proof. vm_refl. Qed.
Lemma D_82980 : decode_any W_82980 = Some (Branch BC_EQ 16 0 7028, 4%Z).
Proof. vm_refl. Qed.

Definition W_82984 : bv 32 := 0x00c40433.
Lemma F_82984 : fetch_word Ubsan.M.loaded_segments (0x82984 : word) = Some W_82984.
Proof. vm_refl. Qed.
Lemma D_82984 : decode_any W_82984 = Some (Op ALU_ADD 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82988 : bv 32 := 0x0015859b.
Lemma F_82988 : fetch_word Ubsan.M.loaded_segments (0x82988 : word) = Some W_82988.
Proof. vm_refl. Qed.
Lemma D_82988 : decode_any W_82988 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8298c : bv 32 := 0x00cb0b33.
Lemma F_8298c : fetch_word Ubsan.M.loaded_segments (0x8298c : word) = Some W_8298c.
Proof. vm_refl. Qed.
Lemma D_8298c : decode_any W_8298c = Some (Op ALU_ADD 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82990 : bv 32 := 0x00da8ab3.
Lemma F_82990 : fetch_word Ubsan.M.loaded_segments (0x82990 : word) = Some W_82990.
Proof. vm_refl. Qed.
Lemma D_82990 : decode_any W_82990 = Some (Op ALU_ADD 21 21 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82994 : bv 32 := 0x00078913.
Lemma F_82994 : fetch_word Ubsan.M.loaded_segments (0x82994 : word) = Some W_82994.
Proof. vm_refl. Qed.
Lemma D_82994 : decode_any W_82994 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82998 : bv 32 := 0x08013783.
Lemma F_82998 : fetch_word Ubsan.M.loaded_segments (0x82998 : word) = Some W_82998.
Proof. vm_refl. Qed.
Lemma D_82998 : decode_any W_82998 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_8299c : bv 32 := 0xf4f592e3.
Lemma F_8299c : fetch_word Ubsan.M.loaded_segments (0x8299c : word) = Some W_8299c.
Proof. vm_refl. Qed.
Lemma D_8299c : decode_any W_8299c = Some (Branch BC_NE 11 15 8004, 4%Z).
Proof. vm_refl. Qed.

Definition W_829a0 : bv 32 := 0x00048463.
Lemma F_829a0 : fetch_word Ubsan.M.loaded_segments (0x829a0 : word) = Some W_829a0.
Proof. vm_refl. Qed.
Lemma D_829a0 : decode_any W_829a0 = Some (Branch BC_EQ 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_829a4 : bv 32 := 0x4150406f.
Lemma F_829a4 : fetch_word Ubsan.M.loaded_segments (0x829a4 : word) = Some W_829a4.
Proof. vm_refl. Qed.
Lemma D_829a4 : decode_any W_829a4 = Some (Jal 0 19476, 4%Z).
Proof. vm_refl. Qed.

Definition W_829a8 : bv 32 := 0x00357593.
Lemma F_829a8 : fetch_word Ubsan.M.loaded_segments (0x829a8 : word) = Some W_829a8.
Proof. vm_refl. Qed.
Lemma D_829a8 : decode_any W_829a8 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_829ac : bv 32 := 0xb40594e3.
Lemma F_829ac : fetch_word Ubsan.M.loaded_segments (0x829ac : word) = Some W_829ac.
Proof. vm_refl. Qed.
Lemma D_829ac : decode_any W_829ac = Some (Branch BC_NE 11 0 6984, 4%Z).
Proof. vm_refl. Qed.

Definition W_829b0 : bv 32 := 0xfffec613.
Lemma F_829b0 : fetch_word Ubsan.M.loaded_segments (0x829b0 : word) = Some W_829b0.
Proof. vm_refl. Qed.
Lemma D_829b0 : decode_any W_829b0 = Some (OpImm ALU_XOR 12 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_829b4 : bv 32 := 0x00271693.
Lemma F_829b4 : fetch_word Ubsan.M.loaded_segments (0x829b4 : word) = Some W_829b4.
Proof. vm_refl. Qed.
Lemma D_829b4 : decode_any W_829b4 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_829b8 : bv 32 := 0x05813e03.
Lemma F_829b8 : fetch_word Ubsan.M.loaded_segments (0x829b8 : word) = Some W_829b8.
Proof. vm_refl. Qed.
Lemma D_829b8 : decode_any W_829b8 = Some (Load SZ8 true 28 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_829bc : bv 32 := 0x002e1793.
Lemma F_829bc : fetch_word Ubsan.M.loaded_segments (0x829bc : word) = Some W_829bc.
Proof. vm_refl. Qed.
Lemma D_829bc : decode_any W_829bc = Some (ShiftImm ALU_SLL 15 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_829c0 : bv 32 := 0x03813883.
Lemma F_829c0 : fetch_word Ubsan.M.loaded_segments (0x829c0 : word) = Some W_829c0.
Proof. vm_refl. Qed.
Lemma D_829c0 : decode_any W_829c0 = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_829c4 : bv 32 := 0x03013803.
Lemma F_829c4 : fetch_word Ubsan.M.loaded_segments (0x829c4 : word) = Some W_829c4.
Proof. vm_refl. Qed.
Lemma D_829c4 : decode_any W_829c4 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_829c8 : bv 32 := 0x011808b3.
Lemma F_829c8 : fetch_word Ubsan.M.loaded_segments (0x829c8 : word) = Some W_829c8.
Proof. vm_refl. Qed.
Lemma D_829c8 : decode_any W_829c8 = Some (Op ALU_ADD 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_829cc : bv 32 := 0x04813283.
Lemma F_829cc : fetch_word Ubsan.M.loaded_segments (0x829cc : word) = Some W_829cc.
Proof. vm_refl. Qed.
Lemma D_829cc : decode_any W_829cc = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_829d0 : bv 32 := 0x43f2d813.
Lemma F_829d0 : fetch_word Ubsan.M.loaded_segments (0x829d0 : word) = Some W_829d0.
Proof. vm_refl. Qed.
Lemma D_829d0 : decode_any W_829d0 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_829d4 : bv 32 := 0x005872b3.
Lemma F_829d4 : fetch_word Ubsan.M.loaded_segments (0x829d4 : word) = Some W_829d4.
Proof. vm_refl. Qed.
Lemma D_829d4 : decode_any W_829d4 = Some (Op ALU_AND 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_829d8 : bv 32 := 0x003f7813.
Lemma F_829d8 : fetch_word Ubsan.M.loaded_segments (0x829d8 : word) = Some W_829d8.
Proof. vm_refl. Qed.
Lemma D_829d8 : decode_any W_829d8 = Some (OpImm ALU_AND 16 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_829dc : bv 32 := 0x05013383.
Lemma F_829dc : fetch_word Ubsan.M.loaded_segments (0x829dc : word) = Some W_829dc.
Proof. vm_refl. Qed.
Lemma D_829dc : decode_any W_829dc = Some (Load SZ8 true 7 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_829e0 : bv 32 := 0x02813303.
Lemma F_829e0 : fetch_word Ubsan.M.loaded_segments (0x829e0 : word) = Some W_829e0.
Proof. vm_refl. Qed.
Lemma D_829e0 : decode_any W_829e0 = Some (Load SZ8 true 6 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_829e4 : bv 32 := 0x4073033b.
Lemma F_829e4 : fetch_word Ubsan.M.loaded_segments (0x829e4 : word) = Some W_829e4.
Proof. vm_refl. Qed.
Lemma D_829e4 : decode_any W_829e4 = Some (Op32 ALU_SUB 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_829e8 : bv 32 := 0x00072713.
Lemma F_829e8 : fetch_word Ubsan.M.loaded_segments (0x829e8 : word) = Some W_829e8.
Proof. vm_refl. Qed.
Lemma D_829e8 : decode_any W_829e8 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_829ec : bv 32 := 0x005882b3.
Lemma F_829ec : fetch_word Ubsan.M.loaded_segments (0x829ec : word) = Some W_829ec.
Proof. vm_refl. Qed.
Lemma D_829ec : decode_any W_829ec = Some (Op ALU_ADD 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_829f0 : bv 32 := 0x00ff08b3.
Lemma F_829f0 : fetch_word Ubsan.M.loaded_segments (0x829f0 : word) = Some W_829f0.
Proof. vm_refl. Qed.
Lemma D_829f0 : decode_any W_829f0 = Some (Op ALU_ADD 17 30 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_829f4 : bv 32 := 0x407282bb.
Lemma F_829f4 : fetch_word Ubsan.M.loaded_segments (0x829f4 : word) = Some W_829f4.
Proof. vm_refl. Qed.
Lemma D_829f4 : decode_any W_829f4 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_829f8 : bv 32 := 0x04013383.
Lemma F_829f8 : fetch_word Ubsan.M.loaded_segments (0x829f8 : word) = Some W_829f8.
Proof. vm_refl. Qed.
Lemma D_829f8 : decode_any W_829f8 = Some (Load SZ8 true 7 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_829fc : bv 32 := 0x407282bb.
Lemma F_829fc : fetch_word Ubsan.M.loaded_segments (0x829fc : word) = Some W_829fc.
Proof. vm_refl. Qed.
Lemma D_829fc : decode_any W_829fc = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a00 : bv 32 := 0x43f2d393.
Lemma F_82a00 : fetch_word Ubsan.M.loaded_segments (0x82a00 : word) = Some W_82a00.
Proof. vm_refl. Qed.
Lemma D_82a00 : decode_any W_82a00 = Some (ShiftImm ALU_SRA 7 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a04 : bv 32 := 0x0053f2b3.
Lemma F_82a04 : fetch_word Ubsan.M.loaded_segments (0x82a04 : word) = Some W_82a04.
Proof. vm_refl. Qed.
Lemma D_82a04 : decode_any W_82a04 = Some (Op ALU_AND 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a08 : bv 32 := 0x405302bb.
Lemma F_82a08 : fetch_word Ubsan.M.loaded_segments (0x82a08 : word) = Some W_82a08.
Proof. vm_refl. Qed.
Lemma D_82a08 : decode_any W_82a08 = Some (Op32 ALU_SUB 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a0c : bv 32 := 0x000e2313.
Lemma F_82a0c : fetch_word Ubsan.M.loaded_segments (0x82a0c : word) = Some W_82a0c.
Proof. vm_refl. Qed.
Lemma D_82a0c : decode_any W_82a0c = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a10 : bv 32 := 0x00050393.
Lemma F_82a10 : fetch_word Ubsan.M.loaded_segments (0x82a10 : word) = Some W_82a10.
Proof. vm_refl. Qed.
Lemma D_82a10 : decode_any W_82a10 = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a14 : bv 32 := 0xae0500e3.
Lemma F_82a14 : fetch_word Ubsan.M.loaded_segments (0x82a14 : word) = Some W_82a14.
Proof. vm_refl. Qed.
Lemma D_82a14 : decode_any W_82a14 = Some (Branch BC_EQ 10 0 6880, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a18 : bv 32 := 0xac081ee3.
Lemma F_82a18 : fetch_word Ubsan.M.loaded_segments (0x82a18 : word) = Some W_82a18.
Proof. vm_refl. Qed.
Lemma D_82a18 : decode_any W_82a18 = Some (Branch BC_NE 16 0 6876, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a1c : bv 32 := 0x00bf0e33.
Lemma F_82a1c : fetch_word Ubsan.M.loaded_segments (0x82a1c : word) = Some W_82a1c.
Proof. vm_refl. Qed.
Lemma D_82a1c : decode_any W_82a1c = Some (Op ALU_ADD 28 30 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a20 : bv 32 := 0xac0e0ae3.
Lemma F_82a20 : fetch_word Ubsan.M.loaded_segments (0x82a20 : word) = Some W_82a20.
Proof. vm_refl. Qed.
Lemma D_82a20 : decode_any W_82a20 = Some (Branch BC_EQ 28 0 6868, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a24 : bv 32 := 0x00052f83.
Lemma F_82a24 : fetch_word Ubsan.M.loaded_segments (0x82a24 : word) = Some W_82a24.
Proof. vm_refl. Qed.
Lemma D_82a24 : decode_any W_82a24 = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a28 : bv 32 := 0x000e2403.
Lemma F_82a28 : fetch_word Ubsan.M.loaded_segments (0x82a28 : word) = Some W_82a28.
Proof. vm_refl. Qed.
Lemma D_82a28 : decode_any W_82a28 = Some (Load SZ4 true 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a2c : bv 32 := 0x00cfffb3.
Lemma F_82a2c : fetch_word Ubsan.M.loaded_segments (0x82a2c : word) = Some W_82a2c.
Proof. vm_refl. Qed.
Lemma D_82a2c : decode_any W_82a2c = Some (Op ALU_AND 31 31 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a30 : bv 32 := 0xfff44413.
Lemma F_82a30 : fetch_word Ubsan.M.loaded_segments (0x82a30 : word) = Some W_82a30.
Proof. vm_refl. Qed.
Lemma D_82a30 : decode_any W_82a30 = Some (OpImm ALU_XOR 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a34 : bv 32 := 0x008ef433.
Lemma F_82a34 : fetch_word Ubsan.M.loaded_segments (0x82a34 : word) = Some W_82a34.
Proof. vm_refl. Qed.
Lemma D_82a34 : decode_any W_82a34 = Some (Op ALU_AND 8 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a38 : bv 32 := 0x01f46433.
Lemma F_82a38 : fetch_word Ubsan.M.loaded_segments (0x82a38 : word) = Some W_82a38.
Proof. vm_refl. Qed.
Lemma D_82a38 : decode_any W_82a38 = Some (Op ALU_OR 8 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a3c : bv 32 := 0x00768fb3.
Lemma F_82a3c : fetch_word Ubsan.M.loaded_segments (0x82a3c : word) = Some W_82a3c.
Proof. vm_refl. Qed.
Lemma D_82a3c : decode_any W_82a3c = Some (Op ALU_ADD 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a40 : bv 32 := 0x00852023.
Lemma F_82a40 : fetch_word Ubsan.M.loaded_segments (0x82a40 : word) = Some W_82a40.
Proof. vm_refl. Qed.
Lemma D_82a40 : decode_any W_82a40 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a44 : bv 32 := 0xaa0f88e3.
Lemma F_82a44 : fetch_word Ubsan.M.loaded_segments (0x82a44 : word) = Some W_82a44.
Proof. vm_refl. Qed.
Lemma D_82a44 : decode_any W_82a44 = Some (Branch BC_EQ 31 0 6832, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a48 : bv 32 := 0x007fb3b3.
Lemma F_82a48 : fetch_word Ubsan.M.loaded_segments (0x82a48 : word) = Some W_82a48.
Proof. vm_refl. Qed.
Lemma D_82a48 : decode_any W_82a48 = Some (Op ALU_SLTU 7 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a4c : bv 32 := 0x00e3c3b3.
Lemma F_82a4c : fetch_word Ubsan.M.loaded_segments (0x82a4c : word) = Some W_82a4c.
Proof. vm_refl. Qed.
Lemma D_82a4c : decode_any W_82a4c = Some (Op ALU_XOR 7 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a50 : bv 32 := 0x0013c393.
Lemma F_82a50 : fetch_word Ubsan.M.loaded_segments (0x82a50 : word) = Some W_82a50.
Proof. vm_refl. Qed.
Lemma D_82a50 : decode_any W_82a50 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a54 : bv 32 := 0xaa0380e3.
Lemma F_82a54 : fetch_word Ubsan.M.loaded_segments (0x82a54 : word) = Some W_82a54.
Proof. vm_refl. Qed.
Lemma D_82a54 : decode_any W_82a54 = Some (Branch BC_EQ 7 0 6816, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a58 : bv 32 := 0x00b883b3.
Lemma F_82a58 : fetch_word Ubsan.M.loaded_segments (0x82a58 : word) = Some W_82a58.
Proof. vm_refl. Qed.
Lemma D_82a58 : decode_any W_82a58 = Some (Op ALU_ADD 7 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a5c : bv 32 := 0xa8038ce3.
Lemma F_82a5c : fetch_word Ubsan.M.loaded_segments (0x82a5c : word) = Some W_82a5c.
Proof. vm_refl. Qed.
Lemma D_82a5c : decode_any W_82a5c = Some (Branch BC_EQ 7 0 6808, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a60 : bv 32 := 0x01c3b3b3.
Lemma F_82a60 : fetch_word Ubsan.M.loaded_segments (0x82a60 : word) = Some W_82a60.
Proof. vm_refl. Qed.
Lemma D_82a60 : decode_any W_82a60 = Some (Op ALU_SLTU 7 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a64 : bv 32 := 0x0063c3b3.
Lemma F_82a64 : fetch_word Ubsan.M.loaded_segments (0x82a64 : word) = Some W_82a64.
Proof. vm_refl. Qed.
Lemma D_82a64 : decode_any W_82a64 = Some (Op ALU_XOR 7 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a68 : bv 32 := 0x0013c393.
Lemma F_82a68 : fetch_word Ubsan.M.loaded_segments (0x82a68 : word) = Some W_82a68.
Proof. vm_refl. Qed.
Lemma D_82a68 : decode_any W_82a68 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a6c : bv 32 := 0xa80384e3.
Lemma F_82a6c : fetch_word Ubsan.M.loaded_segments (0x82a6c : word) = Some W_82a6c.
Proof. vm_refl. Qed.
Lemma D_82a6c : decode_any W_82a6c = Some (Branch BC_EQ 7 0 6792, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a70 : bv 32 := 0x0012829b.
Lemma F_82a70 : fetch_word Ubsan.M.loaded_segments (0x82a70 : word) = Some W_82a70.
Proof. vm_refl. Qed.
Lemma D_82a70 : decode_any W_82a70 = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a74 : bv 32 := 0x00f585b3.
Lemma F_82a74 : fetch_word Ubsan.M.loaded_segments (0x82a74 : word) = Some W_82a74.
Proof. vm_refl. Qed.
Lemma D_82a74 : decode_any W_82a74 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a78 : bv 32 := 0x00d50533.
Lemma F_82a78 : fetch_word Ubsan.M.loaded_segments (0x82a78 : word) = Some W_82a78.
Proof. vm_refl. Qed.
Lemma D_82a78 : decode_any W_82a78 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a7c : bv 32 := 0x000f8393.
Lemma F_82a7c : fetch_word Ubsan.M.loaded_segments (0x82a7c : word) = Some W_82a7c.
Proof. vm_refl. Qed.
Lemma D_82a7c : decode_any W_82a7c = Some (OpImm ALU_ADD 7 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a80 : bv 32 := 0xf8029ae3.
Lemma F_82a80 : fetch_word Ubsan.M.loaded_segments (0x82a80 : word) = Some W_82a80.
Proof. vm_refl. Qed.
Lemma D_82a80 : decode_any W_82a80 = Some (Branch BC_NE 5 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a84 : bv 32 := 0x3350406f.
Lemma F_82a84 : fetch_word Ubsan.M.loaded_segments (0x82a84 : word) = Some W_82a84.
Proof. vm_refl. Qed.
Lemma D_82a84 : decode_any W_82a84 = Some (Jal 0 19252, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a88 : bv 32 := 0x0e008263.
Lemma F_82a88 : fetch_word Ubsan.M.loaded_segments (0x82a88 : word) = Some W_82a88.
Proof. vm_refl. Qed.
Lemma D_82a88 : decode_any W_82a88 = Some (Branch BC_EQ 1 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a8c : bv 32 := 0x003a7593.
Lemma F_82a8c : fetch_word Ubsan.M.loaded_segments (0x82a8c : word) = Some W_82a8c.
Proof. vm_refl. Qed.
Lemma D_82a8c : decode_any W_82a8c = Some (OpImm ALU_AND 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a90 : bv 32 := 0xa60592e3.
Lemma F_82a90 : fetch_word Ubsan.M.loaded_segments (0x82a90 : word) = Some W_82a90.
Proof. vm_refl. Qed.
Lemma D_82a90 : decode_any W_82a90 = Some (Branch BC_NE 11 0 6756, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a94 : bv 32 := 0xfffbc613.
Lemma F_82a94 : fetch_word Ubsan.M.loaded_segments (0x82a94 : word) = Some W_82a94.
Proof. vm_refl. Qed.
Lemma D_82a94 : decode_any W_82a94 = Some (OpImm ALU_XOR 12 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a98 : bv 32 := 0x00271693.
Lemma F_82a98 : fetch_word Ubsan.M.loaded_segments (0x82a98 : word) = Some W_82a98.
Proof. vm_refl. Qed.
Lemma D_82a98 : decode_any W_82a98 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a9c : bv 32 := 0x05813983.
Lemma F_82a9c : fetch_word Ubsan.M.loaded_segments (0x82a9c : word) = Some W_82a9c.
Proof. vm_refl. Qed.
Lemma D_82a9c : decode_any W_82a9c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa0 : bv 32 := 0x00299893.
Lemma F_82aa0 : fetch_word Ubsan.M.loaded_segments (0x82aa0 : word) = Some W_82aa0.
Proof. vm_refl. Qed.
Lemma D_82aa0 : decode_any W_82aa0 = Some (ShiftImm ALU_SLL 17 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa4 : bv 32 := 0x003af293.
Lemma F_82aa4 : fetch_word Ubsan.M.loaded_segments (0x82aa4 : word) = Some W_82aa4.
Proof. vm_refl. Qed.
Lemma D_82aa4 : decode_any W_82aa4 = Some (OpImm ALU_AND 5 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa8 : bv 32 := 0x05013e03.
Lemma F_82aa8 : fetch_word Ubsan.M.loaded_segments (0x82aa8 : word) = Some W_82aa8.
Proof. vm_refl. Qed.
Lemma D_82aa8 : decode_any W_82aa8 = Some (Load SZ8 true 28 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aac : bv 32 := 0x02813783.
Lemma F_82aac : fetch_word Ubsan.M.loaded_segments (0x82aac : word) = Some W_82aac.
Proof. vm_refl. Qed.
Lemma D_82aac : decode_any W_82aac = Some (Load SZ8 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab0 : bv 32 := 0x41c7833b.
Lemma F_82ab0 : fetch_word Ubsan.M.loaded_segments (0x82ab0 : word) = Some W_82ab0.
Proof. vm_refl. Qed.
Lemma D_82ab0 : decode_any W_82ab0 = Some (Op32 ALU_SUB 6 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab4 : bv 32 := 0x03813803.
Lemma F_82ab4 : fetch_word Ubsan.M.loaded_segments (0x82ab4 : word) = Some W_82ab4.
Proof. vm_refl. Qed.
Lemma D_82ab4 : decode_any W_82ab4 = Some (Load SZ8 true 16 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab8 : bv 32 := 0x03013783.
Lemma F_82ab8 : fetch_word Ubsan.M.loaded_segments (0x82ab8 : word) = Some W_82ab8.
Proof. vm_refl. Qed.
Lemma D_82ab8 : decode_any W_82ab8 = Some (Load SZ8 true 15 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82abc : bv 32 := 0x01078833.
Lemma F_82abc : fetch_word Ubsan.M.loaded_segments (0x82abc : word) = Some W_82abc.
Proof. vm_refl. Qed.
Lemma D_82abc : decode_any W_82abc = Some (Op ALU_ADD 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac0 : bv 32 := 0x04813c03.
Lemma F_82ac0 : fetch_word Ubsan.M.loaded_segments (0x82ac0 : word) = Some W_82ac0.
Proof. vm_refl. Qed.
Lemma D_82ac0 : decode_any W_82ac0 = Some (Load SZ8 true 24 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac4 : bv 32 := 0x43fc5393.
Lemma F_82ac4 : fetch_word Ubsan.M.loaded_segments (0x82ac4 : word) = Some W_82ac4.
Proof. vm_refl. Qed.
Lemma D_82ac4 : decode_any W_82ac4 = Some (ShiftImm ALU_SRA 7 24 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac8 : bv 32 := 0x00072793.
Lemma F_82ac8 : fetch_word Ubsan.M.loaded_segments (0x82ac8 : word) = Some W_82ac8.
Proof. vm_refl. Qed.
Lemma D_82ac8 : decode_any W_82ac8 = Some (OpImm ALU_SLT 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82acc : bv 32 := 0x0183f3b3.
Lemma F_82acc : fetch_word Ubsan.M.loaded_segments (0x82acc : word) = Some W_82acc.
Proof. vm_refl. Qed.
Lemma D_82acc : decode_any W_82acc = Some (Op ALU_AND 7 7 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad0 : bv 32 := 0x41c80e3b.
Lemma F_82ad0 : fetch_word Ubsan.M.loaded_segments (0x82ad0 : word) = Some W_82ad0.
Proof. vm_refl. Qed.
Lemma D_82ad0 : decode_any W_82ad0 = Some (Op32 ALU_SUB 28 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad4 : bv 32 := 0x011a8833.
Lemma F_82ad4 : fetch_word Ubsan.M.loaded_segments (0x82ad4 : word) = Some W_82ad4.
Proof. vm_refl. Qed.
Lemma D_82ad4 : decode_any W_82ad4 = Some (Op ALU_ADD 16 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad8 : bv 32 := 0x04013c03.
Lemma F_82ad8 : fetch_word Ubsan.M.loaded_segments (0x82ad8 : word) = Some W_82ad8.
Proof. vm_refl. Qed.
Lemma D_82ad8 : decode_any W_82ad8 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82adc : bv 32 := 0x418e0e3b.
Lemma F_82adc : fetch_word Ubsan.M.loaded_segments (0x82adc : word) = Some W_82adc.
Proof. vm_refl. Qed.
Lemma D_82adc : decode_any W_82adc = Some (Op32 ALU_SUB 28 28 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae0 : bv 32 := 0x007e03bb.
Lemma F_82ae0 : fetch_word Ubsan.M.loaded_segments (0x82ae0 : word) = Some W_82ae0.
Proof. vm_refl. Qed.
Lemma D_82ae0 : decode_any W_82ae0 = Some (Op32 ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae4 : bv 32 := 0x43f3de13.
Lemma F_82ae4 : fetch_word Ubsan.M.loaded_segments (0x82ae4 : word) = Some W_82ae4.
Proof. vm_refl. Qed.
Lemma D_82ae4 : decode_any W_82ae4 = Some (ShiftImm ALU_SRA 28 7 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae8 : bv 32 := 0x007e73b3.
Lemma F_82ae8 : fetch_word Ubsan.M.loaded_segments (0x82ae8 : word) = Some W_82ae8.
Proof. vm_refl. Qed.
Lemma D_82ae8 : decode_any W_82ae8 = Some (Op ALU_AND 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aec : bv 32 := 0x407303bb.
Lemma F_82aec : fetch_word Ubsan.M.loaded_segments (0x82aec : word) = Some W_82aec.
Proof. vm_refl. Qed.
Lemma D_82aec : decode_any W_82aec = Some (Op32 ALU_SUB 7 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af0 : bv 32 := 0x0009ae13.
Lemma F_82af0 : fetch_word Ubsan.M.loaded_segments (0x82af0 : word) = Some W_82af0.
Proof. vm_refl. Qed.
Lemma D_82af0 : decode_any W_82af0 = Some (OpImm ALU_SLT 28 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af4 : bv 32 := 0x000a0993.
Lemma F_82af4 : fetch_word Ubsan.M.loaded_segments (0x82af4 : word) = Some W_82af4.
Proof. vm_refl. Qed.
Lemma D_82af4 : decode_any W_82af4 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af8 : bv 32 := 0x9e0a0ee3.
Lemma F_82af8 : fetch_word Ubsan.M.loaded_segments (0x82af8 : word) = Some W_82af8.
Proof. vm_refl. Qed.
Lemma D_82af8 : decode_any W_82af8 = Some (Branch BC_EQ 20 0 6652, 4%Z).
Proof. vm_refl. Qed.

Definition W_82afc : bv 32 := 0x9e029ce3.
Lemma F_82afc : fetch_word Ubsan.M.loaded_segments (0x82afc : word) = Some W_82afc.
Proof. vm_refl. Qed.
Lemma D_82afc : decode_any W_82afc = Some (Branch BC_NE 5 0 6648, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b00 : bv 32 := 0x00ba8c33.
Lemma F_82b00 : fetch_word Ubsan.M.loaded_segments (0x82b00 : word) = Some W_82b00.
Proof. vm_refl. Qed.
Lemma D_82b00 : decode_any W_82b00 = Some (Op ALU_ADD 24 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b04 : bv 32 := 0x9e0c08e3.
Lemma F_82b04 : fetch_word Ubsan.M.loaded_segments (0x82b04 : word) = Some W_82b04.
Proof. vm_refl. Qed.
Lemma D_82b04 : decode_any W_82b04 = Some (Branch BC_EQ 24 0 6640, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b08 : bv 32 := 0x000a2303.
Lemma F_82b08 : fetch_word Ubsan.M.loaded_segments (0x82b08 : word) = Some W_82b08.
Proof. vm_refl. Qed.
Lemma D_82b08 : decode_any W_82b08 = Some (Load SZ4 true 6 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b0c : bv 32 := 0x000c2c83.
Lemma F_82b0c : fetch_word Ubsan.M.loaded_segments (0x82b0c : word) = Some W_82b0c.
Proof. vm_refl. Qed.
Lemma D_82b0c : decode_any W_82b0c = Some (Load SZ4 true 25 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b10 : bv 32 := 0x00c37d33.
Lemma F_82b10 : fetch_word Ubsan.M.loaded_segments (0x82b10 : word) = Some W_82b10.
Proof. vm_refl. Qed.
Lemma D_82b10 : decode_any W_82b10 = Some (Op ALU_AND 26 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b14 : bv 32 := 0x006cf333.
Lemma F_82b14 : fetch_word Ubsan.M.loaded_segments (0x82b14 : word) = Some W_82b14.
Proof. vm_refl. Qed.
Lemma D_82b14 : decode_any W_82b14 = Some (Op ALU_AND 6 25 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b18 : bv 32 := 0xfff34313.
Lemma F_82b18 : fetch_word Ubsan.M.loaded_segments (0x82b18 : word) = Some W_82b18.
Proof. vm_refl. Qed.
Lemma D_82b18 : decode_any W_82b18 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b1c : bv 32 := 0x006bf333.
Lemma F_82b1c : fetch_word Ubsan.M.loaded_segments (0x82b1c : word) = Some W_82b1c.
Proof. vm_refl. Qed.
Lemma D_82b1c : decode_any W_82b1c = Some (Op ALU_AND 6 23 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b20 : bv 32 := 0x01a36333.
Lemma F_82b20 : fetch_word Ubsan.M.loaded_segments (0x82b20 : word) = Some W_82b20.
Proof. vm_refl. Qed.
Lemma D_82b20 : decode_any W_82b20 = Some (Op ALU_OR 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b24 : bv 32 := 0x01368cb3.
Lemma F_82b24 : fetch_word Ubsan.M.loaded_segments (0x82b24 : word) = Some W_82b24.
Proof. vm_refl. Qed.
Lemma D_82b24 : decode_any W_82b24 = Some (Op ALU_ADD 25 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b28 : bv 32 := 0x006a2023.
Lemma F_82b28 : fetch_word Ubsan.M.loaded_segments (0x82b28 : word) = Some W_82b28.
Proof. vm_refl. Qed.
Lemma D_82b28 : decode_any W_82b28 = Some (Store SZ4 20 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b2c : bv 32 := 0x9c0c84e3.
Lemma F_82b2c : fetch_word Ubsan.M.loaded_segments (0x82b2c : word) = Some W_82b2c.
Proof. vm_refl. Qed.
Lemma D_82b2c : decode_any W_82b2c = Some (Branch BC_EQ 25 0 6600, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b30 : bv 32 := 0x013cb333.
Lemma F_82b30 : fetch_word Ubsan.M.loaded_segments (0x82b30 : word) = Some W_82b30.
Proof. vm_refl. Qed.
Lemma D_82b30 : decode_any W_82b30 = Some (Op ALU_SLTU 6 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b34 : bv 32 := 0x00f34333.
Lemma F_82b34 : fetch_word Ubsan.M.loaded_segments (0x82b34 : word) = Some W_82b34.
Proof. vm_refl. Qed.
Lemma D_82b34 : decode_any W_82b34 = Some (Op ALU_XOR 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b38 : bv 32 := 0x00134313.
Lemma F_82b38 : fetch_word Ubsan.M.loaded_segments (0x82b38 : word) = Some W_82b38.
Proof. vm_refl. Qed.
Lemma D_82b38 : decode_any W_82b38 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b3c : bv 32 := 0x9a030ce3.
Lemma F_82b3c : fetch_word Ubsan.M.loaded_segments (0x82b3c : word) = Some W_82b3c.
Proof. vm_refl. Qed.
Lemma D_82b3c : decode_any W_82b3c = Some (Branch BC_EQ 6 0 6584, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b40 : bv 32 := 0x00b80333.
Lemma F_82b40 : fetch_word Ubsan.M.loaded_segments (0x82b40 : word) = Some W_82b40.
Proof. vm_refl. Qed.
Lemma D_82b40 : decode_any W_82b40 = Some (Op ALU_ADD 6 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b44 : bv 32 := 0x9a0308e3.
Lemma F_82b44 : fetch_word Ubsan.M.loaded_segments (0x82b44 : word) = Some W_82b44.
Proof. vm_refl. Qed.
Lemma D_82b44 : decode_any W_82b44 = Some (Branch BC_EQ 6 0 6576, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b48 : bv 32 := 0x01833333.
Lemma F_82b48 : fetch_word Ubsan.M.loaded_segments (0x82b48 : word) = Some W_82b48.
Proof. vm_refl. Qed.
Lemma D_82b48 : decode_any W_82b48 = Some (Op ALU_SLTU 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b4c : bv 32 := 0x01c34333.
Lemma F_82b4c : fetch_word Ubsan.M.loaded_segments (0x82b4c : word) = Some W_82b4c.
Proof. vm_refl. Qed.
Lemma D_82b4c : decode_any W_82b4c = Some (Op ALU_XOR 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b50 : bv 32 := 0x00134313.
Lemma F_82b50 : fetch_word Ubsan.M.loaded_segments (0x82b50 : word) = Some W_82b50.
Proof. vm_refl. Qed.
Lemma D_82b50 : decode_any W_82b50 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b54 : bv 32 := 0x9a0300e3.
Lemma F_82b54 : fetch_word Ubsan.M.loaded_segments (0x82b54 : word) = Some W_82b54.
Proof. vm_refl. Qed.
Lemma D_82b54 : decode_any W_82b54 = Some (Branch BC_EQ 6 0 6560, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b58 : bv 32 := 0x0013839b.
Lemma F_82b58 : fetch_word Ubsan.M.loaded_segments (0x82b58 : word) = Some W_82b58.
Proof. vm_refl. Qed.
Lemma D_82b58 : decode_any W_82b58 = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b5c : bv 32 := 0x011585b3.
Lemma F_82b5c : fetch_word Ubsan.M.loaded_segments (0x82b5c : word) = Some W_82b5c.
Proof. vm_refl. Qed.
Lemma D_82b5c : decode_any W_82b5c = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b60 : bv 32 := 0x00da0a33.
Lemma F_82b60 : fetch_word Ubsan.M.loaded_segments (0x82b60 : word) = Some W_82b60.
Proof. vm_refl. Qed.
Lemma D_82b60 : decode_any W_82b60 = Some (Op ALU_ADD 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b64 : bv 32 := 0x000c8993.
Lemma F_82b64 : fetch_word Ubsan.M.loaded_segments (0x82b64 : word) = Some W_82b64.
Proof. vm_refl. Qed.
Lemma D_82b64 : decode_any W_82b64 = Some (OpImm ALU_ADD 19 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b68 : bv 32 := 0xf80398e3.
Lemma F_82b68 : fetch_word Ubsan.M.loaded_segments (0x82b68 : word) = Some W_82b68.
Proof. vm_refl. Qed.
Lemma D_82b68 : decode_any W_82b68 = Some (Branch BC_NE 7 0 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b6c : bv 32 := 0x100b1063.
Lemma F_82b6c : fetch_word Ubsan.M.loaded_segments (0x82b6c : word) = Some W_82b6c.
Proof. vm_refl. Qed.
Lemma D_82b6c : decode_any W_82b6c = Some (Branch BC_NE 22 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b70 : bv 32 := 0x00000593.
Lemma F_82b70 : fetch_word Ubsan.M.loaded_segments (0x82b70 : word) = Some W_82b70.
Proof. vm_refl. Qed.
Lemma D_82b70 : decode_any W_82b70 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b74 : bv 32 := 0x00271613.
Lemma F_82b74 : fetch_word Ubsan.M.loaded_segments (0x82b74 : word) = Some W_82b74.
Proof. vm_refl. Qed.
Lemma D_82b74 : decode_any W_82b74 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b78 : bv 32 := 0x05813303.
Lemma F_82b78 : fetch_word Ubsan.M.loaded_segments (0x82b78 : word) = Some W_82b78.
Proof. vm_refl. Qed.
Lemma D_82b78 : decode_any W_82b78 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b7c : bv 32 := 0x00231693.
Lemma F_82b7c : fetch_word Ubsan.M.loaded_segments (0x82b7c : word) = Some W_82b7c.
Proof. vm_refl. Qed.
Lemma D_82b7c : decode_any W_82b7c = Some (ShiftImm ALU_SLL 13 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b80 : bv 32 := 0x00397793.
Lemma F_82b80 : fetch_word Ubsan.M.loaded_segments (0x82b80 : word) = Some W_82b80.
Proof. vm_refl. Qed.
Lemma D_82b80 : decode_any W_82b80 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b84 : bv 32 := 0x00347813.
Lemma F_82b84 : fetch_word Ubsan.M.loaded_segments (0x82b84 : word) = Some W_82b84.
Proof. vm_refl. Qed.
Lemma D_82b84 : decode_any W_82b84 = Some (OpImm ALU_AND 16 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b88 : bv 32 := 0x002f9893.
Lemma F_82b88 : fetch_word Ubsan.M.loaded_segments (0x82b88 : word) = Some W_82b88.
Proof. vm_refl. Qed.
Lemma D_82b88 : decode_any W_82b88 = Some (ShiftImm ALU_SLL 17 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b8c : bv 32 := 0x00072293.
Lemma F_82b8c : fetch_word Ubsan.M.loaded_segments (0x82b8c : word) = Some W_82b8c.
Proof. vm_refl. Qed.
Lemma D_82b8c : decode_any W_82b8c = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b90 : bv 32 := 0x00032393.
Lemma F_82b90 : fetch_word Ubsan.M.loaded_segments (0x82b90 : word) = Some W_82b90.
Proof. vm_refl. Qed.
Lemma D_82b90 : decode_any W_82b90 = Some (OpImm ALU_SLT 7 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b94 : bv 32 := 0x00183993.
Lemma F_82b94 : fetch_word Ubsan.M.loaded_segments (0x82b94 : word) = Some W_82b94.
Proof. vm_refl. Qed.
Lemma D_82b94 : decode_any W_82b94 = Some (OpImm ALU_SLTU 19 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b98 : bv 32 := 0x0017ba13.
Lemma F_82b98 : fetch_word Ubsan.M.loaded_segments (0x82b98 : word) = Some W_82b98.
Proof. vm_refl. Qed.
Lemma D_82b98 : decode_any W_82b98 = Some (OpImm ALU_SLTU 20 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b9c : bv 32 := 0x00090a93.
Lemma F_82b9c : fetch_word Ubsan.M.loaded_segments (0x82b9c : word) = Some W_82b9c.
Proof. vm_refl. Qed.
Lemma D_82b9c : decode_any W_82b9c = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba0 : bv 32 := 0x00040b13.
Lemma F_82ba0 : fetch_word Ubsan.M.loaded_segments (0x82ba0 : word) = Some W_82ba0.
Proof. vm_refl. Qed.
Lemma D_82ba0 : decode_any W_82ba0 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba4 : bv 32 := 0x060f8663.
Lemma F_82ba4 : fetch_word Ubsan.M.loaded_segments (0x82ba4 : word) = Some W_82ba4.
Proof. vm_refl. Qed.
Lemma D_82ba4 : decode_any W_82ba4 = Some (Branch BC_EQ 31 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba8 : bv 32 := 0x00000793.
Lemma F_82ba8 : fetch_word Ubsan.M.loaded_segments (0x82ba8 : word) = Some W_82ba8.
Proof. vm_refl. Qed.
Lemma D_82ba8 : decode_any W_82ba8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bac : bv 32 := 0x01203833.
Lemma F_82bac : fetch_word Ubsan.M.loaded_segments (0x82bac : word) = Some W_82bac.
Proof. vm_refl. Qed.
Lemma D_82bac : decode_any W_82bac = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb0 : bv 32 := 0x00803e33.
Lemma F_82bb0 : fetch_word Ubsan.M.loaded_segments (0x82bb0 : word) = Some W_82bb0.
Proof. vm_refl. Qed.
Lemma D_82bb0 : decode_any W_82bb0 = Some (Op ALU_SLTU 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb4 : bv 32 := 0x010a7bb3.
Lemma F_82bb4 : fetch_word Ubsan.M.loaded_segments (0x82bb4 : word) = Some W_82bb4.
Proof. vm_refl. Qed.
Lemma D_82bb4 : decode_any W_82bb4 = Some (Op ALU_AND 23 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb8 : bv 32 := 0x01c9fc33.
Lemma F_82bb8 : fetch_word Ubsan.M.loaded_segments (0x82bb8 : word) = Some W_82bb8.
Proof. vm_refl. Qed.
Lemma D_82bb8 : decode_any W_82bb8 = Some (Op ALU_AND 24 19 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bbc : bv 32 := 0x00fa8333.
Lemma F_82bbc : fetch_word Ubsan.M.loaded_segments (0x82bbc : word) = Some W_82bbc.
Proof. vm_refl. Qed.
Lemma D_82bbc : decode_any W_82bbc = Some (Op ALU_ADD 6 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bc0 : bv 32 := 0x93236ae3.
Lemma F_82bc0 : fetch_word Ubsan.M.loaded_segments (0x82bc0 : word) = Some W_82bc0.
Proof. vm_refl. Qed.
Lemma D_82bc0 : decode_any W_82bc0 = Some (Branch BC_LTU 6 18 6452, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bc4 : bv 32 := 0x00133313.
Lemma F_82bc4 : fetch_word Ubsan.M.loaded_segments (0x82bc4 : word) = Some W_82bc4.
Proof. vm_refl. Qed.
Lemma D_82bc4 : decode_any W_82bc4 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bc8 : bv 32 := 0x00684333.
Lemma F_82bc8 : fetch_word Ubsan.M.loaded_segments (0x82bc8 : word) = Some W_82bc8.
Proof. vm_refl. Qed.
Lemma D_82bc8 : decode_any W_82bc8 = Some (Op ALU_XOR 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bcc : bv 32 := 0x920304e3.
Lemma F_82bcc : fetch_word Ubsan.M.loaded_segments (0x82bcc : word) = Some W_82bcc.
Proof. vm_refl. Qed.
Lemma D_82bcc : decode_any W_82bcc = Some (Branch BC_EQ 6 0 6440, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bd0 : bv 32 := 0x920b82e3.
Lemma F_82bd0 : fetch_word Ubsan.M.loaded_segments (0x82bd0 : word) = Some W_82bd0.
Proof. vm_refl. Qed.
Lemma D_82bd0 : decode_any W_82bd0 = Some (Branch BC_EQ 23 0 6436, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bd4 : bv 32 := 0x00fb0333.
Lemma F_82bd4 : fetch_word Ubsan.M.loaded_segments (0x82bd4 : word) = Some W_82bd4.
Proof. vm_refl. Qed.
Lemma D_82bd4 : decode_any W_82bd4 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bd8 : bv 32 := 0x90836ee3.
Lemma F_82bd8 : fetch_word Ubsan.M.loaded_segments (0x82bd8 : word) = Some W_82bd8.
Proof. vm_refl. Qed.
Lemma D_82bd8 : decode_any W_82bd8 = Some (Branch BC_LTU 6 8 6428, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bdc : bv 32 := 0x00133313.
Lemma F_82bdc : fetch_word Ubsan.M.loaded_segments (0x82bdc : word) = Some W_82bdc.
Proof. vm_refl. Qed.
Lemma D_82bdc : decode_any W_82bdc = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82be0 : bv 32 := 0x006e4333.
Lemma F_82be0 : fetch_word Ubsan.M.loaded_segments (0x82be0 : word) = Some W_82be0.
Proof. vm_refl. Qed.
Lemma D_82be0 : decode_any W_82be0 = Some (Op ALU_XOR 6 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82be4 : bv 32 := 0x900308e3.
Lemma F_82be4 : fetch_word Ubsan.M.loaded_segments (0x82be4 : word) = Some W_82be4.
Proof. vm_refl. Qed.
Lemma D_82be4 : decode_any W_82be4 = Some (Branch BC_EQ 6 0 6416, 4%Z).
Proof. vm_refl. Qed.

Definition W_82be8 : bv 32 := 0x900c06e3.
Lemma F_82be8 : fetch_word Ubsan.M.loaded_segments (0x82be8 : word) = Some W_82be8.
Proof. vm_refl. Qed.
Lemma D_82be8 : decode_any W_82be8 = Some (Branch BC_EQ 24 0 6412, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bec : bv 32 := 0x00f90333.
Lemma F_82bec : fetch_word Ubsan.M.loaded_segments (0x82bec : word) = Some W_82bec.
Proof. vm_refl. Qed.
Lemma D_82bec : decode_any W_82bec = Some (Op ALU_ADD 6 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bf0 : bv 32 := 0x00f40cb3.
Lemma F_82bf0 : fetch_word Ubsan.M.loaded_segments (0x82bf0 : word) = Some W_82bf0.
Proof. vm_refl. Qed.
Lemma D_82bf0 : decode_any W_82bf0 = Some (Op ALU_ADD 25 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bf4 : bv 32 := 0x00032303.
Lemma F_82bf4 : fetch_word Ubsan.M.loaded_segments (0x82bf4 : word) = Some W_82bf4.
Proof. vm_refl. Qed.
Lemma D_82bf4 : decode_any W_82bf4 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bf8 : bv 32 := 0x000cad03.
Lemma F_82bf8 : fetch_word Ubsan.M.loaded_segments (0x82bf8 : word) = Some W_82bf8.
Proof. vm_refl. Qed.
Lemma D_82bf8 : decode_any W_82bf8 = Some (Load SZ4 true 26 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bfc : bv 32 := 0x006d7333.
Lemma F_82bfc : fetch_word Ubsan.M.loaded_segments (0x82bfc : word) = Some W_82bfc.
Proof. vm_refl. Qed.
Lemma D_82bfc : decode_any W_82bfc = Some (Op ALU_AND 6 26 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c00 : bv 32 := 0xfff34313.
Lemma F_82c00 : fetch_word Ubsan.M.loaded_segments (0x82c00 : word) = Some W_82c00.
Proof. vm_refl. Qed.
Lemma D_82c00 : decode_any W_82c00 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c04 : bv 32 := 0x00478793.
Lemma F_82c04 : fetch_word Ubsan.M.loaded_segments (0x82c04 : word) = Some W_82c04.
Proof. vm_refl. Qed.
Lemma D_82c04 : decode_any W_82c04 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c08 : bv 32 := 0x006ca023.
Lemma F_82c08 : fetch_word Ubsan.M.loaded_segments (0x82c08 : word) = Some W_82c08.
Proof. vm_refl. Qed.
Lemma D_82c08 : decode_any W_82c08 = Some (Store SZ4 25 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c0c : bv 32 := 0xfaf898e3.
Lemma F_82c0c : fetch_word Ubsan.M.loaded_segments (0x82c0c : word) = Some W_82c0c.
Proof. vm_refl. Qed.
Lemma D_82c0c : decode_any W_82c0c = Some (Branch BC_NE 17 15 8112, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c10 : bv 32 := 0x00c407b3.
Lemma F_82c10 : fetch_word Ubsan.M.loaded_segments (0x82c10 : word) = Some W_82c10.
Proof. vm_refl. Qed.
Lemma D_82c10 : decode_any W_82c10 = Some (Op ALU_ADD 15 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c14 : bv 32 := 0x00803833.
Lemma F_82c14 : fetch_word Ubsan.M.loaded_segments (0x82c14 : word) = Some W_82c14.
Proof. vm_refl. Qed.
Lemma D_82c14 : decode_any W_82c14 = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c18 : bv 32 := 0x0017b313.
Lemma F_82c18 : fetch_word Ubsan.M.loaded_segments (0x82c18 : word) = Some W_82c18.
Proof. vm_refl. Qed.
Lemma D_82c18 : decode_any W_82c18 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c1c : bv 32 := 0x8c680ce3.
Lemma F_82c1c : fetch_word Ubsan.M.loaded_segments (0x82c1c : word) = Some W_82c1c.
Proof. vm_refl. Qed.
Lemma D_82c1c : decode_any W_82c1c = Some (Branch BC_EQ 16 6 6360, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c20 : bv 32 := 0x0087b7b3.
Lemma F_82c20 : fetch_word Ubsan.M.loaded_segments (0x82c20 : word) = Some W_82c20.
Proof. vm_refl. Qed.
Lemma D_82c20 : decode_any W_82c20 = Some (Op ALU_SLTU 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c24 : bv 32 := 0x0057c7b3.
Lemma F_82c24 : fetch_word Ubsan.M.loaded_segments (0x82c24 : word) = Some W_82c24.
Proof. vm_refl. Qed.
Lemma D_82c24 : decode_any W_82c24 = Some (Op ALU_XOR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c28 : bv 32 := 0x0017c793.
Lemma F_82c28 : fetch_word Ubsan.M.loaded_segments (0x82c28 : word) = Some W_82c28.
Proof. vm_refl. Qed.
Lemma D_82c28 : decode_any W_82c28 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c2c : bv 32 := 0x8c0784e3.
Lemma F_82c2c : fetch_word Ubsan.M.loaded_segments (0x82c2c : word) = Some W_82c2c.
Proof. vm_refl. Qed.
Lemma D_82c2c : decode_any W_82c2c = Some (Branch BC_EQ 15 0 6344, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c30 : bv 32 := 0x012687b3.
Lemma F_82c30 : fetch_word Ubsan.M.loaded_segments (0x82c30 : word) = Some W_82c30.
Proof. vm_refl. Qed.
Lemma D_82c30 : decode_any W_82c30 = Some (Op ALU_ADD 15 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c34 : bv 32 := 0x01203833.
Lemma F_82c34 : fetch_word Ubsan.M.loaded_segments (0x82c34 : word) = Some W_82c34.
Proof. vm_refl. Qed.
Lemma D_82c34 : decode_any W_82c34 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c38 : bv 32 := 0x0017b313.
Lemma F_82c38 : fetch_word Ubsan.M.loaded_segments (0x82c38 : word) = Some W_82c38.
Proof. vm_refl. Qed.
Lemma D_82c38 : decode_any W_82c38 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c3c : bv 32 := 0x8a680ce3.
Lemma F_82c3c : fetch_word Ubsan.M.loaded_segments (0x82c3c : word) = Some W_82c3c.
Proof. vm_refl. Qed.
Lemma D_82c3c : decode_any W_82c3c = Some (Branch BC_EQ 16 6 6328, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c40 : bv 32 := 0x0127b833.
Lemma F_82c40 : fetch_word Ubsan.M.loaded_segments (0x82c40 : word) = Some W_82c40.
Proof. vm_refl. Qed.
Lemma D_82c40 : decode_any W_82c40 = Some (Op ALU_SLTU 16 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c44 : bv 32 := 0x00784833.
Lemma F_82c44 : fetch_word Ubsan.M.loaded_segments (0x82c44 : word) = Some W_82c44.
Proof. vm_refl. Qed.
Lemma D_82c44 : decode_any W_82c44 = Some (Op ALU_XOR 16 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c48 : bv 32 := 0x00184813.
Lemma F_82c48 : fetch_word Ubsan.M.loaded_segments (0x82c48 : word) = Some W_82c48.
Proof. vm_refl. Qed.
Lemma D_82c48 : decode_any W_82c48 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c4c : bv 32 := 0x8a0804e3.
Lemma F_82c4c : fetch_word Ubsan.M.loaded_segments (0x82c4c : word) = Some W_82c4c.
Proof. vm_refl. Qed.
Lemma D_82c4c : decode_any W_82c4c = Some (Branch BC_EQ 16 0 6312, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c50 : bv 32 := 0x00c40433.
Lemma F_82c50 : fetch_word Ubsan.M.loaded_segments (0x82c50 : word) = Some W_82c50.
Proof. vm_refl. Qed.
Lemma D_82c50 : decode_any W_82c50 = Some (Op ALU_ADD 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c54 : bv 32 := 0x0015859b.
Lemma F_82c54 : fetch_word Ubsan.M.loaded_segments (0x82c54 : word) = Some W_82c54.
Proof. vm_refl. Qed.
Lemma D_82c54 : decode_any W_82c54 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c58 : bv 32 := 0x00cb0b33.
Lemma F_82c58 : fetch_word Ubsan.M.loaded_segments (0x82c58 : word) = Some W_82c58.
Proof. vm_refl. Qed.
Lemma D_82c58 : decode_any W_82c58 = Some (Op ALU_ADD 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c5c : bv 32 := 0x00da8ab3.
Lemma F_82c5c : fetch_word Ubsan.M.loaded_segments (0x82c5c : word) = Some W_82c5c.
Proof. vm_refl. Qed.
Lemma D_82c5c : decode_any W_82c5c = Some (Op ALU_ADD 21 21 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c60 : bv 32 := 0x00078913.
Lemma F_82c60 : fetch_word Ubsan.M.loaded_segments (0x82c60 : word) = Some W_82c60.
Proof. vm_refl. Qed.
Lemma D_82c60 : decode_any W_82c60 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c64 : bv 32 := 0x08013783.
Lemma F_82c64 : fetch_word Ubsan.M.loaded_segments (0x82c64 : word) = Some W_82c64.
Proof. vm_refl. Qed.
Lemma D_82c64 : decode_any W_82c64 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c68 : bv 32 := 0xf2f59ee3.
Lemma F_82c68 : fetch_word Ubsan.M.loaded_segments (0x82c68 : word) = Some W_82c68.
Proof. vm_refl. Qed.
Lemma D_82c68 : decode_any W_82c68 = Some (Branch BC_NE 11 15 7996, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c6c : bv 32 := 0x00048463.
Lemma F_82c6c : fetch_word Ubsan.M.loaded_segments (0x82c6c : word) = Some W_82c6c.
Proof. vm_refl. Qed.
Lemma D_82c6c : decode_any W_82c6c = Some (Branch BC_EQ 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c70 : bv 32 := 0x1490406f.
Lemma F_82c70 : fetch_word Ubsan.M.loaded_segments (0x82c70 : word) = Some W_82c70.
Proof. vm_refl. Qed.
Lemma D_82c70 : decode_any W_82c70 = Some (Jal 0 18760, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c74 : bv 32 := 0x00357593.
Lemma F_82c74 : fetch_word Ubsan.M.loaded_segments (0x82c74 : word) = Some W_82c74.
Proof. vm_refl. Qed.
Lemma D_82c74 : decode_any W_82c74 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c78 : bv 32 := 0x86059ee3.
Lemma F_82c78 : fetch_word Ubsan.M.loaded_segments (0x82c78 : word) = Some W_82c78.
Proof. vm_refl. Qed.
Lemma D_82c78 : decode_any W_82c78 = Some (Branch BC_NE 11 0 6268, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c7c : bv 32 := 0xfffec613.
Lemma F_82c7c : fetch_word Ubsan.M.loaded_segments (0x82c7c : word) = Some W_82c7c.
Proof. vm_refl. Qed.
Lemma D_82c7c : decode_any W_82c7c = Some (OpImm ALU_XOR 12 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c80 : bv 32 := 0x00271693.
Lemma F_82c80 : fetch_word Ubsan.M.loaded_segments (0x82c80 : word) = Some W_82c80.
Proof. vm_refl. Qed.
Lemma D_82c80 : decode_any W_82c80 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c84 : bv 32 := 0x05813e03.
Lemma F_82c84 : fetch_word Ubsan.M.loaded_segments (0x82c84 : word) = Some W_82c84.
Proof. vm_refl. Qed.
Lemma D_82c84 : decode_any W_82c84 = Some (Load SZ8 true 28 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c88 : bv 32 := 0x002e1793.
Lemma F_82c88 : fetch_word Ubsan.M.loaded_segments (0x82c88 : word) = Some W_82c88.
Proof. vm_refl. Qed.
Lemma D_82c88 : decode_any W_82c88 = Some (ShiftImm ALU_SLL 15 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c8c : bv 32 := 0x03813883.
Lemma F_82c8c : fetch_word Ubsan.M.loaded_segments (0x82c8c : word) = Some W_82c8c.
Proof. vm_refl. Qed.
Lemma D_82c8c : decode_any W_82c8c = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c90 : bv 32 := 0x03013803.
Lemma F_82c90 : fetch_word Ubsan.M.loaded_segments (0x82c90 : word) = Some W_82c90.
Proof. vm_refl. Qed.
Lemma D_82c90 : decode_any W_82c90 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c94 : bv 32 := 0x011808b3.
Lemma F_82c94 : fetch_word Ubsan.M.loaded_segments (0x82c94 : word) = Some W_82c94.
Proof. vm_refl. Qed.
Lemma D_82c94 : decode_any W_82c94 = Some (Op ALU_ADD 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c98 : bv 32 := 0x04813283.
Lemma F_82c98 : fetch_word Ubsan.M.loaded_segments (0x82c98 : word) = Some W_82c98.
Proof. vm_refl. Qed.
Lemma D_82c98 : decode_any W_82c98 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c9c : bv 32 := 0x43f2d813.
Lemma F_82c9c : fetch_word Ubsan.M.loaded_segments (0x82c9c : word) = Some W_82c9c.
Proof. vm_refl. Qed.
Lemma D_82c9c : decode_any W_82c9c = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ca0 : bv 32 := 0x005872b3.
Lemma F_82ca0 : fetch_word Ubsan.M.loaded_segments (0x82ca0 : word) = Some W_82ca0.
Proof. vm_refl. Qed.
Lemma D_82ca0 : decode_any W_82ca0 = Some (Op ALU_AND 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ca4 : bv 32 := 0x003f7813.
Lemma F_82ca4 : fetch_word Ubsan.M.loaded_segments (0x82ca4 : word) = Some W_82ca4.
Proof. vm_refl. Qed.
Lemma D_82ca4 : decode_any W_82ca4 = Some (OpImm ALU_AND 16 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ca8 : bv 32 := 0x05013383.
Lemma F_82ca8 : fetch_word Ubsan.M.loaded_segments (0x82ca8 : word) = Some W_82ca8.
Proof. vm_refl. Qed.
Lemma D_82ca8 : decode_any W_82ca8 = Some (Load SZ8 true 7 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cac : bv 32 := 0x02813303.
Lemma F_82cac : fetch_word Ubsan.M.loaded_segments (0x82cac : word) = Some W_82cac.
Proof. vm_refl. Qed.
Lemma D_82cac : decode_any W_82cac = Some (Load SZ8 true 6 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cb0 : bv 32 := 0x4073033b.
Lemma F_82cb0 : fetch_word Ubsan.M.loaded_segments (0x82cb0 : word) = Some W_82cb0.
Proof. vm_refl. Qed.
Lemma D_82cb0 : decode_any W_82cb0 = Some (Op32 ALU_SUB 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cb4 : bv 32 := 0x00072713.
Lemma F_82cb4 : fetch_word Ubsan.M.loaded_segments (0x82cb4 : word) = Some W_82cb4.
Proof. vm_refl. Qed.
Lemma D_82cb4 : decode_any W_82cb4 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cb8 : bv 32 := 0x005882b3.
Lemma F_82cb8 : fetch_word Ubsan.M.loaded_segments (0x82cb8 : word) = Some W_82cb8.
Proof. vm_refl. Qed.
Lemma D_82cb8 : decode_any W_82cb8 = Some (Op ALU_ADD 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cbc : bv 32 := 0x00ff08b3.
Lemma F_82cbc : fetch_word Ubsan.M.loaded_segments (0x82cbc : word) = Some W_82cbc.
Proof. vm_refl. Qed.
Lemma D_82cbc : decode_any W_82cbc = Some (Op ALU_ADD 17 30 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cc0 : bv 32 := 0x407282bb.
Lemma F_82cc0 : fetch_word Ubsan.M.loaded_segments (0x82cc0 : word) = Some W_82cc0.
Proof. vm_refl. Qed.
Lemma D_82cc0 : decode_any W_82cc0 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cc4 : bv 32 := 0x04013383.
Lemma F_82cc4 : fetch_word Ubsan.M.loaded_segments (0x82cc4 : word) = Some W_82cc4.
Proof. vm_refl. Qed.
Lemma D_82cc4 : decode_any W_82cc4 = Some (Load SZ8 true 7 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cc8 : bv 32 := 0x407282bb.
Lemma F_82cc8 : fetch_word Ubsan.M.loaded_segments (0x82cc8 : word) = Some W_82cc8.
Proof. vm_refl. Qed.
Lemma D_82cc8 : decode_any W_82cc8 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ccc : bv 32 := 0x43f2d393.
Lemma F_82ccc : fetch_word Ubsan.M.loaded_segments (0x82ccc : word) = Some W_82ccc.
Proof. vm_refl. Qed.
Lemma D_82ccc : decode_any W_82ccc = Some (ShiftImm ALU_SRA 7 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cd0 : bv 32 := 0x0053f2b3.
Lemma F_82cd0 : fetch_word Ubsan.M.loaded_segments (0x82cd0 : word) = Some W_82cd0.
Proof. vm_refl. Qed.
Lemma D_82cd0 : decode_any W_82cd0 = Some (Op ALU_AND 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cd4 : bv 32 := 0x405302bb.
Lemma F_82cd4 : fetch_word Ubsan.M.loaded_segments (0x82cd4 : word) = Some W_82cd4.
Proof. vm_refl. Qed.
Lemma D_82cd4 : decode_any W_82cd4 = Some (Op32 ALU_SUB 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cd8 : bv 32 := 0x000e2313.
Lemma F_82cd8 : fetch_word Ubsan.M.loaded_segments (0x82cd8 : word) = Some W_82cd8.
Proof. vm_refl. Qed.
Lemma D_82cd8 : decode_any W_82cd8 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cdc : bv 32 := 0x00050393.
Lemma F_82cdc : fetch_word Ubsan.M.loaded_segments (0x82cdc : word) = Some W_82cdc.
Proof. vm_refl. Qed.
Lemma D_82cdc : decode_any W_82cdc = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ce0 : bv 32 := 0x80050ae3.
Lemma F_82ce0 : fetch_word Ubsan.M.loaded_segments (0x82ce0 : word) = Some W_82ce0.
Proof. vm_refl. Qed.
Lemma D_82ce0 : decode_any W_82ce0 = Some (Branch BC_EQ 10 0 6164, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ce4 : bv 32 := 0x800818e3.
Lemma F_82ce4 : fetch_word Ubsan.M.loaded_segments (0x82ce4 : word) = Some W_82ce4.
Proof. vm_refl. Qed.
Lemma D_82ce4 : decode_any W_82ce4 = Some (Branch BC_NE 16 0 6160, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ce8 : bv 32 := 0x00bf0e33.
Lemma F_82ce8 : fetch_word Ubsan.M.loaded_segments (0x82ce8 : word) = Some W_82ce8.
Proof. vm_refl. Qed.
Lemma D_82ce8 : decode_any W_82ce8 = Some (Op ALU_ADD 28 30 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cec : bv 32 := 0x800e04e3.
Lemma F_82cec : fetch_word Ubsan.M.loaded_segments (0x82cec : word) = Some W_82cec.
Proof. vm_refl. Qed.
Lemma D_82cec : decode_any W_82cec = Some (Branch BC_EQ 28 0 6152, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cf0 : bv 32 := 0x00052f83.
Lemma F_82cf0 : fetch_word Ubsan.M.loaded_segments (0x82cf0 : word) = Some W_82cf0.
Proof. vm_refl. Qed.
Lemma D_82cf0 : decode_any W_82cf0 = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cf4 : bv 32 := 0x000e2403.
Lemma F_82cf4 : fetch_word Ubsan.M.loaded_segments (0x82cf4 : word) = Some W_82cf4.
Proof. vm_refl. Qed.
Lemma D_82cf4 : decode_any W_82cf4 = Some (Load SZ4 true 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cf8 : bv 32 := 0x00cff4b3.
Lemma F_82cf8 : fetch_word Ubsan.M.loaded_segments (0x82cf8 : word) = Some W_82cf8.
Proof. vm_refl. Qed.
Lemma D_82cf8 : decode_any W_82cf8 = Some (Op ALU_AND 9 31 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cfc : bv 32 := 0x01f47fb3.
Lemma F_82cfc : fetch_word Ubsan.M.loaded_segments (0x82cfc : word) = Some W_82cfc.
Proof. vm_refl. Qed.
Lemma D_82cfc : decode_any W_82cfc = Some (Op ALU_AND 31 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d00 : bv 32 := 0xffffcf93.
Lemma F_82d00 : fetch_word Ubsan.M.loaded_segments (0x82d00 : word) = Some W_82d00.
Proof. vm_refl. Qed.
Lemma D_82d00 : decode_any W_82d00 = Some (OpImm ALU_XOR 31 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d04 : bv 32 := 0x01feffb3.
Lemma F_82d04 : fetch_word Ubsan.M.loaded_segments (0x82d04 : word) = Some W_82d04.
Proof. vm_refl. Qed.
Lemma D_82d04 : decode_any W_82d04 = Some (Op ALU_AND 31 29 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d08 : bv 32 := 0x009fe433.
Lemma F_82d08 : fetch_word Ubsan.M.loaded_segments (0x82d08 : word) = Some W_82d08.
Proof. vm_refl. Qed.
Lemma D_82d08 : decode_any W_82d08 = Some (Op ALU_OR 8 31 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d0c : bv 32 := 0x00768fb3.
Lemma F_82d0c : fetch_word Ubsan.M.loaded_segments (0x82d0c : word) = Some W_82d0c.
Proof. vm_refl. Qed.
Lemma D_82d0c : decode_any W_82d0c = Some (Op ALU_ADD 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d10 : bv 32 := 0x00852023.
Lemma F_82d10 : fetch_word Ubsan.M.loaded_segments (0x82d10 : word) = Some W_82d10.
Proof. vm_refl. Qed.
Lemma D_82d10 : decode_any W_82d10 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d14 : bv 32 := 0xfe0f8063.
Lemma F_82d14 : fetch_word Ubsan.M.loaded_segments (0x82d14 : word) = Some W_82d14.
Proof. vm_refl. Qed.
Lemma D_82d14 : decode_any W_82d14 = Some (Branch BC_EQ 31 0 6112, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d18 : bv 32 := 0x007fb3b3.
Lemma F_82d18 : fetch_word Ubsan.M.loaded_segments (0x82d18 : word) = Some W_82d18.
Proof. vm_refl. Qed.
Lemma D_82d18 : decode_any W_82d18 = Some (Op ALU_SLTU 7 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d1c : bv 32 := 0x00e3c3b3.
Lemma F_82d1c : fetch_word Ubsan.M.loaded_segments (0x82d1c : word) = Some W_82d1c.
Proof. vm_refl. Qed.
Lemma D_82d1c : decode_any W_82d1c = Some (Op ALU_XOR 7 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d20 : bv 32 := 0x0013c393.
Lemma F_82d20 : fetch_word Ubsan.M.loaded_segments (0x82d20 : word) = Some W_82d20.
Proof. vm_refl. Qed.
Lemma D_82d20 : decode_any W_82d20 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d24 : bv 32 := 0xfc038863.
Lemma F_82d24 : fetch_word Ubsan.M.loaded_segments (0x82d24 : word) = Some W_82d24.
Proof. vm_refl. Qed.
Lemma D_82d24 : decode_any W_82d24 = Some (Branch BC_EQ 7 0 6096, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d28 : bv 32 := 0x00b883b3.
Lemma F_82d28 : fetch_word Ubsan.M.loaded_segments (0x82d28 : word) = Some W_82d28.
Proof. vm_refl. Qed.
Lemma D_82d28 : decode_any W_82d28 = Some (Op ALU_ADD 7 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d2c : bv 32 := 0xfc038463.
Lemma F_82d2c : fetch_word Ubsan.M.loaded_segments (0x82d2c : word) = Some W_82d2c.
Proof. vm_refl. Qed.
Lemma D_82d2c : decode_any W_82d2c = Some (Branch BC_EQ 7 0 6088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d30 : bv 32 := 0x01c3b3b3.
Lemma F_82d30 : fetch_word Ubsan.M.loaded_segments (0x82d30 : word) = Some W_82d30.
Proof. vm_refl. Qed.
Lemma D_82d30 : decode_any W_82d30 = Some (Op ALU_SLTU 7 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d34 : bv 32 := 0x0063c3b3.
Lemma F_82d34 : fetch_word Ubsan.M.loaded_segments (0x82d34 : word) = Some W_82d34.
Proof. vm_refl. Qed.
Lemma D_82d34 : decode_any W_82d34 = Some (Op ALU_XOR 7 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d38 : bv 32 := 0x0013c393.
Lemma F_82d38 : fetch_word Ubsan.M.loaded_segments (0x82d38 : word) = Some W_82d38.
Proof. vm_refl. Qed.
Lemma D_82d38 : decode_any W_82d38 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d3c : bv 32 := 0xfa038c63.
Lemma F_82d3c : fetch_word Ubsan.M.loaded_segments (0x82d3c : word) = Some W_82d3c.
Proof. vm_refl. Qed.
Lemma D_82d3c : decode_any W_82d3c = Some (Branch BC_EQ 7 0 6072, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d40 : bv 32 := 0x0012829b.
Lemma F_82d40 : fetch_word Ubsan.M.loaded_segments (0x82d40 : word) = Some W_82d40.
Proof. vm_refl. Qed.
Lemma D_82d40 : decode_any W_82d40 = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d44 : bv 32 := 0x00f585b3.
Lemma F_82d44 : fetch_word Ubsan.M.loaded_segments (0x82d44 : word) = Some W_82d44.
Proof. vm_refl. Qed.
Lemma D_82d44 : decode_any W_82d44 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d48 : bv 32 := 0x00d50533.
Lemma F_82d48 : fetch_word Ubsan.M.loaded_segments (0x82d48 : word) = Some W_82d48.
Proof. vm_refl. Qed.
Lemma D_82d48 : decode_any W_82d48 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d4c : bv 32 := 0x000f8393.
Lemma F_82d4c : fetch_word Ubsan.M.loaded_segments (0x82d4c : word) = Some W_82d4c.
Proof. vm_refl. Qed.
Lemma D_82d4c : decode_any W_82d4c = Some (OpImm ALU_ADD 7 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d50 : bv 32 := 0xf80298e3.
Lemma F_82d50 : fetch_word Ubsan.M.loaded_segments (0x82d50 : word) = Some W_82d50.
Proof. vm_refl. Qed.
Lemma D_82d50 : decode_any W_82d50 = Some (Branch BC_NE 5 0 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d54 : bv 32 := 0x0650406f.
Lemma F_82d54 : fetch_word Ubsan.M.loaded_segments (0x82d54 : word) = Some W_82d54.
Proof. vm_refl. Qed.
Lemma D_82d54 : decode_any W_82d54 = Some (Jal 0 18532, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d58 : bv 32 := 0x0e008063.
Lemma F_82d58 : fetch_word Ubsan.M.loaded_segments (0x82d58 : word) = Some W_82d58.
Proof. vm_refl. Qed.
Lemma D_82d58 : decode_any W_82d58 = Some (Branch BC_EQ 1 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d5c : bv 32 := 0x003a7593.
Lemma F_82d5c : fetch_word Ubsan.M.loaded_segments (0x82d5c : word) = Some W_82d5c.
Proof. vm_refl. Qed.
Lemma D_82d5c : decode_any W_82d5c = Some (OpImm ALU_AND 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d60 : bv 32 := 0xf8059a63.
Lemma F_82d60 : fetch_word Ubsan.M.loaded_segments (0x82d60 : word) = Some W_82d60.
Proof. vm_refl. Qed.
Lemma D_82d60 : decode_any W_82d60 = Some (Branch BC_NE 11 0 6036, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d64 : bv 32 := 0xfffbc613.
Lemma F_82d64 : fetch_word Ubsan.M.loaded_segments (0x82d64 : word) = Some W_82d64.
Proof. vm_refl. Qed.
Lemma D_82d64 : decode_any W_82d64 = Some (OpImm ALU_XOR 12 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d68 : bv 32 := 0x00271693.
Lemma F_82d68 : fetch_word Ubsan.M.loaded_segments (0x82d68 : word) = Some W_82d68.
Proof. vm_refl. Qed.
Lemma D_82d68 : decode_any W_82d68 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d6c : bv 32 := 0x05813983.
Lemma F_82d6c : fetch_word Ubsan.M.loaded_segments (0x82d6c : word) = Some W_82d6c.
Proof. vm_refl. Qed.
Lemma D_82d6c : decode_any W_82d6c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d70 : bv 32 := 0x00299893.
Lemma F_82d70 : fetch_word Ubsan.M.loaded_segments (0x82d70 : word) = Some W_82d70.
Proof. vm_refl. Qed.
Lemma D_82d70 : decode_any W_82d70 = Some (ShiftImm ALU_SLL 17 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d74 : bv 32 := 0x003af293.
Lemma F_82d74 : fetch_word Ubsan.M.loaded_segments (0x82d74 : word) = Some W_82d74.
Proof. vm_refl. Qed.
Lemma D_82d74 : decode_any W_82d74 = Some (OpImm ALU_AND 5 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d78 : bv 32 := 0x05013e03.
Lemma F_82d78 : fetch_word Ubsan.M.loaded_segments (0x82d78 : word) = Some W_82d78.
Proof. vm_refl. Qed.
Lemma D_82d78 : decode_any W_82d78 = Some (Load SZ8 true 28 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d7c : bv 32 := 0x02813783.
Lemma F_82d7c : fetch_word Ubsan.M.loaded_segments (0x82d7c : word) = Some W_82d7c.
Proof. vm_refl. Qed.
Lemma D_82d7c : decode_any W_82d7c = Some (Load SZ8 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d80 : bv 32 := 0x41c7833b.
Lemma F_82d80 : fetch_word Ubsan.M.loaded_segments (0x82d80 : word) = Some W_82d80.
Proof. vm_refl. Qed.
Lemma D_82d80 : decode_any W_82d80 = Some (Op32 ALU_SUB 6 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d84 : bv 32 := 0x03813803.
Lemma F_82d84 : fetch_word Ubsan.M.loaded_segments (0x82d84 : word) = Some W_82d84.
Proof. vm_refl. Qed.
Lemma D_82d84 : decode_any W_82d84 = Some (Load SZ8 true 16 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d88 : bv 32 := 0x03013783.
Lemma F_82d88 : fetch_word Ubsan.M.loaded_segments (0x82d88 : word) = Some W_82d88.
Proof. vm_refl. Qed.
Lemma D_82d88 : decode_any W_82d88 = Some (Load SZ8 true 15 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d8c : bv 32 := 0x01078833.
Lemma F_82d8c : fetch_word Ubsan.M.loaded_segments (0x82d8c : word) = Some W_82d8c.
Proof. vm_refl. Qed.
Lemma D_82d8c : decode_any W_82d8c = Some (Op ALU_ADD 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d90 : bv 32 := 0x04813c03.
Lemma F_82d90 : fetch_word Ubsan.M.loaded_segments (0x82d90 : word) = Some W_82d90.
Proof. vm_refl. Qed.
Lemma D_82d90 : decode_any W_82d90 = Some (Load SZ8 true 24 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d94 : bv 32 := 0x43fc5393.
Lemma F_82d94 : fetch_word Ubsan.M.loaded_segments (0x82d94 : word) = Some W_82d94.
Proof. vm_refl. Qed.
Lemma D_82d94 : decode_any W_82d94 = Some (ShiftImm ALU_SRA 7 24 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d98 : bv 32 := 0x00072793.
Lemma F_82d98 : fetch_word Ubsan.M.loaded_segments (0x82d98 : word) = Some W_82d98.
Proof. vm_refl. Qed.
Lemma D_82d98 : decode_any W_82d98 = Some (OpImm ALU_SLT 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d9c : bv 32 := 0x0183f3b3.
Lemma F_82d9c : fetch_word Ubsan.M.loaded_segments (0x82d9c : word) = Some W_82d9c.
Proof. vm_refl. Qed.
Lemma D_82d9c : decode_any W_82d9c = Some (Op ALU_AND 7 7 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82da0 : bv 32 := 0x41c80e3b.
Lemma F_82da0 : fetch_word Ubsan.M.loaded_segments (0x82da0 : word) = Some W_82da0.
Proof. vm_refl. Qed.
Lemma D_82da0 : decode_any W_82da0 = Some (Op32 ALU_SUB 28 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82da4 : bv 32 := 0x011a8833.
Lemma F_82da4 : fetch_word Ubsan.M.loaded_segments (0x82da4 : word) = Some W_82da4.
Proof. vm_refl. Qed.
Lemma D_82da4 : decode_any W_82da4 = Some (Op ALU_ADD 16 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82da8 : bv 32 := 0x04013c03.
Lemma F_82da8 : fetch_word Ubsan.M.loaded_segments (0x82da8 : word) = Some W_82da8.
Proof. vm_refl. Qed.
Lemma D_82da8 : decode_any W_82da8 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dac : bv 32 := 0x418e0e3b.
Lemma F_82dac : fetch_word Ubsan.M.loaded_segments (0x82dac : word) = Some W_82dac.
Proof. vm_refl. Qed.
Lemma D_82dac : decode_any W_82dac = Some (Op32 ALU_SUB 28 28 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82db0 : bv 32 := 0x007e03bb.
Lemma F_82db0 : fetch_word Ubsan.M.loaded_segments (0x82db0 : word) = Some W_82db0.
Proof. vm_refl. Qed.
Lemma D_82db0 : decode_any W_82db0 = Some (Op32 ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82db4 : bv 32 := 0x43f3de13.
Lemma F_82db4 : fetch_word Ubsan.M.loaded_segments (0x82db4 : word) = Some W_82db4.
Proof. vm_refl. Qed.
Lemma D_82db4 : decode_any W_82db4 = Some (ShiftImm ALU_SRA 28 7 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82db8 : bv 32 := 0x007e73b3.
Lemma F_82db8 : fetch_word Ubsan.M.loaded_segments (0x82db8 : word) = Some W_82db8.
Proof. vm_refl. Qed.
Lemma D_82db8 : decode_any W_82db8 = Some (Op ALU_AND 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dbc : bv 32 := 0x407303bb.
Lemma F_82dbc : fetch_word Ubsan.M.loaded_segments (0x82dbc : word) = Some W_82dbc.
Proof. vm_refl. Qed.
Lemma D_82dbc : decode_any W_82dbc = Some (Op32 ALU_SUB 7 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dc0 : bv 32 := 0x0009ae13.
Lemma F_82dc0 : fetch_word Ubsan.M.loaded_segments (0x82dc0 : word) = Some W_82dc0.
Proof. vm_refl. Qed.
Lemma D_82dc0 : decode_any W_82dc0 = Some (OpImm ALU_SLT 28 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dc4 : bv 32 := 0x000a0993.
Lemma F_82dc4 : fetch_word Ubsan.M.loaded_segments (0x82dc4 : word) = Some W_82dc4.
Proof. vm_refl. Qed.
Lemma D_82dc4 : decode_any W_82dc4 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dc8 : bv 32 := 0xf20a0663.
Lemma F_82dc8 : fetch_word Ubsan.M.loaded_segments (0x82dc8 : word) = Some W_82dc8.
Proof. vm_refl. Qed.
Lemma D_82dc8 : decode_any W_82dc8 = Some (Branch BC_EQ 20 0 5932, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dcc : bv 32 := 0xf2029463.
Lemma F_82dcc : fetch_word Ubsan.M.loaded_segments (0x82dcc : word) = Some W_82dcc.
Proof. vm_refl. Qed.
Lemma D_82dcc : decode_any W_82dcc = Some (Branch BC_NE 5 0 5928, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dd0 : bv 32 := 0x00ba8c33.
Lemma F_82dd0 : fetch_word Ubsan.M.loaded_segments (0x82dd0 : word) = Some W_82dd0.
Proof. vm_refl. Qed.
Lemma D_82dd0 : decode_any W_82dd0 = Some (Op ALU_ADD 24 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dd4 : bv 32 := 0xf20c0063.
Lemma F_82dd4 : fetch_word Ubsan.M.loaded_segments (0x82dd4 : word) = Some W_82dd4.
Proof. vm_refl. Qed.
Lemma D_82dd4 : decode_any W_82dd4 = Some (Branch BC_EQ 24 0 5920, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dd8 : bv 32 := 0x000a2303.
Lemma F_82dd8 : fetch_word Ubsan.M.loaded_segments (0x82dd8 : word) = Some W_82dd8.
Proof. vm_refl. Qed.
Lemma D_82dd8 : decode_any W_82dd8 = Some (Load SZ4 true 6 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ddc : bv 32 := 0x000c2c83.
Lemma F_82ddc : fetch_word Ubsan.M.loaded_segments (0x82ddc : word) = Some W_82ddc.
Proof. vm_refl. Qed.
Lemma D_82ddc : decode_any W_82ddc = Some (Load SZ4 true 25 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82de0 : bv 32 := 0x00c37d33.
Lemma F_82de0 : fetch_word Ubsan.M.loaded_segments (0x82de0 : word) = Some W_82de0.
Proof. vm_refl. Qed.
Lemma D_82de0 : decode_any W_82de0 = Some (Op ALU_AND 26 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82de4 : bv 32 := 0x006ce333.
Lemma F_82de4 : fetch_word Ubsan.M.loaded_segments (0x82de4 : word) = Some W_82de4.
Proof. vm_refl. Qed.
Lemma D_82de4 : decode_any W_82de4 = Some (Op ALU_OR 6 25 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82de8 : bv 32 := 0x01737333.
Lemma F_82de8 : fetch_word Ubsan.M.loaded_segments (0x82de8 : word) = Some W_82de8.
Proof. vm_refl. Qed.
Lemma D_82de8 : decode_any W_82de8 = Some (Op ALU_AND 6 6 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dec : bv 32 := 0x01a36333.
Lemma F_82dec : fetch_word Ubsan.M.loaded_segments (0x82dec : word) = Some W_82dec.
Proof. vm_refl. Qed.
Lemma D_82dec : decode_any W_82dec = Some (Op ALU_OR 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_82df0 : bv 32 := 0x01368cb3.
Lemma F_82df0 : fetch_word Ubsan.M.loaded_segments (0x82df0 : word) = Some W_82df0.
Proof. vm_refl. Qed.
Lemma D_82df0 : decode_any W_82df0 = Some (Op ALU_ADD 25 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82df4 : bv 32 := 0x006a2023.
Lemma F_82df4 : fetch_word Ubsan.M.loaded_segments (0x82df4 : word) = Some W_82df4.
Proof. vm_refl. Qed.
Lemma D_82df4 : decode_any W_82df4 = Some (Store SZ4 20 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82df8 : bv 32 := 0xee0c8e63.
Lemma F_82df8 : fetch_word Ubsan.M.loaded_segments (0x82df8 : word) = Some W_82df8.
Proof. vm_refl. Qed.
Lemma D_82df8 : decode_any W_82df8 = Some (Branch BC_EQ 25 0 5884, 4%Z).
Proof. vm_refl. Qed.

Definition W_82dfc : bv 32 := 0x013cb333.
Lemma F_82dfc : fetch_word Ubsan.M.loaded_segments (0x82dfc : word) = Some W_82dfc.
Proof. vm_refl. Qed.
Lemma D_82dfc : decode_any W_82dfc = Some (Op ALU_SLTU 6 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e00 : bv 32 := 0x00f34333.
Lemma F_82e00 : fetch_word Ubsan.M.loaded_segments (0x82e00 : word) = Some W_82e00.
Proof. vm_refl. Qed.
Lemma D_82e00 : decode_any W_82e00 = Some (Op ALU_XOR 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e04 : bv 32 := 0x00134313.
Lemma F_82e04 : fetch_word Ubsan.M.loaded_segments (0x82e04 : word) = Some W_82e04.
Proof. vm_refl. Qed.
Lemma D_82e04 : decode_any W_82e04 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e08 : bv 32 := 0xee030663.
Lemma F_82e08 : fetch_word Ubsan.M.loaded_segments (0x82e08 : word) = Some W_82e08.
Proof. vm_refl. Qed.
Lemma D_82e08 : decode_any W_82e08 = Some (Branch BC_EQ 6 0 5868, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e0c : bv 32 := 0x00b80333.
Lemma F_82e0c : fetch_word Ubsan.M.loaded_segments (0x82e0c : word) = Some W_82e0c.
Proof. vm_refl. Qed.
Lemma D_82e0c : decode_any W_82e0c = Some (Op ALU_ADD 6 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e10 : bv 32 := 0xee030263.
Lemma F_82e10 : fetch_word Ubsan.M.loaded_segments (0x82e10 : word) = Some W_82e10.
Proof. vm_refl. Qed.
Lemma D_82e10 : decode_any W_82e10 = Some (Branch BC_EQ 6 0 5860, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e14 : bv 32 := 0x01833333.
Lemma F_82e14 : fetch_word Ubsan.M.loaded_segments (0x82e14 : word) = Some W_82e14.
Proof. vm_refl. Qed.
Lemma D_82e14 : decode_any W_82e14 = Some (Op ALU_SLTU 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e18 : bv 32 := 0x01c34333.
Lemma F_82e18 : fetch_word Ubsan.M.loaded_segments (0x82e18 : word) = Some W_82e18.
Proof. vm_refl. Qed.
Lemma D_82e18 : decode_any W_82e18 = Some (Op ALU_XOR 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e1c : bv 32 := 0x00134313.
Lemma F_82e1c : fetch_word Ubsan.M.loaded_segments (0x82e1c : word) = Some W_82e1c.
Proof. vm_refl. Qed.
Lemma D_82e1c : decode_any W_82e1c = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e20 : bv 32 := 0xec030a63.
Lemma F_82e20 : fetch_word Ubsan.M.loaded_segments (0x82e20 : word) = Some W_82e20.
Proof. vm_refl. Qed.
Lemma D_82e20 : decode_any W_82e20 = Some (Branch BC_EQ 6 0 5844, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e24 : bv 32 := 0x0013839b.
Lemma F_82e24 : fetch_word Ubsan.M.loaded_segments (0x82e24 : word) = Some W_82e24.
Proof. vm_refl. Qed.
Lemma D_82e24 : decode_any W_82e24 = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e28 : bv 32 := 0x011585b3.
Lemma F_82e28 : fetch_word Ubsan.M.loaded_segments (0x82e28 : word) = Some W_82e28.
Proof. vm_refl. Qed.
Lemma D_82e28 : decode_any W_82e28 = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e2c : bv 32 := 0x00da0a33.
Lemma F_82e2c : fetch_word Ubsan.M.loaded_segments (0x82e2c : word) = Some W_82e2c.
Proof. vm_refl. Qed.
Lemma D_82e2c : decode_any W_82e2c = Some (Op ALU_ADD 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e30 : bv 32 := 0x000c8993.
Lemma F_82e30 : fetch_word Ubsan.M.loaded_segments (0x82e30 : word) = Some W_82e30.
Proof. vm_refl. Qed.
Lemma D_82e30 : decode_any W_82e30 = Some (OpImm ALU_ADD 19 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e34 : bv 32 := 0xf8039ae3.
Lemma F_82e34 : fetch_word Ubsan.M.loaded_segments (0x82e34 : word) = Some W_82e34.
Proof. vm_refl. Qed.
Lemma D_82e34 : decode_any W_82e34 = Some (Branch BC_NE 7 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e38 : bv 32 := 0x0e0b1e63.
Lemma F_82e38 : fetch_word Ubsan.M.loaded_segments (0x82e38 : word) = Some W_82e38.
Proof. vm_refl. Qed.
Lemma D_82e38 : decode_any W_82e38 = Some (Branch BC_NE 22 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e3c : bv 32 := 0x00000593.
Lemma F_82e3c : fetch_word Ubsan.M.loaded_segments (0x82e3c : word) = Some W_82e3c.
Proof. vm_refl. Qed.
Lemma D_82e3c : decode_any W_82e3c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e40 : bv 32 := 0x00271613.
Lemma F_82e40 : fetch_word Ubsan.M.loaded_segments (0x82e40 : word) = Some W_82e40.
Proof. vm_refl. Qed.
Lemma D_82e40 : decode_any W_82e40 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e44 : bv 32 := 0x05813303.
Lemma F_82e44 : fetch_word Ubsan.M.loaded_segments (0x82e44 : word) = Some W_82e44.
Proof. vm_refl. Qed.
Lemma D_82e44 : decode_any W_82e44 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e48 : bv 32 := 0x00231693.
Lemma F_82e48 : fetch_word Ubsan.M.loaded_segments (0x82e48 : word) = Some W_82e48.
Proof. vm_refl. Qed.
Lemma D_82e48 : decode_any W_82e48 = Some (ShiftImm ALU_SLL 13 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e4c : bv 32 := 0x00397793.
Lemma F_82e4c : fetch_word Ubsan.M.loaded_segments (0x82e4c : word) = Some W_82e4c.
Proof. vm_refl. Qed.
Lemma D_82e4c : decode_any W_82e4c = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e50 : bv 32 := 0x00347813.
Lemma F_82e50 : fetch_word Ubsan.M.loaded_segments (0x82e50 : word) = Some W_82e50.
Proof. vm_refl. Qed.
Lemma D_82e50 : decode_any W_82e50 = Some (OpImm ALU_AND 16 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e54 : bv 32 := 0x002f9893.
Lemma F_82e54 : fetch_word Ubsan.M.loaded_segments (0x82e54 : word) = Some W_82e54.
Proof. vm_refl. Qed.
Lemma D_82e54 : decode_any W_82e54 = Some (ShiftImm ALU_SLL 17 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e58 : bv 32 := 0x00072293.
Lemma F_82e58 : fetch_word Ubsan.M.loaded_segments (0x82e58 : word) = Some W_82e58.
Proof. vm_refl. Qed.
Lemma D_82e58 : decode_any W_82e58 = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e5c : bv 32 := 0x00032393.
Lemma F_82e5c : fetch_word Ubsan.M.loaded_segments (0x82e5c : word) = Some W_82e5c.
Proof. vm_refl. Qed.
Lemma D_82e5c : decode_any W_82e5c = Some (OpImm ALU_SLT 7 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e60 : bv 32 := 0x00183993.
Lemma F_82e60 : fetch_word Ubsan.M.loaded_segments (0x82e60 : word) = Some W_82e60.
Proof. vm_refl. Qed.
Lemma D_82e60 : decode_any W_82e60 = Some (OpImm ALU_SLTU 19 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e64 : bv 32 := 0x0017ba13.
Lemma F_82e64 : fetch_word Ubsan.M.loaded_segments (0x82e64 : word) = Some W_82e64.
Proof. vm_refl. Qed.
Lemma D_82e64 : decode_any W_82e64 = Some (OpImm ALU_SLTU 20 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e68 : bv 32 := 0x00090a93.
Lemma F_82e68 : fetch_word Ubsan.M.loaded_segments (0x82e68 : word) = Some W_82e68.
Proof. vm_refl. Qed.
Lemma D_82e68 : decode_any W_82e68 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e6c : bv 32 := 0x00040b13.
Lemma F_82e6c : fetch_word Ubsan.M.loaded_segments (0x82e6c : word) = Some W_82e6c.
Proof. vm_refl. Qed.
Lemma D_82e6c : decode_any W_82e6c = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e70 : bv 32 := 0x060f8463.
Lemma F_82e70 : fetch_word Ubsan.M.loaded_segments (0x82e70 : word) = Some W_82e70.
Proof. vm_refl. Qed.
Lemma D_82e70 : decode_any W_82e70 = Some (Branch BC_EQ 31 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e74 : bv 32 := 0x00000793.
Lemma F_82e74 : fetch_word Ubsan.M.loaded_segments (0x82e74 : word) = Some W_82e74.
Proof. vm_refl. Qed.
Lemma D_82e74 : decode_any W_82e74 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e78 : bv 32 := 0x01203833.
Lemma F_82e78 : fetch_word Ubsan.M.loaded_segments (0x82e78 : word) = Some W_82e78.
Proof. vm_refl. Qed.
Lemma D_82e78 : decode_any W_82e78 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e7c : bv 32 := 0x00803e33.
Lemma F_82e7c : fetch_word Ubsan.M.loaded_segments (0x82e7c : word) = Some W_82e7c.
Proof. vm_refl. Qed.
Lemma D_82e7c : decode_any W_82e7c = Some (Op ALU_SLTU 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e80 : bv 32 := 0x010a7bb3.
Lemma F_82e80 : fetch_word Ubsan.M.loaded_segments (0x82e80 : word) = Some W_82e80.
Proof. vm_refl. Qed.
Lemma D_82e80 : decode_any W_82e80 = Some (Op ALU_AND 23 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e84 : bv 32 := 0x01c9fc33.
Lemma F_82e84 : fetch_word Ubsan.M.loaded_segments (0x82e84 : word) = Some W_82e84.
Proof. vm_refl. Qed.
Lemma D_82e84 : decode_any W_82e84 = Some (Op ALU_AND 24 19 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e88 : bv 32 := 0x00fa8333.
Lemma F_82e88 : fetch_word Ubsan.M.loaded_segments (0x82e88 : word) = Some W_82e88.
Proof. vm_refl. Qed.
Lemma D_82e88 : decode_any W_82e88 = Some (Op ALU_ADD 6 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e8c : bv 32 := 0xe7236463.
Lemma F_82e8c : fetch_word Ubsan.M.loaded_segments (0x82e8c : word) = Some W_82e8c.
Proof. vm_refl. Qed.
Lemma D_82e8c : decode_any W_82e8c = Some (Branch BC_LTU 6 18 5736, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e90 : bv 32 := 0x00133313.
Lemma F_82e90 : fetch_word Ubsan.M.loaded_segments (0x82e90 : word) = Some W_82e90.
Proof. vm_refl. Qed.
Lemma D_82e90 : decode_any W_82e90 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e94 : bv 32 := 0x00684333.
Lemma F_82e94 : fetch_word Ubsan.M.loaded_segments (0x82e94 : word) = Some W_82e94.
Proof. vm_refl. Qed.
Lemma D_82e94 : decode_any W_82e94 = Some (Op ALU_XOR 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e98 : bv 32 := 0xe4030e63.
Lemma F_82e98 : fetch_word Ubsan.M.loaded_segments (0x82e98 : word) = Some W_82e98.
Proof. vm_refl. Qed.
Lemma D_82e98 : decode_any W_82e98 = Some (Branch BC_EQ 6 0 5724, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e9c : bv 32 := 0xe40b8c63.
Lemma F_82e9c : fetch_word Ubsan.M.loaded_segments (0x82e9c : word) = Some W_82e9c.
Proof. vm_refl. Qed.
Lemma D_82e9c : decode_any W_82e9c = Some (Branch BC_EQ 23 0 5720, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ea0 : bv 32 := 0x00fb0333.
Lemma F_82ea0 : fetch_word Ubsan.M.loaded_segments (0x82ea0 : word) = Some W_82ea0.
Proof. vm_refl. Qed.
Lemma D_82ea0 : decode_any W_82ea0 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ea4 : bv 32 := 0xe4836863.
Lemma F_82ea4 : fetch_word Ubsan.M.loaded_segments (0x82ea4 : word) = Some W_82ea4.
Proof. vm_refl. Qed.
Lemma D_82ea4 : decode_any W_82ea4 = Some (Branch BC_LTU 6 8 5712, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ea8 : bv 32 := 0x00133313.
Lemma F_82ea8 : fetch_word Ubsan.M.loaded_segments (0x82ea8 : word) = Some W_82ea8.
Proof. vm_refl. Qed.
Lemma D_82ea8 : decode_any W_82ea8 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82eac : bv 32 := 0x006e4333.
Lemma F_82eac : fetch_word Ubsan.M.loaded_segments (0x82eac : word) = Some W_82eac.
Proof. vm_refl. Qed.
Lemma D_82eac : decode_any W_82eac = Some (Op ALU_XOR 6 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82eb0 : bv 32 := 0xe4030263.
Lemma F_82eb0 : fetch_word Ubsan.M.loaded_segments (0x82eb0 : word) = Some W_82eb0.
Proof. vm_refl. Qed.
Lemma D_82eb0 : decode_any W_82eb0 = Some (Branch BC_EQ 6 0 5700, 4%Z).
Proof. vm_refl. Qed.

Definition W_82eb4 : bv 32 := 0xe40c0063.
Lemma F_82eb4 : fetch_word Ubsan.M.loaded_segments (0x82eb4 : word) = Some W_82eb4.
Proof. vm_refl. Qed.
Lemma D_82eb4 : decode_any W_82eb4 = Some (Branch BC_EQ 24 0 5696, 4%Z).
Proof. vm_refl. Qed.

Definition W_82eb8 : bv 32 := 0x00f90333.
Lemma F_82eb8 : fetch_word Ubsan.M.loaded_segments (0x82eb8 : word) = Some W_82eb8.
Proof. vm_refl. Qed.
Lemma D_82eb8 : decode_any W_82eb8 = Some (Op ALU_ADD 6 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ebc : bv 32 := 0x00f40cb3.
Lemma F_82ebc : fetch_word Ubsan.M.loaded_segments (0x82ebc : word) = Some W_82ebc.
Proof. vm_refl. Qed.
Lemma D_82ebc : decode_any W_82ebc = Some (Op ALU_ADD 25 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ec0 : bv 32 := 0x00032303.
Lemma F_82ec0 : fetch_word Ubsan.M.loaded_segments (0x82ec0 : word) = Some W_82ec0.
Proof. vm_refl. Qed.
Lemma D_82ec0 : decode_any W_82ec0 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ec4 : bv 32 := 0x000cad03.
Lemma F_82ec4 : fetch_word Ubsan.M.loaded_segments (0x82ec4 : word) = Some W_82ec4.
Proof. vm_refl. Qed.
Lemma D_82ec4 : decode_any W_82ec4 = Some (Load SZ4 true 26 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ec8 : bv 32 := 0x006d6333.
Lemma F_82ec8 : fetch_word Ubsan.M.loaded_segments (0x82ec8 : word) = Some W_82ec8.
Proof. vm_refl. Qed.
Lemma D_82ec8 : decode_any W_82ec8 = Some (Op ALU_OR 6 26 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ecc : bv 32 := 0x00478793.
Lemma F_82ecc : fetch_word Ubsan.M.loaded_segments (0x82ecc : word) = Some W_82ecc.
Proof. vm_refl. Qed.
Lemma D_82ecc : decode_any W_82ecc = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ed0 : bv 32 := 0x006ca023.
Lemma F_82ed0 : fetch_word Ubsan.M.loaded_segments (0x82ed0 : word) = Some W_82ed0.
Proof. vm_refl. Qed.
Lemma D_82ed0 : decode_any W_82ed0 = Some (Store SZ4 25 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ed4 : bv 32 := 0xfaf89ae3.
Lemma F_82ed4 : fetch_word Ubsan.M.loaded_segments (0x82ed4 : word) = Some W_82ed4.
Proof. vm_refl. Qed.
Lemma D_82ed4 : decode_any W_82ed4 = Some (Branch BC_NE 17 15 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ed8 : bv 32 := 0x00c407b3.
Lemma F_82ed8 : fetch_word Ubsan.M.loaded_segments (0x82ed8 : word) = Some W_82ed8.
Proof. vm_refl. Qed.
Lemma D_82ed8 : decode_any W_82ed8 = Some (Op ALU_ADD 15 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82edc : bv 32 := 0x00803833.
Lemma F_82edc : fetch_word Ubsan.M.loaded_segments (0x82edc : word) = Some W_82edc.
Proof. vm_refl. Qed.
Lemma D_82edc : decode_any W_82edc = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ee0 : bv 32 := 0x0017b313.
Lemma F_82ee0 : fetch_word Ubsan.M.loaded_segments (0x82ee0 : word) = Some W_82ee0.
Proof. vm_refl. Qed.
Lemma D_82ee0 : decode_any W_82ee0 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ee4 : bv 32 := 0xe0680863.
Lemma F_82ee4 : fetch_word Ubsan.M.loaded_segments (0x82ee4 : word) = Some W_82ee4.
Proof. vm_refl. Qed.
Lemma D_82ee4 : decode_any W_82ee4 = Some (Branch BC_EQ 16 6 5648, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ee8 : bv 32 := 0x0087b7b3.
Lemma F_82ee8 : fetch_word Ubsan.M.loaded_segments (0x82ee8 : word) = Some W_82ee8.
Proof. vm_refl. Qed.
Lemma D_82ee8 : decode_any W_82ee8 = Some (Op ALU_SLTU 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82eec : bv 32 := 0x0057c7b3.
Lemma F_82eec : fetch_word Ubsan.M.loaded_segments (0x82eec : word) = Some W_82eec.
Proof. vm_refl. Qed.
Lemma D_82eec : decode_any W_82eec = Some (Op ALU_XOR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ef0 : bv 32 := 0x0017c793.
Lemma F_82ef0 : fetch_word Ubsan.M.loaded_segments (0x82ef0 : word) = Some W_82ef0.
Proof. vm_refl. Qed.
Lemma D_82ef0 : decode_any W_82ef0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ef4 : bv 32 := 0xe0078063.
Lemma F_82ef4 : fetch_word Ubsan.M.loaded_segments (0x82ef4 : word) = Some W_82ef4.
Proof. vm_refl. Qed.
Lemma D_82ef4 : decode_any W_82ef4 = Some (Branch BC_EQ 15 0 5632, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ef8 : bv 32 := 0x012687b3.
Lemma F_82ef8 : fetch_word Ubsan.M.loaded_segments (0x82ef8 : word) = Some W_82ef8.
Proof. vm_refl. Qed.
Lemma D_82ef8 : decode_any W_82ef8 = Some (Op ALU_ADD 15 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82efc : bv 32 := 0x01203833.
Lemma F_82efc : fetch_word Ubsan.M.loaded_segments (0x82efc : word) = Some W_82efc.
Proof. vm_refl. Qed.
Lemma D_82efc : decode_any W_82efc = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f00 : bv 32 := 0x0017b313.
Lemma F_82f00 : fetch_word Ubsan.M.loaded_segments (0x82f00 : word) = Some W_82f00.
Proof. vm_refl. Qed.
Lemma D_82f00 : decode_any W_82f00 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f04 : bv 32 := 0xde680863.
Lemma F_82f04 : fetch_word Ubsan.M.loaded_segments (0x82f04 : word) = Some W_82f04.
Proof. vm_refl. Qed.
Lemma D_82f04 : decode_any W_82f04 = Some (Branch BC_EQ 16 6 5616, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f08 : bv 32 := 0x0127b833.
Lemma F_82f08 : fetch_word Ubsan.M.loaded_segments (0x82f08 : word) = Some W_82f08.
Proof. vm_refl. Qed.
Lemma D_82f08 : decode_any W_82f08 = Some (Op ALU_SLTU 16 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f0c : bv 32 := 0x00784833.
Lemma F_82f0c : fetch_word Ubsan.M.loaded_segments (0x82f0c : word) = Some W_82f0c.
Proof. vm_refl. Qed.
Lemma D_82f0c : decode_any W_82f0c = Some (Op ALU_XOR 16 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f10 : bv 32 := 0x00184813.
Lemma F_82f10 : fetch_word Ubsan.M.loaded_segments (0x82f10 : word) = Some W_82f10.
Proof. vm_refl. Qed.
Lemma D_82f10 : decode_any W_82f10 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f14 : bv 32 := 0xde080063.
Lemma F_82f14 : fetch_word Ubsan.M.loaded_segments (0x82f14 : word) = Some W_82f14.
Proof. vm_refl. Qed.
Lemma D_82f14 : decode_any W_82f14 = Some (Branch BC_EQ 16 0 5600, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f18 : bv 32 := 0x00c40433.
Lemma F_82f18 : fetch_word Ubsan.M.loaded_segments (0x82f18 : word) = Some W_82f18.
Proof. vm_refl. Qed.
Lemma D_82f18 : decode_any W_82f18 = Some (Op ALU_ADD 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f1c : bv 32 := 0x0015859b.
Lemma F_82f1c : fetch_word Ubsan.M.loaded_segments (0x82f1c : word) = Some W_82f1c.
Proof. vm_refl. Qed.
Lemma D_82f1c : decode_any W_82f1c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f20 : bv 32 := 0x00cb0b33.
Lemma F_82f20 : fetch_word Ubsan.M.loaded_segments (0x82f20 : word) = Some W_82f20.
Proof. vm_refl. Qed.
Lemma D_82f20 : decode_any W_82f20 = Some (Op ALU_ADD 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f24 : bv 32 := 0x00da8ab3.
Lemma F_82f24 : fetch_word Ubsan.M.loaded_segments (0x82f24 : word) = Some W_82f24.
Proof. vm_refl. Qed.
Lemma D_82f24 : decode_any W_82f24 = Some (Op ALU_ADD 21 21 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f28 : bv 32 := 0x00078913.
Lemma F_82f28 : fetch_word Ubsan.M.loaded_segments (0x82f28 : word) = Some W_82f28.
Proof. vm_refl. Qed.
Lemma D_82f28 : decode_any W_82f28 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f2c : bv 32 := 0x08013783.
Lemma F_82f2c : fetch_word Ubsan.M.loaded_segments (0x82f2c : word) = Some W_82f2c.
Proof. vm_refl. Qed.
Lemma D_82f2c : decode_any W_82f2c = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f30 : bv 32 := 0xf4f590e3.
Lemma F_82f30 : fetch_word Ubsan.M.loaded_segments (0x82f30 : word) = Some W_82f30.
Proof. vm_refl. Qed.
Lemma D_82f30 : decode_any W_82f30 = Some (Branch BC_NE 11 15 8000, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f34 : bv 32 := 0x00048463.
Lemma F_82f34 : fetch_word Ubsan.M.loaded_segments (0x82f34 : word) = Some W_82f34.
Proof. vm_refl. Qed.
Lemma D_82f34 : decode_any W_82f34 = Some (Branch BC_EQ 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f38 : bv 32 := 0x6800406f.
Lemma F_82f38 : fetch_word Ubsan.M.loaded_segments (0x82f38 : word) = Some W_82f38.
Proof. vm_refl. Qed.
Lemma D_82f38 : decode_any W_82f38 = Some (Jal 0 18048, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f3c : bv 32 := 0x00357593.
Lemma F_82f3c : fetch_word Ubsan.M.loaded_segments (0x82f3c : word) = Some W_82f3c.
Proof. vm_refl. Qed.
Lemma D_82f3c : decode_any W_82f3c = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f40 : bv 32 := 0xda059a63.
Lemma F_82f40 : fetch_word Ubsan.M.loaded_segments (0x82f40 : word) = Some W_82f40.
Proof. vm_refl. Qed.
Lemma D_82f40 : decode_any W_82f40 = Some (Branch BC_NE 11 0 5556, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f44 : bv 32 := 0xfffec613.
Lemma F_82f44 : fetch_word Ubsan.M.loaded_segments (0x82f44 : word) = Some W_82f44.
Proof. vm_refl. Qed.
Lemma D_82f44 : decode_any W_82f44 = Some (OpImm ALU_XOR 12 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f48 : bv 32 := 0x00271693.
Lemma F_82f48 : fetch_word Ubsan.M.loaded_segments (0x82f48 : word) = Some W_82f48.
Proof. vm_refl. Qed.
Lemma D_82f48 : decode_any W_82f48 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f4c : bv 32 := 0x05813e03.
Lemma F_82f4c : fetch_word Ubsan.M.loaded_segments (0x82f4c : word) = Some W_82f4c.
Proof. vm_refl. Qed.
Lemma D_82f4c : decode_any W_82f4c = Some (Load SZ8 true 28 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f50 : bv 32 := 0x002e1793.
Lemma F_82f50 : fetch_word Ubsan.M.loaded_segments (0x82f50 : word) = Some W_82f50.
Proof. vm_refl. Qed.
Lemma D_82f50 : decode_any W_82f50 = Some (ShiftImm ALU_SLL 15 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f54 : bv 32 := 0x03813883.
Lemma F_82f54 : fetch_word Ubsan.M.loaded_segments (0x82f54 : word) = Some W_82f54.
Proof. vm_refl. Qed.
Lemma D_82f54 : decode_any W_82f54 = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f58 : bv 32 := 0x03013803.
Lemma F_82f58 : fetch_word Ubsan.M.loaded_segments (0x82f58 : word) = Some W_82f58.
Proof. vm_refl. Qed.
Lemma D_82f58 : decode_any W_82f58 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f5c : bv 32 := 0x011808b3.
Lemma F_82f5c : fetch_word Ubsan.M.loaded_segments (0x82f5c : word) = Some W_82f5c.
Proof. vm_refl. Qed.
Lemma D_82f5c : decode_any W_82f5c = Some (Op ALU_ADD 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f60 : bv 32 := 0x04813283.
Lemma F_82f60 : fetch_word Ubsan.M.loaded_segments (0x82f60 : word) = Some W_82f60.
Proof. vm_refl. Qed.
Lemma D_82f60 : decode_any W_82f60 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f64 : bv 32 := 0x43f2d813.
Lemma F_82f64 : fetch_word Ubsan.M.loaded_segments (0x82f64 : word) = Some W_82f64.
Proof. vm_refl. Qed.
Lemma D_82f64 : decode_any W_82f64 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f68 : bv 32 := 0x005872b3.
Lemma F_82f68 : fetch_word Ubsan.M.loaded_segments (0x82f68 : word) = Some W_82f68.
Proof. vm_refl. Qed.
Lemma D_82f68 : decode_any W_82f68 = Some (Op ALU_AND 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f6c : bv 32 := 0x003f7813.
Lemma F_82f6c : fetch_word Ubsan.M.loaded_segments (0x82f6c : word) = Some W_82f6c.
Proof. vm_refl. Qed.
Lemma D_82f6c : decode_any W_82f6c = Some (OpImm ALU_AND 16 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f70 : bv 32 := 0x05013383.
Lemma F_82f70 : fetch_word Ubsan.M.loaded_segments (0x82f70 : word) = Some W_82f70.
Proof. vm_refl. Qed.
Lemma D_82f70 : decode_any W_82f70 = Some (Load SZ8 true 7 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f74 : bv 32 := 0x02813303.
Lemma F_82f74 : fetch_word Ubsan.M.loaded_segments (0x82f74 : word) = Some W_82f74.
Proof. vm_refl. Qed.
Lemma D_82f74 : decode_any W_82f74 = Some (Load SZ8 true 6 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f78 : bv 32 := 0x4073033b.
Lemma F_82f78 : fetch_word Ubsan.M.loaded_segments (0x82f78 : word) = Some W_82f78.
Proof. vm_refl. Qed.
Lemma D_82f78 : decode_any W_82f78 = Some (Op32 ALU_SUB 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f7c : bv 32 := 0x00072713.
Lemma F_82f7c : fetch_word Ubsan.M.loaded_segments (0x82f7c : word) = Some W_82f7c.
Proof. vm_refl. Qed.
Lemma D_82f7c : decode_any W_82f7c = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f80 : bv 32 := 0x005882b3.
Lemma F_82f80 : fetch_word Ubsan.M.loaded_segments (0x82f80 : word) = Some W_82f80.
Proof. vm_refl. Qed.
Lemma D_82f80 : decode_any W_82f80 = Some (Op ALU_ADD 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f84 : bv 32 := 0x00ff08b3.
Lemma F_82f84 : fetch_word Ubsan.M.loaded_segments (0x82f84 : word) = Some W_82f84.
Proof. vm_refl. Qed.
Lemma D_82f84 : decode_any W_82f84 = Some (Op ALU_ADD 17 30 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f88 : bv 32 := 0x407282bb.
Lemma F_82f88 : fetch_word Ubsan.M.loaded_segments (0x82f88 : word) = Some W_82f88.
Proof. vm_refl. Qed.
Lemma D_82f88 : decode_any W_82f88 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f8c : bv 32 := 0x04013383.
Lemma F_82f8c : fetch_word Ubsan.M.loaded_segments (0x82f8c : word) = Some W_82f8c.
Proof. vm_refl. Qed.
Lemma D_82f8c : decode_any W_82f8c = Some (Load SZ8 true 7 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f90 : bv 32 := 0x407282bb.
Lemma F_82f90 : fetch_word Ubsan.M.loaded_segments (0x82f90 : word) = Some W_82f90.
Proof. vm_refl. Qed.
Lemma D_82f90 : decode_any W_82f90 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f94 : bv 32 := 0x43f2d393.
Lemma F_82f94 : fetch_word Ubsan.M.loaded_segments (0x82f94 : word) = Some W_82f94.
Proof. vm_refl. Qed.
Lemma D_82f94 : decode_any W_82f94 = Some (ShiftImm ALU_SRA 7 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f98 : bv 32 := 0x0053f2b3.
Lemma F_82f98 : fetch_word Ubsan.M.loaded_segments (0x82f98 : word) = Some W_82f98.
Proof. vm_refl. Qed.
Lemma D_82f98 : decode_any W_82f98 = Some (Op ALU_AND 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f9c : bv 32 := 0x405302bb.
Lemma F_82f9c : fetch_word Ubsan.M.loaded_segments (0x82f9c : word) = Some W_82f9c.
Proof. vm_refl. Qed.
Lemma D_82f9c : decode_any W_82f9c = Some (Op32 ALU_SUB 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fa0 : bv 32 := 0x000e2313.
Lemma F_82fa0 : fetch_word Ubsan.M.loaded_segments (0x82fa0 : word) = Some W_82fa0.
Proof. vm_refl. Qed.
Lemma D_82fa0 : decode_any W_82fa0 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fa4 : bv 32 := 0x00050393.
Lemma F_82fa4 : fetch_word Ubsan.M.loaded_segments (0x82fa4 : word) = Some W_82fa4.
Proof. vm_refl. Qed.
Lemma D_82fa4 : decode_any W_82fa4 = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fa8 : bv 32 := 0xd4050663.
Lemma F_82fa8 : fetch_word Ubsan.M.loaded_segments (0x82fa8 : word) = Some W_82fa8.
Proof. vm_refl. Qed.
Lemma D_82fa8 : decode_any W_82fa8 = Some (Branch BC_EQ 10 0 5452, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fac : bv 32 := 0xd4081463.
Lemma F_82fac : fetch_word Ubsan.M.loaded_segments (0x82fac : word) = Some W_82fac.
Proof. vm_refl. Qed.
Lemma D_82fac : decode_any W_82fac = Some (Branch BC_NE 16 0 5448, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fb0 : bv 32 := 0x00bf0e33.
Lemma F_82fb0 : fetch_word Ubsan.M.loaded_segments (0x82fb0 : word) = Some W_82fb0.
Proof. vm_refl. Qed.
Lemma D_82fb0 : decode_any W_82fb0 = Some (Op ALU_ADD 28 30 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fb4 : bv 32 := 0xd40e0063.
Lemma F_82fb4 : fetch_word Ubsan.M.loaded_segments (0x82fb4 : word) = Some W_82fb4.
Proof. vm_refl. Qed.
Lemma D_82fb4 : decode_any W_82fb4 = Some (Branch BC_EQ 28 0 5440, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fb8 : bv 32 := 0x00052f83.
Lemma F_82fb8 : fetch_word Ubsan.M.loaded_segments (0x82fb8 : word) = Some W_82fb8.
Proof. vm_refl. Qed.
Lemma D_82fb8 : decode_any W_82fb8 = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fbc : bv 32 := 0x000e2403.
Lemma F_82fbc : fetch_word Ubsan.M.loaded_segments (0x82fbc : word) = Some W_82fbc.
Proof. vm_refl. Qed.
Lemma D_82fbc : decode_any W_82fbc = Some (Load SZ4 true 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fc0 : bv 32 := 0x00cff4b3.
Lemma F_82fc0 : fetch_word Ubsan.M.loaded_segments (0x82fc0 : word) = Some W_82fc0.
Proof. vm_refl. Qed.
Lemma D_82fc0 : decode_any W_82fc0 = Some (Op ALU_AND 9 31 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fc4 : bv 32 := 0x01f46fb3.
Lemma F_82fc4 : fetch_word Ubsan.M.loaded_segments (0x82fc4 : word) = Some W_82fc4.
Proof. vm_refl. Qed.
Lemma D_82fc4 : decode_any W_82fc4 = Some (Op ALU_OR 31 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fc8 : bv 32 := 0x01dfffb3.
Lemma F_82fc8 : fetch_word Ubsan.M.loaded_segments (0x82fc8 : word) = Some W_82fc8.
Proof. vm_refl. Qed.
Lemma D_82fc8 : decode_any W_82fc8 = Some (Op ALU_AND 31 31 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fcc : bv 32 := 0x009fe433.
Lemma F_82fcc : fetch_word Ubsan.M.loaded_segments (0x82fcc : word) = Some W_82fcc.
Proof. vm_refl. Qed.
Lemma D_82fcc : decode_any W_82fcc = Some (Op ALU_OR 8 31 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fd0 : bv 32 := 0x00768fb3.
Lemma F_82fd0 : fetch_word Ubsan.M.loaded_segments (0x82fd0 : word) = Some W_82fd0.
Proof. vm_refl. Qed.
Lemma D_82fd0 : decode_any W_82fd0 = Some (Op ALU_ADD 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fd4 : bv 32 := 0x00852023.
Lemma F_82fd4 : fetch_word Ubsan.M.loaded_segments (0x82fd4 : word) = Some W_82fd4.
Proof. vm_refl. Qed.
Lemma D_82fd4 : decode_any W_82fd4 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fd8 : bv 32 := 0xd00f8e63.
Lemma F_82fd8 : fetch_word Ubsan.M.loaded_segments (0x82fd8 : word) = Some W_82fd8.
Proof. vm_refl. Qed.
Lemma D_82fd8 : decode_any W_82fd8 = Some (Branch BC_EQ 31 0 5404, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fdc : bv 32 := 0x007fb3b3.
Lemma F_82fdc : fetch_word Ubsan.M.loaded_segments (0x82fdc : word) = Some W_82fdc.
Proof. vm_refl. Qed.
Lemma D_82fdc : decode_any W_82fdc = Some (Op ALU_SLTU 7 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fe0 : bv 32 := 0x00e3c3b3.
Lemma F_82fe0 : fetch_word Ubsan.M.loaded_segments (0x82fe0 : word) = Some W_82fe0.
Proof. vm_refl. Qed.
Lemma D_82fe0 : decode_any W_82fe0 = Some (Op ALU_XOR 7 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fe4 : bv 32 := 0x0013c393.
Lemma F_82fe4 : fetch_word Ubsan.M.loaded_segments (0x82fe4 : word) = Some W_82fe4.
Proof. vm_refl. Qed.
Lemma D_82fe4 : decode_any W_82fe4 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fe8 : bv 32 := 0xd0038663.
Lemma F_82fe8 : fetch_word Ubsan.M.loaded_segments (0x82fe8 : word) = Some W_82fe8.
Proof. vm_refl. Qed.
Lemma D_82fe8 : decode_any W_82fe8 = Some (Branch BC_EQ 7 0 5388, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fec : bv 32 := 0x00b883b3.
Lemma F_82fec : fetch_word Ubsan.M.loaded_segments (0x82fec : word) = Some W_82fec.
Proof. vm_refl. Qed.
Lemma D_82fec : decode_any W_82fec = Some (Op ALU_ADD 7 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ff0 : bv 32 := 0xd0038263.
Lemma F_82ff0 : fetch_word Ubsan.M.loaded_segments (0x82ff0 : word) = Some W_82ff0.
Proof. vm_refl. Qed.
Lemma D_82ff0 : decode_any W_82ff0 = Some (Branch BC_EQ 7 0 5380, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ff4 : bv 32 := 0x01c3b3b3.
Lemma F_82ff4 : fetch_word Ubsan.M.loaded_segments (0x82ff4 : word) = Some W_82ff4.
Proof. vm_refl. Qed.
Lemma D_82ff4 : decode_any W_82ff4 = Some (Op ALU_SLTU 7 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ff8 : bv 32 := 0x0063c3b3.
Lemma F_82ff8 : fetch_word Ubsan.M.loaded_segments (0x82ff8 : word) = Some W_82ff8.
Proof. vm_refl. Qed.
Lemma D_82ff8 : decode_any W_82ff8 = Some (Op ALU_XOR 7 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ffc : bv 32 := 0x0013c393.
Lemma F_82ffc : fetch_word Ubsan.M.loaded_segments (0x82ffc : word) = Some W_82ffc.
Proof. vm_refl. Qed.
Lemma D_82ffc : decode_any W_82ffc = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.
