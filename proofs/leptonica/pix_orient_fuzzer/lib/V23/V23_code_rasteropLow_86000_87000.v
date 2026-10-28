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

Definition W_86000 : bv 32 := 0x011e08b3.
Lemma F_86000 : fetch_word Ubsan.M.loaded_segments (0x86000 : word) = Some W_86000.
Proof. vm_refl. Qed.
Lemma D_86000 : decode_any W_86000 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86004 : bv 32 := 0x04813a03.
Lemma F_86004 : fetch_word Ubsan.M.loaded_segments (0x86004 : word) = Some W_86004.
Proof. vm_refl. Qed.
Lemma D_86004 : decode_any W_86004 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_86008 : bv 32 := 0x43fa5e13.
Lemma F_86008 : fetch_word Ubsan.M.loaded_segments (0x86008 : word) = Some W_86008.
Proof. vm_refl. Qed.
Lemma D_86008 : decode_any W_86008 = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_8600c : bv 32 := 0x01013983.
Lemma F_8600c : fetch_word Ubsan.M.loaded_segments (0x8600c : word) = Some W_8600c.
Proof. vm_refl. Qed.
Lemma D_8600c : decode_any W_8600c = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86010 : bv 32 := 0x0019f993.
Lemma F_86010 : fetch_word Ubsan.M.loaded_segments (0x86010 : word) = Some W_86010.
Proof. vm_refl. Qed.
Lemma D_86010 : decode_any W_86010 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86014 : bv 32 := 0x001d7c13.
Lemma F_86014 : fetch_word Ubsan.M.loaded_segments (0x86014 : word) = Some W_86014.
Proof. vm_refl. Qed.
Lemma D_86014 : decode_any W_86014 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86018 : bv 32 := 0x01f00093.
Lemma F_86018 : fetch_word Ubsan.M.loaded_segments (0x86018 : word) = Some W_86018.
Proof. vm_refl. Qed.
Lemma D_86018 : decode_any W_86018 = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_8601c : bv 32 := 0x014e7e33.
Lemma F_8601c : fetch_word Ubsan.M.loaded_segments (0x8601c : word) = Some W_8601c.
Proof. vm_refl. Qed.
Lemma D_8601c : decode_any W_8601c = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86020 : bv 32 := 0x409888bb.
Lemma F_86020 : fetch_word Ubsan.M.loaded_segments (0x86020 : word) = Some W_86020.
Proof. vm_refl. Qed.
Lemma D_86020 : decode_any W_86020 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86024 : bv 32 := 0x00d78a33.
Lemma F_86024 : fetch_word Ubsan.M.loaded_segments (0x86024 : word) = Some W_86024.
Proof. vm_refl. Qed.
Lemma D_86024 : decode_any W_86024 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86028 : bv 32 := 0x00163b13.
Lemma F_86028 : fetch_word Ubsan.M.loaded_segments (0x86028 : word) = Some W_86028.
Proof. vm_refl. Qed.
Lemma D_86028 : decode_any W_86028 = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8602c : bv 32 := 0x04013603.
Lemma F_8602c : fetch_word Ubsan.M.loaded_segments (0x8602c : word) = Some W_8602c.
Proof. vm_refl. Qed.
Lemma D_8602c : decode_any W_8602c = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86030 : bv 32 := 0x40c8863b.
Lemma F_86030 : fetch_word Ubsan.M.loaded_segments (0x86030 : word) = Some W_86030.
Proof. vm_refl. Qed.
Lemma D_86030 : decode_any W_86030 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86034 : bv 32 := 0x01c6063b.
Lemma F_86034 : fetch_word Ubsan.M.loaded_segments (0x86034 : word) = Some W_86034.
Proof. vm_refl. Qed.
Lemma D_86034 : decode_any W_86034 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86038 : bv 32 := 0x43f65893.
Lemma F_86038 : fetch_word Ubsan.M.loaded_segments (0x86038 : word) = Some W_86038.
Proof. vm_refl. Qed.
Lemma D_86038 : decode_any W_86038 = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_8603c : bv 32 := 0x00c8f633.
Lemma F_8603c : fetch_word Ubsan.M.loaded_segments (0x8603c : word) = Some W_8603c.
Proof. vm_refl. Qed.
Lemma D_8603c : decode_any W_8603c = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86040 : bv 32 := 0x40c80e3b.
Lemma F_86040 : fetch_word Ubsan.M.loaded_segments (0x86040 : word) = Some W_86040.
Proof. vm_refl. Qed.
Lemma D_86040 : decode_any W_86040 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86044 : bv 32 := 0x00072493.
Lemma F_86044 : fetch_word Ubsan.M.loaded_segments (0x86044 : word) = Some W_86044.
Proof. vm_refl. Qed.
Lemma D_86044 : decode_any W_86044 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86048 : bv 32 := 0x000c8813.
Lemma F_86048 : fetch_word Ubsan.M.loaded_segments (0x86048 : word) = Some W_86048.
Proof. vm_refl. Qed.
Lemma D_86048 : decode_any W_86048 = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8604c : bv 32 := 0x00b78d33.
Lemma F_8604c : fetch_word Ubsan.M.loaded_segments (0x8604c : word) = Some W_8604c.
Proof. vm_refl. Qed.
Lemma D_8604c : decode_any W_8604c = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86050 : bv 32 := 0x01a03633.
Lemma F_86050 : fetch_word Ubsan.M.loaded_segments (0x86050 : word) = Some W_86050.
Proof. vm_refl. Qed.
Lemma D_86050 : decode_any W_86050 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86054 : bv 32 := 0x00cb7633.
Lemma F_86054 : fetch_word Ubsan.M.loaded_segments (0x86054 : word) = Some W_86054.
Proof. vm_refl. Qed.
Lemma D_86054 : decode_any W_86054 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86058 : bv 32 := 0x04098a63.
Lemma F_86058 : fetch_word Ubsan.M.loaded_segments (0x86058 : word) = Some W_86058.
Proof. vm_refl. Qed.
Lemma D_86058 : decode_any W_86058 = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_8605c : bv 32 := 0x00061463.
Lemma F_8605c : fetch_word Ubsan.M.loaded_segments (0x8605c : word) = Some W_8605c.
Proof. vm_refl. Qed.
Lemma D_8605c : decode_any W_8605c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86060 : bv 32 := 0xc94fc06f.
Lemma F_86060 : fetch_word Ubsan.M.loaded_segments (0x86060 : word) = Some W_86060.
Proof. vm_refl. Qed.
Lemma D_86060 : decode_any W_86060 = Some (Jal 0 2081940, 4%Z).
Proof. vm_refl. Qed.

Definition W_86064 : bv 32 := 0x02000613.
Lemma F_86064 : fetch_word Ubsan.M.loaded_segments (0x86064 : word) = Some W_86064.
Proof. vm_refl. Qed.
Lemma D_86064 : decode_any W_86064 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86068 : bv 32 := 0x00cf1463.
Lemma F_86068 : fetch_word Ubsan.M.loaded_segments (0x86068 : word) = Some W_86068.
Proof. vm_refl. Qed.
Lemma D_86068 : decode_any W_86068 = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8606c : bv 32 := 0xc88fc06f.
Lemma F_8606c : fetch_word Ubsan.M.loaded_segments (0x8606c : word) = Some W_8606c.
Proof. vm_refl. Qed.
Lemma D_8606c : decode_any W_8606c = Some (Jal 0 2081928, 4%Z).
Proof. vm_refl. Qed.

Definition W_86070 : bv 32 := 0x000d2603.
Lemma F_86070 : fetch_word Ubsan.M.loaded_segments (0x86070 : word) = Some W_86070.
Proof. vm_refl. Qed.
Lemma D_86070 : decode_any W_86070 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86074 : bv 32 := 0x01d61abb.
Lemma F_86074 : fetch_word Ubsan.M.loaded_segments (0x86074 : word) = Some W_86074.
Proof. vm_refl. Qed.
Lemma D_86074 : decode_any W_86074 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86078 : bv 32 := 0x040c1663.
Lemma F_86078 : fetch_word Ubsan.M.loaded_segments (0x86078 : word) = Some W_86078.
Proof. vm_refl. Qed.
Lemma D_86078 : decode_any W_86078 = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_8607c : bv 32 := 0xffb00613.
Lemma F_8607c : fetch_word Ubsan.M.loaded_segments (0x8607c : word) = Some W_8607c.
Proof. vm_refl. Qed.
Lemma D_8607c : decode_any W_8607c = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_86080 : bv 32 := 0x01a67463.
Lemma F_86080 : fetch_word Ubsan.M.loaded_segments (0x86080 : word) = Some W_86080.
Proof. vm_refl. Qed.
Lemma D_86080 : decode_any W_86080 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86084 : bv 32 := 0xc70fc06f.
Lemma F_86084 : fetch_word Ubsan.M.loaded_segments (0x86084 : word) = Some W_86084.
Proof. vm_refl. Qed.
Lemma D_86084 : decode_any W_86084 = Some (Jal 0 2081904, 4%Z).
Proof. vm_refl. Qed.

Definition W_86088 : bv 32 := 0x0080f463.
Lemma F_86088 : fetch_word Ubsan.M.loaded_segments (0x86088 : word) = Some W_86088.
Proof. vm_refl. Qed.
Lemma D_86088 : decode_any W_86088 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8608c : bv 32 := 0xc68fc06f.
Lemma F_8608c : fetch_word Ubsan.M.loaded_segments (0x8608c : word) = Some W_8608c.
Proof. vm_refl. Qed.
Lemma D_8608c : decode_any W_8608c = Some (Jal 0 2081896, 4%Z).
Proof. vm_refl. Qed.

Definition W_86090 : bv 32 := 0x004d2603.
Lemma F_86090 : fetch_word Ubsan.M.loaded_segments (0x86090 : word) = Some W_86090.
Proof. vm_refl. Qed.
Lemma D_86090 : decode_any W_86090 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86094 : bv 32 := 0x00013883.
Lemma F_86094 : fetch_word Ubsan.M.loaded_segments (0x86094 : word) = Some W_86094.
Proof. vm_refl. Qed.
Lemma D_86094 : decode_any W_86094 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86098 : bv 32 := 0x011af8b3.
Lemma F_86098 : fetch_word Ubsan.M.loaded_segments (0x86098 : word) = Some W_86098.
Proof. vm_refl. Qed.
Lemma D_86098 : decode_any W_86098 = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8609c : bv 32 := 0x0086563b.
Lemma F_8609c : fetch_word Ubsan.M.loaded_segments (0x8609c : word) = Some W_8609c.
Proof. vm_refl. Qed.
Lemma D_8609c : decode_any W_8609c = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860a0 : bv 32 := 0x01f67633.
Lemma F_860a0 : fetch_word Ubsan.M.loaded_segments (0x860a0 : word) = Some W_860a0.
Proof. vm_refl. Qed.
Lemma D_860a0 : decode_any W_860a0 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_860a4 : bv 32 := 0x01166ab3.
Lemma F_860a4 : fetch_word Ubsan.M.loaded_segments (0x860a4 : word) = Some W_860a4.
Proof. vm_refl. Qed.
Lemma D_860a4 : decode_any W_860a4 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_860a8 : bv 32 := 0x01c0006f.
Lemma F_860a8 : fetch_word Ubsan.M.loaded_segments (0x860a8 : word) = Some W_860a8.
Proof. vm_refl. Qed.
Lemma D_860a8 : decode_any W_860a8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_860ac : bv 32 := 0x00061463.
Lemma F_860ac : fetch_word Ubsan.M.loaded_segments (0x860ac : word) = Some W_860ac.
Proof. vm_refl. Qed.
Lemma D_860ac : decode_any W_860ac = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860b0 : bv 32 := 0xc44fc06f.
Lemma F_860b0 : fetch_word Ubsan.M.loaded_segments (0x860b0 : word) = Some W_860b0.
Proof. vm_refl. Qed.
Lemma D_860b0 : decode_any W_860b0 = Some (Jal 0 2081860, 4%Z).
Proof. vm_refl. Qed.

Definition W_860b4 : bv 32 := 0x0080f463.
Lemma F_860b4 : fetch_word Ubsan.M.loaded_segments (0x860b4 : word) = Some W_860b4.
Proof. vm_refl. Qed.
Lemma D_860b4 : decode_any W_860b4 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860b8 : bv 32 := 0xc3cfc06f.
Lemma F_860b8 : fetch_word Ubsan.M.loaded_segments (0x860b8 : word) = Some W_860b8.
Proof. vm_refl. Qed.
Lemma D_860b8 : decode_any W_860b8 = Some (Jal 0 2081852, 4%Z).
Proof. vm_refl. Qed.

Definition W_860bc : bv 32 := 0x000d2603.
Lemma F_860bc : fetch_word Ubsan.M.loaded_segments (0x860bc : word) = Some W_860bc.
Proof. vm_refl. Qed.
Lemma D_860bc : decode_any W_860bc = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_860c0 : bv 32 := 0x00865abb.
Lemma F_860c0 : fetch_word Ubsan.M.loaded_segments (0x860c0 : word) = Some W_860c0.
Proof. vm_refl. Qed.
Lemma D_860c0 : decode_any W_860c0 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860c4 : bv 32 := 0x000b8463.
Lemma F_860c4 : fetch_word Ubsan.M.loaded_segments (0x860c4 : word) = Some W_860c4.
Proof. vm_refl. Qed.
Lemma D_860c4 : decode_any W_860c4 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860c8 : bv 32 := 0xc2cfc06f.
Lemma F_860c8 : fetch_word Ubsan.M.loaded_segments (0x860c8 : word) = Some W_860c8.
Proof. vm_refl. Qed.
Lemma D_860c8 : decode_any W_860c8 = Some (Jal 0 2081836, 4%Z).
Proof. vm_refl. Qed.

Definition W_860cc : bv 32 := 0x000c9463.
Lemma F_860cc : fetch_word Ubsan.M.loaded_segments (0x860cc : word) = Some W_860cc.
Proof. vm_refl. Qed.
Lemma D_860cc : decode_any W_860cc = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860d0 : bv 32 := 0xc24fc06f.
Lemma F_860d0 : fetch_word Ubsan.M.loaded_segments (0x860d0 : word) = Some W_860d0.
Proof. vm_refl. Qed.
Lemma D_860d0 : decode_any W_860d0 = Some (Jal 0 2081828, 4%Z).
Proof. vm_refl. Qed.

Definition W_860d4 : bv 32 := 0x000ca603.
Lemma F_860d4 : fetch_word Ubsan.M.loaded_segments (0x860d4 : word) = Some W_860d4.
Proof. vm_refl. Qed.
Lemma D_860d4 : decode_any W_860d4 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_860d8 : bv 32 := 0x005678b3.
Lemma F_860d8 : fetch_word Ubsan.M.loaded_segments (0x860d8 : word) = Some W_860d8.
Proof. vm_refl. Qed.
Lemma D_860d8 : decode_any W_860d8 = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_860dc : bv 32 := 0x00cac633.
Lemma F_860dc : fetch_word Ubsan.M.loaded_segments (0x860dc : word) = Some W_860dc.
Proof. vm_refl. Qed.
Lemma D_860dc : decode_any W_860dc = Some (Op ALU_XOR 12 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_860e0 : bv 32 := 0xfff64613.
Lemma F_860e0 : fetch_word Ubsan.M.loaded_segments (0x860e0 : word) = Some W_860e0.
Proof. vm_refl. Qed.
Lemma D_860e0 : decode_any W_860e0 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_860e4 : bv 32 := 0x00cdf633.
Lemma F_860e4 : fetch_word Ubsan.M.loaded_segments (0x860e4 : word) = Some W_860e4.
Proof. vm_refl. Qed.
Lemma D_860e4 : decode_any W_860e4 = Some (Op ALU_AND 12 27 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_860e8 : bv 32 := 0x01166633.
Lemma F_860e8 : fetch_word Ubsan.M.loaded_segments (0x860e8 : word) = Some W_860e8.
Proof. vm_refl. Qed.
Lemma D_860e8 : decode_any W_860e8 = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_860ec : bv 32 := 0x01038ab3.
Lemma F_860ec : fetch_word Ubsan.M.loaded_segments (0x860ec : word) = Some W_860ec.
Proof. vm_refl. Qed.
Lemma D_860ec : decode_any W_860ec = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_860f0 : bv 32 := 0x00cca023.
Lemma F_860f0 : fetch_word Ubsan.M.loaded_segments (0x860f0 : word) = Some W_860f0.
Proof. vm_refl. Qed.
Lemma D_860f0 : decode_any W_860f0 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_860f4 : bv 32 := 0x000a9463.
Lemma F_860f4 : fetch_word Ubsan.M.loaded_segments (0x860f4 : word) = Some W_860f4.
Proof. vm_refl. Qed.
Lemma D_860f4 : decode_any W_860f4 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_860f8 : bv 32 := 0xbfcfc06f.
Lemma F_860f8 : fetch_word Ubsan.M.loaded_segments (0x860f8 : word) = Some W_860f8.
Proof. vm_refl. Qed.
Lemma D_860f8 : decode_any W_860f8 = Some (Jal 0 2081788, 4%Z).
Proof. vm_refl. Qed.

Definition W_860fc : bv 32 := 0x010ab633.
Lemma F_860fc : fetch_word Ubsan.M.loaded_segments (0x860fc : word) = Some W_860fc.
Proof. vm_refl. Qed.
Lemma D_860fc : decode_any W_860fc = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86100 : bv 32 := 0x00964633.
Lemma F_86100 : fetch_word Ubsan.M.loaded_segments (0x86100 : word) = Some W_86100.
Proof. vm_refl. Qed.
Lemma D_86100 : decode_any W_86100 = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86104 : bv 32 := 0x00164613.
Lemma F_86104 : fetch_word Ubsan.M.loaded_segments (0x86104 : word) = Some W_86104.
Proof. vm_refl. Qed.
Lemma D_86104 : decode_any W_86104 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86108 : bv 32 := 0x00061463.
Lemma F_86108 : fetch_word Ubsan.M.loaded_segments (0x86108 : word) = Some W_86108.
Proof. vm_refl. Qed.
Lemma D_86108 : decode_any W_86108 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8610c : bv 32 := 0xbe8fc06f.
Lemma F_8610c : fetch_word Ubsan.M.loaded_segments (0x8610c : word) = Some W_8610c.
Proof. vm_refl. Qed.
Lemma D_8610c : decode_any W_8610c = Some (Jal 0 2081768, 4%Z).
Proof. vm_refl. Qed.

Definition W_86110 : bv 32 := 0x00ba0633.
Lemma F_86110 : fetch_word Ubsan.M.loaded_segments (0x86110 : word) = Some W_86110.
Proof. vm_refl. Qed.
Lemma D_86110 : decode_any W_86110 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86114 : bv 32 := 0x00061463.
Lemma F_86114 : fetch_word Ubsan.M.loaded_segments (0x86114 : word) = Some W_86114.
Proof. vm_refl. Qed.
Lemma D_86114 : decode_any W_86114 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86118 : bv 32 := 0xbdcfc06f.
Lemma F_86118 : fetch_word Ubsan.M.loaded_segments (0x86118 : word) = Some W_86118.
Proof. vm_refl. Qed.
Lemma D_86118 : decode_any W_86118 = Some (Jal 0 2081756, 4%Z).
Proof. vm_refl. Qed.

Definition W_8611c : bv 32 := 0x01a63633.
Lemma F_8611c : fetch_word Ubsan.M.loaded_segments (0x8611c : word) = Some W_8611c.
Proof. vm_refl. Qed.
Lemma D_8611c : decode_any W_8611c = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86120 : bv 32 := 0x07813803.
Lemma F_86120 : fetch_word Ubsan.M.loaded_segments (0x86120 : word) = Some W_86120.
Proof. vm_refl. Qed.
Lemma D_86120 : decode_any W_86120 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86124 : bv 32 := 0x01064633.
Lemma F_86124 : fetch_word Ubsan.M.loaded_segments (0x86124 : word) = Some W_86124.
Proof. vm_refl. Qed.
Lemma D_86124 : decode_any W_86124 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86128 : bv 32 := 0x00164613.
Lemma F_86128 : fetch_word Ubsan.M.loaded_segments (0x86128 : word) = Some W_86128.
Proof. vm_refl. Qed.
Lemma D_86128 : decode_any W_86128 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8612c : bv 32 := 0x00061463.
Lemma F_8612c : fetch_word Ubsan.M.loaded_segments (0x8612c : word) = Some W_8612c.
Proof. vm_refl. Qed.
Lemma D_8612c : decode_any W_8612c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86130 : bv 32 := 0xbc4fc06f.
Lemma F_86130 : fetch_word Ubsan.M.loaded_segments (0x86130 : word) = Some W_86130.
Proof. vm_refl. Qed.
Lemma D_86130 : decode_any W_86130 = Some (Jal 0 2081732, 4%Z).
Proof. vm_refl. Qed.

Definition W_86134 : bv 32 := 0x001e0e1b.
Lemma F_86134 : fetch_word Ubsan.M.loaded_segments (0x86134 : word) = Some W_86134.
Proof. vm_refl. Qed.
Lemma D_86134 : decode_any W_86134 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86138 : bv 32 := 0x00d585b3.
Lemma F_86138 : fetch_word Ubsan.M.loaded_segments (0x86138 : word) = Some W_86138.
Proof. vm_refl. Qed.
Lemma D_86138 : decode_any W_86138 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8613c : bv 32 := 0x007c8cb3.
Lemma F_8613c : fetch_word Ubsan.M.loaded_segments (0x8613c : word) = Some W_8613c.
Proof. vm_refl. Qed.
Lemma D_8613c : decode_any W_8613c = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86140 : bv 32 := 0x000a8813.
Lemma F_86140 : fetch_word Ubsan.M.loaded_segments (0x86140 : word) = Some W_86140.
Proof. vm_refl. Qed.
Lemma D_86140 : decode_any W_86140 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86144 : bv 32 := 0xf00e14e3.
Lemma F_86144 : fetch_word Ubsan.M.loaded_segments (0x86144 : word) = Some W_86144.
Proof. vm_refl. Qed.
Lemma D_86144 : decode_any W_86144 = Some (Branch BC_NE 28 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_86148 : bv 32 := 0x02013583.
Lemma F_86148 : fetch_word Ubsan.M.loaded_segments (0x86148 : word) = Some W_86148.
Proof. vm_refl. Qed.
Lemma D_86148 : decode_any W_86148 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8614c : bv 32 := 0x16059e63.
Lemma F_8614c : fetch_word Ubsan.M.loaded_segments (0x8614c : word) = Some W_8614c.
Proof. vm_refl. Qed.
Lemma D_8614c : decode_any W_8614c = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_86150 : bv 32 := 0xffffc693.
Lemma F_86150 : fetch_word Ubsan.M.loaded_segments (0x86150 : word) = Some W_86150.
Proof. vm_refl. Qed.
Lemma D_86150 : decode_any W_86150 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86154 : bv 32 := 0x00271293.
Lemma F_86154 : fetch_word Ubsan.M.loaded_segments (0x86154 : word) = Some W_86154.
Proof. vm_refl. Qed.
Lemma D_86154 : decode_any W_86154 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86158 : bv 32 := 0x05813383.
Lemma F_86158 : fetch_word Ubsan.M.loaded_segments (0x86158 : word) = Some W_86158.
Proof. vm_refl. Qed.
Lemma D_86158 : decode_any W_86158 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8615c : bv 32 := 0x00239393.
Lemma F_8615c : fetch_word Ubsan.M.loaded_segments (0x8615c : word) = Some W_8615c.
Proof. vm_refl. Qed.
Lemma D_8615c : decode_any W_8615c = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86160 : bv 32 := 0x00337613.
Lemma F_86160 : fetch_word Ubsan.M.loaded_segments (0x86160 : word) = Some W_86160.
Proof. vm_refl. Qed.
Lemma D_86160 : decode_any W_86160 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86164 : bv 32 := 0x00397793.
Lemma F_86164 : fetch_word Ubsan.M.loaded_segments (0x86164 : word) = Some W_86164.
Proof. vm_refl. Qed.
Lemma D_86164 : decode_any W_86164 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86168 : bv 32 := 0x07013a03.
Lemma F_86168 : fetch_word Ubsan.M.loaded_segments (0x86168 : word) = Some W_86168.
Proof. vm_refl. Qed.
Lemma D_86168 : decode_any W_86168 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8616c : bv 32 := 0x002a1a13.
Lemma F_8616c : fetch_word Ubsan.M.loaded_segments (0x8616c : word) = Some W_8616c.
Proof. vm_refl. Qed.
Lemma D_8616c : decode_any W_8616c = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86170 : bv 32 := 0x00072b93.
Lemma F_86170 : fetch_word Ubsan.M.loaded_segments (0x86170 : word) = Some W_86170.
Proof. vm_refl. Qed.
Lemma D_86170 : decode_any W_86170 = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86174 : bv 32 := 0x02000c93.
Lemma F_86174 : fetch_word Ubsan.M.loaded_segments (0x86174 : word) = Some W_86174.
Proof. vm_refl. Qed.
Lemma D_86174 : decode_any W_86174 = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86178 : bv 32 := 0xffb00d13.
Lemma F_86178 : fetch_word Ubsan.M.loaded_segments (0x86178 : word) = Some W_86178.
Proof. vm_refl. Qed.
Lemma D_86178 : decode_any W_86178 = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_8617c : bv 32 := 0x0017b793.
Lemma F_8617c : fetch_word Ubsan.M.loaded_segments (0x8617c : word) = Some W_8617c.
Proof. vm_refl. Qed.
Lemma D_8617c : decode_any W_8617c = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86180 : bv 32 := 0x02f13023.
Lemma F_86180 : fetch_word Ubsan.M.loaded_segments (0x86180 : word) = Some W_86180.
Proof. vm_refl. Qed.
Lemma D_86180 : decode_any W_86180 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86184 : bv 32 := 0x00163613.
Lemma F_86184 : fetch_word Ubsan.M.loaded_segments (0x86184 : word) = Some W_86184.
Proof. vm_refl. Qed.
Lemma D_86184 : decode_any W_86184 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86188 : bv 32 := 0x00c13823.
Lemma F_86188 : fetch_word Ubsan.M.loaded_segments (0x86188 : word) = Some W_86188.
Proof. vm_refl. Qed.
Lemma D_86188 : decode_any W_86188 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8618c : bv 32 := 0x01f00993.
Lemma F_8618c : fetch_word Ubsan.M.loaded_segments (0x8618c : word) = Some W_8618c.
Proof. vm_refl. Qed.
Lemma D_8618c : decode_any W_8618c = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86190 : bv 32 := 0x00030b13.
Lemma F_86190 : fetch_word Ubsan.M.loaded_segments (0x86190 : word) = Some W_86190.
Proof. vm_refl. Qed.
Lemma D_86190 : decode_any W_86190 = Some (OpImm ALU_ADD 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86194 : bv 32 := 0x00090c13.
Lemma F_86194 : fetch_word Ubsan.M.loaded_segments (0x86194 : word) = Some W_86194.
Proof. vm_refl. Qed.
Lemma D_86194 : decode_any W_86194 = Some (OpImm ALU_ADD 24 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86198 : bv 32 := 0x07013603.
Lemma F_86198 : fetch_word Ubsan.M.loaded_segments (0x86198 : word) = Some W_86198.
Proof. vm_refl. Qed.
Lemma D_86198 : decode_any W_86198 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8619c : bv 32 := 0x0a060e63.
Lemma F_8619c : fetch_word Ubsan.M.loaded_segments (0x8619c : word) = Some W_8619c.
Proof. vm_refl. Qed.
Lemma D_8619c : decode_any W_8619c = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_861a0 : bv 32 := 0x00000d93.
Lemma F_861a0 : fetch_word Ubsan.M.loaded_segments (0x861a0 : word) = Some W_861a0.
Proof. vm_refl. Qed.
Lemma D_861a0 : decode_any W_861a0 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_861a4 : bv 32 := 0x00603833.
Lemma F_861a4 : fetch_word Ubsan.M.loaded_segments (0x861a4 : word) = Some W_861a4.
Proof. vm_refl. Qed.
Lemma D_861a4 : decode_any W_861a4 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_861a8 : bv 32 := 0x01203e33.
Lemma F_861a8 : fetch_word Ubsan.M.loaded_segments (0x861a8 : word) = Some W_861a8.
Proof. vm_refl. Qed.
Lemma D_861a8 : decode_any W_861a8 = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_861ac : bv 32 := 0x01013603.
Lemma F_861ac : fetch_word Ubsan.M.loaded_segments (0x861ac : word) = Some W_861ac.
Proof. vm_refl. Qed.
Lemma D_861ac : decode_any W_861ac = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_861b0 : bv 32 := 0x010674b3.
Lemma F_861b0 : fetch_word Ubsan.M.loaded_segments (0x861b0 : word) = Some W_861b0.
Proof. vm_refl. Qed.
Lemma D_861b0 : decode_any W_861b0 = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_861b4 : bv 32 := 0x02013603.
Lemma F_861b4 : fetch_word Ubsan.M.loaded_segments (0x861b4 : word) = Some W_861b4.
Proof. vm_refl. Qed.
Lemma D_861b4 : decode_any W_861b4 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_861b8 : bv 32 := 0x01c67ab3.
Lemma F_861b8 : fetch_word Ubsan.M.loaded_segments (0x861b8 : word) = Some W_861b8.
Proof. vm_refl. Qed.
Lemma D_861b8 : decode_any W_861b8 = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_861bc : bv 32 := 0x01bb0633.
Lemma F_861bc : fetch_word Ubsan.M.loaded_segments (0x861bc : word) = Some W_861bc.
Proof. vm_refl. Qed.
Lemma D_861bc : decode_any W_861bc = Some (Op ALU_ADD 12 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_861c0 : bv 32 := 0x00667463.
Lemma F_861c0 : fetch_word Ubsan.M.loaded_segments (0x861c0 : word) = Some W_861c0.
Proof. vm_refl. Qed.
Lemma D_861c0 : decode_any W_861c0 = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_861c4 : bv 32 := 0xb30fc06f.
Lemma F_861c4 : fetch_word Ubsan.M.loaded_segments (0x861c4 : word) = Some W_861c4.
Proof. vm_refl. Qed.
Lemma D_861c4 : decode_any W_861c4 = Some (Jal 0 2081584, 4%Z).
Proof. vm_refl. Qed.

Definition W_861c8 : bv 32 := 0x00163613.
Lemma F_861c8 : fetch_word Ubsan.M.loaded_segments (0x861c8 : word) = Some W_861c8.
Proof. vm_refl. Qed.
Lemma D_861c8 : decode_any W_861c8 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_861cc : bv 32 := 0x00c84633.
Lemma F_861cc : fetch_word Ubsan.M.loaded_segments (0x861cc : word) = Some W_861cc.
Proof. vm_refl. Qed.
Lemma D_861cc : decode_any W_861cc = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_861d0 : bv 32 := 0x00061463.
Lemma F_861d0 : fetch_word Ubsan.M.loaded_segments (0x861d0 : word) = Some W_861d0.
Proof. vm_refl. Qed.
Lemma D_861d0 : decode_any W_861d0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_861d4 : bv 32 := 0xb20fc06f.
Lemma F_861d4 : fetch_word Ubsan.M.loaded_segments (0x861d4 : word) = Some W_861d4.
Proof. vm_refl. Qed.
Lemma D_861d4 : decode_any W_861d4 = Some (Jal 0 2081568, 4%Z).
Proof. vm_refl. Qed.

Definition W_861d8 : bv 32 := 0x00049463.
Lemma F_861d8 : fetch_word Ubsan.M.loaded_segments (0x861d8 : word) = Some W_861d8.
Proof. vm_refl. Qed.
Lemma D_861d8 : decode_any W_861d8 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_861dc : bv 32 := 0xb18fc06f.
Lemma F_861dc : fetch_word Ubsan.M.loaded_segments (0x861dc : word) = Some W_861dc.
Proof. vm_refl. Qed.
Lemma D_861dc : decode_any W_861dc = Some (Jal 0 2081560, 4%Z).
Proof. vm_refl. Qed.

Definition W_861e0 : bv 32 := 0x019f1463.
Lemma F_861e0 : fetch_word Ubsan.M.loaded_segments (0x861e0 : word) = Some W_861e0.
Proof. vm_refl. Qed.
Lemma D_861e0 : decode_any W_861e0 = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_861e4 : bv 32 := 0xb10fc06f.
Lemma F_861e4 : fetch_word Ubsan.M.loaded_segments (0x861e4 : word) = Some W_861e4.
Proof. vm_refl. Qed.
Lemma D_861e4 : decode_any W_861e4 = Some (Jal 0 2081552, 4%Z).
Proof. vm_refl. Qed.

Definition W_861e8 : bv 32 := 0x01b30633.
Lemma F_861e8 : fetch_word Ubsan.M.loaded_segments (0x861e8 : word) = Some W_861e8.
Proof. vm_refl. Qed.
Lemma D_861e8 : decode_any W_861e8 = Some (Op ALU_ADD 12 6 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_861ec : bv 32 := 0x00cd7463.
Lemma F_861ec : fetch_word Ubsan.M.loaded_segments (0x861ec : word) = Some W_861ec.
Proof. vm_refl. Qed.
Lemma D_861ec : decode_any W_861ec = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_861f0 : bv 32 := 0xb04fc06f.
Lemma F_861f0 : fetch_word Ubsan.M.loaded_segments (0x861f0 : word) = Some W_861f0.
Proof. vm_refl. Qed.
Lemma D_861f0 : decode_any W_861f0 = Some (Jal 0 2081540, 4%Z).
Proof. vm_refl. Qed.

Definition W_861f4 : bv 32 := 0x0089f463.
Lemma F_861f4 : fetch_word Ubsan.M.loaded_segments (0x861f4 : word) = Some W_861f4.
Proof. vm_refl. Qed.
Lemma D_861f4 : decode_any W_861f4 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_861f8 : bv 32 := 0xafcfc06f.
Lemma F_861f8 : fetch_word Ubsan.M.loaded_segments (0x861f8 : word) = Some W_861f8.
Proof. vm_refl. Qed.
Lemma D_861f8 : decode_any W_861f8 = Some (Jal 0 2081532, 4%Z).
Proof. vm_refl. Qed.

Definition W_861fc : bv 32 := 0x01bc07b3.
Lemma F_861fc : fetch_word Ubsan.M.loaded_segments (0x861fc : word) = Some W_861fc.
Proof. vm_refl. Qed.
Lemma D_861fc : decode_any W_861fc = Some (Op ALU_ADD 15 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86200 : bv 32 := 0x0127f463.
Lemma F_86200 : fetch_word Ubsan.M.loaded_segments (0x86200 : word) = Some W_86200.
Proof. vm_refl. Qed.
Lemma D_86200 : decode_any W_86200 = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86204 : bv 32 := 0xaf0fc06f.
Lemma F_86204 : fetch_word Ubsan.M.loaded_segments (0x86204 : word) = Some W_86204.
Proof. vm_refl. Qed.
Lemma D_86204 : decode_any W_86204 = Some (Jal 0 2081520, 4%Z).
Proof. vm_refl. Qed.

Definition W_86208 : bv 32 := 0x0017b793.
Lemma F_86208 : fetch_word Ubsan.M.loaded_segments (0x86208 : word) = Some W_86208.
Proof. vm_refl. Qed.
Lemma D_86208 : decode_any W_86208 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8620c : bv 32 := 0x00fe47b3.
Lemma F_8620c : fetch_word Ubsan.M.loaded_segments (0x8620c : word) = Some W_8620c.
Proof. vm_refl. Qed.
Lemma D_8620c : decode_any W_8620c = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86210 : bv 32 := 0x00079463.
Lemma F_86210 : fetch_word Ubsan.M.loaded_segments (0x86210 : word) = Some W_86210.
Proof. vm_refl. Qed.
Lemma D_86210 : decode_any W_86210 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86214 : bv 32 := 0xae0fc06f.
Lemma F_86214 : fetch_word Ubsan.M.loaded_segments (0x86214 : word) = Some W_86214.
Proof. vm_refl. Qed.
Lemma D_86214 : decode_any W_86214 = Some (Jal 0 2081504, 4%Z).
Proof. vm_refl. Qed.

Definition W_86218 : bv 32 := 0x000a9463.
Lemma F_86218 : fetch_word Ubsan.M.loaded_segments (0x86218 : word) = Some W_86218.
Proof. vm_refl. Qed.
Lemma D_86218 : decode_any W_86218 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8621c : bv 32 := 0xad8fc06f.
Lemma F_8621c : fetch_word Ubsan.M.loaded_segments (0x8621c : word) = Some W_8621c.
Proof. vm_refl. Qed.
Lemma D_8621c : decode_any W_8621c = Some (Jal 0 2081496, 4%Z).
Proof. vm_refl. Qed.

Definition W_86220 : bv 32 := 0x00062783.
Lemma F_86220 : fetch_word Ubsan.M.loaded_segments (0x86220 : word) = Some W_86220.
Proof. vm_refl. Qed.
Lemma D_86220 : decode_any W_86220 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86224 : bv 32 := 0x00462603.
Lemma F_86224 : fetch_word Ubsan.M.loaded_segments (0x86224 : word) = Some W_86224.
Proof. vm_refl. Qed.
Lemma D_86224 : decode_any W_86224 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86228 : bv 32 := 0x01b908b3.
Lemma F_86228 : fetch_word Ubsan.M.loaded_segments (0x86228 : word) = Some W_86228.
Proof. vm_refl. Qed.
Lemma D_86228 : decode_any W_86228 = Some (Op ALU_ADD 17 18 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8622c : bv 32 := 0x0008a083.
Lemma F_8622c : fetch_word Ubsan.M.loaded_segments (0x8622c : word) = Some W_8622c.
Proof. vm_refl. Qed.
Lemma D_8622c : decode_any W_8622c = Some (Load SZ4 true 1 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86230 : bv 32 := 0x01d797bb.
Lemma F_86230 : fetch_word Ubsan.M.loaded_segments (0x86230 : word) = Some W_86230.
Proof. vm_refl. Qed.
Lemma D_86230 : decode_any W_86230 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86234 : bv 32 := 0x0086563b.
Lemma F_86234 : fetch_word Ubsan.M.loaded_segments (0x86234 : word) = Some W_86234.
Proof. vm_refl. Qed.
Lemma D_86234 : decode_any W_86234 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86238 : bv 32 := 0x00d7f7b3.
Lemma F_86238 : fetch_word Ubsan.M.loaded_segments (0x86238 : word) = Some W_86238.
Proof. vm_refl. Qed.
Lemma D_86238 : decode_any W_86238 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8623c : bv 32 := 0x01f67633.
Lemma F_8623c : fetch_word Ubsan.M.loaded_segments (0x8623c : word) = Some W_8623c.
Proof. vm_refl. Qed.
Lemma D_8623c : decode_any W_8623c = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86240 : bv 32 := 0x00f66633.
Lemma F_86240 : fetch_word Ubsan.M.loaded_segments (0x86240 : word) = Some W_86240.
Proof. vm_refl. Qed.
Lemma D_86240 : decode_any W_86240 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86244 : bv 32 := 0x00164633.
Lemma F_86244 : fetch_word Ubsan.M.loaded_segments (0x86244 : word) = Some W_86244.
Proof. vm_refl. Qed.
Lemma D_86244 : decode_any W_86244 = Some (Op ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86248 : bv 32 := 0xfff64613.
Lemma F_86248 : fetch_word Ubsan.M.loaded_segments (0x86248 : word) = Some W_86248.
Proof. vm_refl. Qed.
Lemma D_86248 : decode_any W_86248 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8624c : bv 32 := 0x004d8d93.
Lemma F_8624c : fetch_word Ubsan.M.loaded_segments (0x8624c : word) = Some W_8624c.
Proof. vm_refl. Qed.
Lemma D_8624c : decode_any W_8624c = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86250 : bv 32 := 0x00c8a023.
Lemma F_86250 : fetch_word Ubsan.M.loaded_segments (0x86250 : word) = Some W_86250.
Proof. vm_refl. Qed.
Lemma D_86250 : decode_any W_86250 = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86254 : bv 32 := 0xf7ba14e3.
Lemma F_86254 : fetch_word Ubsan.M.loaded_segments (0x86254 : word) = Some W_86254.
Proof. vm_refl. Qed.
Lemma D_86254 : decode_any W_86254 = Some (Branch BC_NE 20 27 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_86258 : bv 32 := 0x00590633.
Lemma F_86258 : fetch_word Ubsan.M.loaded_segments (0x86258 : word) = Some W_86258.
Proof. vm_refl. Qed.
Lemma D_86258 : decode_any W_86258 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8625c : bv 32 := 0x012037b3.
Lemma F_8625c : fetch_word Ubsan.M.loaded_segments (0x8625c : word) = Some W_8625c.
Proof. vm_refl. Qed.
Lemma D_8625c : decode_any W_8625c = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86260 : bv 32 := 0x00163813.
Lemma F_86260 : fetch_word Ubsan.M.loaded_segments (0x86260 : word) = Some W_86260.
Proof. vm_refl. Qed.
Lemma D_86260 : decode_any W_86260 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86264 : bv 32 := 0x01079463.
Lemma F_86264 : fetch_word Ubsan.M.loaded_segments (0x86264 : word) = Some W_86264.
Proof. vm_refl. Qed.
Lemma D_86264 : decode_any W_86264 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86268 : bv 32 := 0xa8cfc06f.
Lemma F_86268 : fetch_word Ubsan.M.loaded_segments (0x86268 : word) = Some W_86268.
Proof. vm_refl. Qed.
Lemma D_86268 : decode_any W_86268 = Some (Jal 0 2081420, 4%Z).
Proof. vm_refl. Qed.

Definition W_8626c : bv 32 := 0x01263633.
Lemma F_8626c : fetch_word Ubsan.M.loaded_segments (0x8626c : word) = Some W_8626c.
Proof. vm_refl. Qed.
Lemma D_8626c : decode_any W_8626c = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86270 : bv 32 := 0x01764633.
Lemma F_86270 : fetch_word Ubsan.M.loaded_segments (0x86270 : word) = Some W_86270.
Proof. vm_refl. Qed.
Lemma D_86270 : decode_any W_86270 = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_86274 : bv 32 := 0x00164613.
Lemma F_86274 : fetch_word Ubsan.M.loaded_segments (0x86274 : word) = Some W_86274.
Proof. vm_refl. Qed.
Lemma D_86274 : decode_any W_86274 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86278 : bv 32 := 0x00061463.
Lemma F_86278 : fetch_word Ubsan.M.loaded_segments (0x86278 : word) = Some W_86278.
Proof. vm_refl. Qed.
Lemma D_86278 : decode_any W_86278 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8627c : bv 32 := 0xa78fc06f.
Lemma F_8627c : fetch_word Ubsan.M.loaded_segments (0x8627c : word) = Some W_8627c.
Proof. vm_refl. Qed.
Lemma D_8627c : decode_any W_8627c = Some (Jal 0 2081400, 4%Z).
Proof. vm_refl. Qed.

Definition W_86280 : bv 32 := 0x00638633.
Lemma F_86280 : fetch_word Ubsan.M.loaded_segments (0x86280 : word) = Some W_86280.
Proof. vm_refl. Qed.
Lemma D_86280 : decode_any W_86280 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86284 : bv 32 := 0x006037b3.
Lemma F_86284 : fetch_word Ubsan.M.loaded_segments (0x86284 : word) = Some W_86284.
Proof. vm_refl. Qed.
Lemma D_86284 : decode_any W_86284 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86288 : bv 32 := 0x00163813.
Lemma F_86288 : fetch_word Ubsan.M.loaded_segments (0x86288 : word) = Some W_86288.
Proof. vm_refl. Qed.
Lemma D_86288 : decode_any W_86288 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8628c : bv 32 := 0x01079463.
Lemma F_8628c : fetch_word Ubsan.M.loaded_segments (0x8628c : word) = Some W_8628c.
Proof. vm_refl. Qed.
Lemma D_8628c : decode_any W_8628c = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86290 : bv 32 := 0xa64fc06f.
Lemma F_86290 : fetch_word Ubsan.M.loaded_segments (0x86290 : word) = Some W_86290.
Proof. vm_refl. Qed.
Lemma D_86290 : decode_any W_86290 = Some (Jal 0 2081380, 4%Z).
Proof. vm_refl. Qed.

Definition W_86294 : bv 32 := 0x006637b3.
Lemma F_86294 : fetch_word Ubsan.M.loaded_segments (0x86294 : word) = Some W_86294.
Proof. vm_refl. Qed.
Lemma D_86294 : decode_any W_86294 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86298 : bv 32 := 0x07813803.
Lemma F_86298 : fetch_word Ubsan.M.loaded_segments (0x86298 : word) = Some W_86298.
Proof. vm_refl. Qed.
Lemma D_86298 : decode_any W_86298 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8629c : bv 32 := 0x0107c7b3.
Lemma F_8629c : fetch_word Ubsan.M.loaded_segments (0x8629c : word) = Some W_8629c.
Proof. vm_refl. Qed.
Lemma D_8629c : decode_any W_8629c = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_862a0 : bv 32 := 0x0017c793.
Lemma F_862a0 : fetch_word Ubsan.M.loaded_segments (0x862a0 : word) = Some W_862a0.
Proof. vm_refl. Qed.
Lemma D_862a0 : decode_any W_862a0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_862a4 : bv 32 := 0x00079463.
Lemma F_862a4 : fetch_word Ubsan.M.loaded_segments (0x862a4 : word) = Some W_862a4.
Proof. vm_refl. Qed.
Lemma D_862a4 : decode_any W_862a4 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_862a8 : bv 32 := 0xa4cfc06f.
Lemma F_862a8 : fetch_word Ubsan.M.loaded_segments (0x862a8 : word) = Some W_862a8.
Proof. vm_refl. Qed.
Lemma D_862a8 : decode_any W_862a8 = Some (Jal 0 2081356, 4%Z).
Proof. vm_refl. Qed.

Definition W_862ac : bv 32 := 0x00590933.
Lemma F_862ac : fetch_word Ubsan.M.loaded_segments (0x862ac : word) = Some W_862ac.
Proof. vm_refl. Qed.
Lemma D_862ac : decode_any W_862ac = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_862b0 : bv 32 := 0x0015859b.
Lemma F_862b0 : fetch_word Ubsan.M.loaded_segments (0x862b0 : word) = Some W_862b0.
Proof. vm_refl. Qed.
Lemma D_862b0 : decode_any W_862b0 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_862b4 : bv 32 := 0x005c0c33.
Lemma F_862b4 : fetch_word Ubsan.M.loaded_segments (0x862b4 : word) = Some W_862b4.
Proof. vm_refl. Qed.
Lemma D_862b4 : decode_any W_862b4 = Some (Op ALU_ADD 24 24 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_862b8 : bv 32 := 0x007b0b33.
Lemma F_862b8 : fetch_word Ubsan.M.loaded_segments (0x862b8 : word) = Some W_862b8.
Proof. vm_refl. Qed.
Lemma D_862b8 : decode_any W_862b8 = Some (Op ALU_ADD 22 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_862bc : bv 32 := 0x00060313.
Lemma F_862bc : fetch_word Ubsan.M.loaded_segments (0x862bc : word) = Some W_862bc.
Proof. vm_refl. Qed.
Lemma D_862bc : decode_any W_862bc = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_862c0 : bv 32 := 0x08013603.
Lemma F_862c0 : fetch_word Ubsan.M.loaded_segments (0x862c0 : word) = Some W_862c0.
Proof. vm_refl. Qed.
Lemma D_862c0 : decode_any W_862c0 = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_862c4 : bv 32 := 0xecc59ae3.
Lemma F_862c4 : fetch_word Ubsan.M.loaded_segments (0x862c4 : word) = Some W_862c4.
Proof. vm_refl. Qed.
Lemma D_862c4 : decode_any W_862c4 = Some (Branch BC_NE 11 12 7892, 4%Z).
Proof. vm_refl. Qed.

Definition W_862c8 : bv 32 := 0x01813583.
Lemma F_862c8 : fetch_word Ubsan.M.loaded_segments (0x862c8 : word) = Some W_862c8.
Proof. vm_refl. Qed.
Lemma D_862c8 : decode_any W_862c8 = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_862cc : bv 32 := 0x00058463.
Lemma F_862cc : fetch_word Ubsan.M.loaded_segments (0x862cc : word) = Some W_862cc.
Proof. vm_refl. Qed.
Lemma D_862cc : decode_any W_862cc = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_862d0 : bv 32 := 0x2e80106f.
Lemma F_862d0 : fetch_word Ubsan.M.loaded_segments (0x862d0 : word) = Some W_862d0.
Proof. vm_refl. Qed.
Lemma D_862d0 : decode_any W_862d0 = Some (Jal 0 4840, 4%Z).
Proof. vm_refl. Qed.

Definition W_862d4 : bv 32 := 0x06813583.
Lemma F_862d4 : fetch_word Ubsan.M.loaded_segments (0x862d4 : word) = Some W_862d4.
Proof. vm_refl. Qed.
Lemma D_862d4 : decode_any W_862d4 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_862d8 : bv 32 := 0x0035f593.
Lemma F_862d8 : fetch_word Ubsan.M.loaded_segments (0x862d8 : word) = Some W_862d8.
Proof. vm_refl. Qed.
Lemma D_862d8 : decode_any W_862d8 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_862dc : bv 32 := 0x00058463.
Lemma F_862dc : fetch_word Ubsan.M.loaded_segments (0x862dc : word) = Some W_862dc.
Proof. vm_refl. Qed.
Lemma D_862dc : decode_any W_862dc = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_862e0 : bv 32 := 0xa14fc06f.
Lemma F_862e0 : fetch_word Ubsan.M.loaded_segments (0x862e0 : word) = Some W_862e0.
Proof. vm_refl. Qed.
Lemma D_862e0 : decode_any W_862e0 = Some (Jal 0 2081300, 4%Z).
Proof. vm_refl. Qed.

Definition W_862e4 : bv 32 := 0xffffc613.
Lemma F_862e4 : fetch_word Ubsan.M.loaded_segments (0x862e4 : word) = Some W_862e4.
Proof. vm_refl. Qed.
Lemma D_862e4 : decode_any W_862e4 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_862e8 : bv 32 := 0x06013683.
Lemma F_862e8 : fetch_word Ubsan.M.loaded_segments (0x862e8 : word) = Some W_862e8.
Proof. vm_refl. Qed.
Lemma D_862e8 : decode_any W_862e8 = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_862ec : bv 32 := 0xfff6c693.
Lemma F_862ec : fetch_word Ubsan.M.loaded_segments (0x862ec : word) = Some W_862ec.
Proof. vm_refl. Qed.
Lemma D_862ec : decode_any W_862ec = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_862f0 : bv 32 := 0x00271793.
Lemma F_862f0 : fetch_word Ubsan.M.loaded_segments (0x862f0 : word) = Some W_862f0.
Proof. vm_refl. Qed.
Lemma D_862f0 : decode_any W_862f0 = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_862f4 : bv 32 := 0x05813303.
Lemma F_862f4 : fetch_word Ubsan.M.loaded_segments (0x862f4 : word) = Some W_862f4.
Proof. vm_refl. Qed.
Lemma D_862f4 : decode_any W_862f4 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_862f8 : bv 32 := 0x00231313.
Lemma F_862f8 : fetch_word Ubsan.M.loaded_segments (0x862f8 : word) = Some W_862f8.
Proof. vm_refl. Qed.
Lemma D_862f8 : decode_any W_862f8 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_862fc : bv 32 := 0x00357893.
Lemma F_862fc : fetch_word Ubsan.M.loaded_segments (0x862fc : word) = Some W_862fc.
Proof. vm_refl. Qed.
Lemma D_862fc : decode_any W_862fc = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86300 : bv 32 := 0x05013903.
Lemma F_86300 : fetch_word Ubsan.M.loaded_segments (0x86300 : word) = Some W_86300.
Proof. vm_refl. Qed.
Lemma D_86300 : decode_any W_86300 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_86304 : bv 32 := 0x02813803.
Lemma F_86304 : fetch_word Ubsan.M.loaded_segments (0x86304 : word) = Some W_86304.
Proof. vm_refl. Qed.
Lemma D_86304 : decode_any W_86304 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86308 : bv 32 := 0x412804bb.
Lemma F_86308 : fetch_word Ubsan.M.loaded_segments (0x86308 : word) = Some W_86308.
Proof. vm_refl. Qed.
Lemma D_86308 : decode_any W_86308 = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8630c : bv 32 := 0x03813383.
Lemma F_8630c : fetch_word Ubsan.M.loaded_segments (0x8630c : word) = Some W_8630c.
Proof. vm_refl. Qed.
Lemma D_8630c : decode_any W_8630c = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_86310 : bv 32 := 0x03013803.
Lemma F_86310 : fetch_word Ubsan.M.loaded_segments (0x86310 : word) = Some W_86310.
Proof. vm_refl. Qed.
Lemma D_86310 : decode_any W_86310 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_86314 : bv 32 := 0x007803b3.
Lemma F_86314 : fetch_word Ubsan.M.loaded_segments (0x86314 : word) = Some W_86314.
Proof. vm_refl. Qed.
Lemma D_86314 : decode_any W_86314 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86318 : bv 32 := 0x04813283.
Lemma F_86318 : fetch_word Ubsan.M.loaded_segments (0x86318 : word) = Some W_86318.
Proof. vm_refl. Qed.
Lemma D_86318 : decode_any W_86318 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8631c : bv 32 := 0x43f2d813.
Lemma F_8631c : fetch_word Ubsan.M.loaded_segments (0x8631c : word) = Some W_8631c.
Proof. vm_refl. Qed.
Lemma D_8631c : decode_any W_8631c = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86320 : bv 32 := 0x00587e33.
Lemma F_86320 : fetch_word Ubsan.M.loaded_segments (0x86320 : word) = Some W_86320.
Proof. vm_refl. Qed.
Lemma D_86320 : decode_any W_86320 = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86324 : bv 32 := 0x02000813.
Lemma F_86324 : fetch_word Ubsan.M.loaded_segments (0x86324 : word) = Some W_86324.
Proof. vm_refl. Qed.
Lemma D_86324 : decode_any W_86324 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86328 : bv 32 := 0x00813283.
Lemma F_86328 : fetch_word Ubsan.M.loaded_segments (0x86328 : word) = Some W_86328.
Proof. vm_refl. Qed.
Lemma D_86328 : decode_any W_86328 = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8632c : bv 32 := 0x0012f293.
Lemma F_8632c : fetch_word Ubsan.M.loaded_segments (0x8632c : word) = Some W_8632c.
Proof. vm_refl. Qed.
Lemma D_8632c : decode_any W_8632c = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86330 : bv 32 := 0x00072713.
Lemma F_86330 : fetch_word Ubsan.M.loaded_segments (0x86330 : word) = Some W_86330.
Proof. vm_refl. Qed.
Lemma D_86330 : decode_any W_86330 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86334 : bv 32 := 0x01c38e33.
Lemma F_86334 : fetch_word Ubsan.M.loaded_segments (0x86334 : word) = Some W_86334.
Proof. vm_refl. Qed.
Lemma D_86334 : decode_any W_86334 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86338 : bv 32 := 0xffb00393.
Lemma F_86338 : fetch_word Ubsan.M.loaded_segments (0x86338 : word) = Some W_86338.
Proof. vm_refl. Qed.
Lemma D_86338 : decode_any W_86338 = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_8633c : bv 32 := 0x412e093b.
Lemma F_8633c : fetch_word Ubsan.M.loaded_segments (0x8633c : word) = Some W_8633c.
Proof. vm_refl. Qed.
Lemma D_8633c : decode_any W_8633c = Some (Op32 ALU_SUB 18 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86340 : bv 32 := 0x06813e03.
Lemma F_86340 : fetch_word Ubsan.M.loaded_segments (0x86340 : word) = Some W_86340.
Proof. vm_refl. Qed.
Lemma D_86340 : decode_any W_86340 = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86344 : bv 32 := 0x006e0e33.
Lemma F_86344 : fetch_word Ubsan.M.loaded_segments (0x86344 : word) = Some W_86344.
Proof. vm_refl. Qed.
Lemma D_86344 : decode_any W_86344 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86348 : bv 32 := 0x04013983.
Lemma F_86348 : fetch_word Ubsan.M.loaded_segments (0x86348 : word) = Some W_86348.
Proof. vm_refl. Qed.
Lemma D_86348 : decode_any W_86348 = Some (Load SZ8 true 19 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8634c : bv 32 := 0x4139093b.
Lemma F_8634c : fetch_word Ubsan.M.loaded_segments (0x8634c : word) = Some W_8634c.
Proof. vm_refl. Qed.
Lemma D_8634c : decode_any W_8634c = Some (Op32 ALU_SUB 18 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86350 : bv 32 := 0x43f95993.
Lemma F_86350 : fetch_word Ubsan.M.loaded_segments (0x86350 : word) = Some W_86350.
Proof. vm_refl. Qed.
Lemma D_86350 : decode_any W_86350 = Some (ShiftImm ALU_SRA 19 18 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86354 : bv 32 := 0x0129f933.
Lemma F_86354 : fetch_word Ubsan.M.loaded_segments (0x86354 : word) = Some W_86354.
Proof. vm_refl. Qed.
Lemma D_86354 : decode_any W_86354 = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86358 : bv 32 := 0x412484bb.
Lemma F_86358 : fetch_word Ubsan.M.loaded_segments (0x86358 : word) = Some W_86358.
Proof. vm_refl. Qed.
Lemma D_86358 : decode_any W_86358 = Some (Op32 ALU_SUB 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8635c : bv 32 := 0x01f00993.
Lemma F_8635c : fetch_word Ubsan.M.loaded_segments (0x8635c : word) = Some W_8635c.
Proof. vm_refl. Qed.
Lemma D_8635c : decode_any W_8635c = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86360 : bv 32 := 0x00050a13.
Lemma F_86360 : fetch_word Ubsan.M.loaded_segments (0x86360 : word) = Some W_86360.
Proof. vm_refl. Qed.
Lemma D_86360 : decode_any W_86360 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86364 : bv 32 := 0x06813a83.
Lemma F_86364 : fetch_word Ubsan.M.loaded_segments (0x86364 : word) = Some W_86364.
Proof. vm_refl. Qed.
Lemma D_86364 : decode_any W_86364 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86368 : bv 32 := 0x00ba8ab3.
Lemma F_86368 : fetch_word Ubsan.M.loaded_segments (0x86368 : word) = Some W_86368.
Proof. vm_refl. Qed.
Lemma D_86368 : decode_any W_86368 = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8636c : bv 32 := 0x000a9463.
Lemma F_8636c : fetch_word Ubsan.M.loaded_segments (0x8636c : word) = Some W_8636c.
Proof. vm_refl. Qed.
Lemma D_8636c : decode_any W_8636c = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86370 : bv 32 := 0x984fc06f.
Lemma F_86370 : fetch_word Ubsan.M.loaded_segments (0x86370 : word) = Some W_86370.
Proof. vm_refl. Qed.
Lemma D_86370 : decode_any W_86370 = Some (Jal 0 2081156, 4%Z).
Proof. vm_refl. Qed.

Definition W_86374 : bv 32 := 0x010f1463.
Lemma F_86374 : fetch_word Ubsan.M.loaded_segments (0x86374 : word) = Some W_86374.
Proof. vm_refl. Qed.
Lemma D_86374 : decode_any W_86374 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86378 : bv 32 := 0x97cfc06f.
Lemma F_86378 : fetch_word Ubsan.M.loaded_segments (0x86378 : word) = Some W_86378.
Proof. vm_refl. Qed.
Lemma D_86378 : decode_any W_86378 = Some (Jal 0 2081148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8637c : bv 32 := 0x000aa903.
Lemma F_8637c : fetch_word Ubsan.M.loaded_segments (0x8637c : word) = Some W_8637c.
Proof. vm_refl. Qed.
Lemma D_8637c : decode_any W_8637c = Some (Load SZ4 true 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86380 : bv 32 := 0x01d91b3b.
Lemma F_86380 : fetch_word Ubsan.M.loaded_segments (0x86380 : word) = Some W_86380.
Proof. vm_refl. Qed.
Lemma D_86380 : decode_any W_86380 = Some (Op32 ALU_SLL 22 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86384 : bv 32 := 0x02029463.
Lemma F_86384 : fetch_word Ubsan.M.loaded_segments (0x86384 : word) = Some W_86384.
Proof. vm_refl. Qed.
Lemma D_86384 : decode_any W_86384 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86388 : bv 32 := 0x0153f463.
Lemma F_86388 : fetch_word Ubsan.M.loaded_segments (0x86388 : word) = Some W_86388.
Proof. vm_refl. Qed.
Lemma D_86388 : decode_any W_86388 = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8638c : bv 32 := 0x968fc06f.
Lemma F_8638c : fetch_word Ubsan.M.loaded_segments (0x8638c : word) = Some W_8638c.
Proof. vm_refl. Qed.
Lemma D_8638c : decode_any W_8638c = Some (Jal 0 2081128, 4%Z).
Proof. vm_refl. Qed.

Definition W_86390 : bv 32 := 0x0089f463.
Lemma F_86390 : fetch_word Ubsan.M.loaded_segments (0x86390 : word) = Some W_86390.
Proof. vm_refl. Qed.
Lemma D_86390 : decode_any W_86390 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86394 : bv 32 := 0x960fc06f.
Lemma F_86394 : fetch_word Ubsan.M.loaded_segments (0x86394 : word) = Some W_86394.
Proof. vm_refl. Qed.
Lemma D_86394 : decode_any W_86394 = Some (Jal 0 2081120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86398 : bv 32 := 0x004aa903.
Lemma F_86398 : fetch_word Ubsan.M.loaded_segments (0x86398 : word) = Some W_86398.
Proof. vm_refl. Qed.
Lemma D_86398 : decode_any W_86398 = Some (Load SZ4 true 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8639c : bv 32 := 0x00cb7b33.
Lemma F_8639c : fetch_word Ubsan.M.loaded_segments (0x8639c : word) = Some W_8639c.
Proof. vm_refl. Qed.
Lemma D_8639c : decode_any W_8639c = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_863a0 : bv 32 := 0x0089593b.
Lemma F_863a0 : fetch_word Ubsan.M.loaded_segments (0x863a0 : word) = Some W_863a0.
Proof. vm_refl. Qed.
Lemma D_863a0 : decode_any W_863a0 = Some (Op32 ALU_SRL 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_863a4 : bv 32 := 0x01f97933.
Lemma F_863a4 : fetch_word Ubsan.M.loaded_segments (0x863a4 : word) = Some W_863a4.
Proof. vm_refl. Qed.
Lemma D_863a4 : decode_any W_863a4 = Some (Op ALU_AND 18 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_863a8 : bv 32 := 0x01696b33.
Lemma F_863a8 : fetch_word Ubsan.M.loaded_segments (0x863a8 : word) = Some W_863a8.
Proof. vm_refl. Qed.
Lemma D_863a8 : decode_any W_863a8 = Some (Op ALU_OR 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_863ac : bv 32 := 0x00088463.
Lemma F_863ac : fetch_word Ubsan.M.loaded_segments (0x863ac : word) = Some W_863ac.
Proof. vm_refl. Qed.
Lemma D_863ac : decode_any W_863ac = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_863b0 : bv 32 := 0x944fc06f.
Lemma F_863b0 : fetch_word Ubsan.M.loaded_segments (0x863b0 : word) = Some W_863b0.
Proof. vm_refl. Qed.
Lemma D_863b0 : decode_any W_863b0 = Some (Jal 0 2081092, 4%Z).
Proof. vm_refl. Qed.

Definition W_863b4 : bv 32 := 0x00051463.
Lemma F_863b4 : fetch_word Ubsan.M.loaded_segments (0x863b4 : word) = Some W_863b4.
Proof. vm_refl. Qed.
Lemma D_863b4 : decode_any W_863b4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_863b8 : bv 32 := 0x93cfc06f.
Lemma F_863b8 : fetch_word Ubsan.M.loaded_segments (0x863b8 : word) = Some W_863b8.
Proof. vm_refl. Qed.
Lemma D_863b8 : decode_any W_863b8 = Some (Jal 0 2081084, 4%Z).
Proof. vm_refl. Qed.

Definition W_863bc : bv 32 := 0x00052903.
Lemma F_863bc : fetch_word Ubsan.M.loaded_segments (0x863bc : word) = Some W_863bc.
Proof. vm_refl. Qed.
Lemma D_863bc : decode_any W_863bc = Some (Load SZ4 true 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_863c0 : bv 32 := 0x00d97bb3.
Lemma F_863c0 : fetch_word Ubsan.M.loaded_segments (0x863c0 : word) = Some W_863c0.
Proof. vm_refl. Qed.
Lemma D_863c0 : decode_any W_863c0 = Some (Op ALU_AND 23 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_863c4 : bv 32 := 0x012b4933.
Lemma F_863c4 : fetch_word Ubsan.M.loaded_segments (0x863c4 : word) = Some W_863c4.
Proof. vm_refl. Qed.
Lemma D_863c4 : decode_any W_863c4 = Some (Op ALU_XOR 18 22 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_863c8 : bv 32 := 0xfff94913.
Lemma F_863c8 : fetch_word Ubsan.M.loaded_segments (0x863c8 : word) = Some W_863c8.
Proof. vm_refl. Qed.
Lemma D_863c8 : decode_any W_863c8 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_863cc : bv 32 := 0x06013b03.
Lemma F_863cc : fetch_word Ubsan.M.loaded_segments (0x863cc : word) = Some W_863cc.
Proof. vm_refl. Qed.
Lemma D_863cc : decode_any W_863cc = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_863d0 : bv 32 := 0x012b7933.
Lemma F_863d0 : fetch_word Ubsan.M.loaded_segments (0x863d0 : word) = Some W_863d0.
Proof. vm_refl. Qed.
Lemma D_863d0 : decode_any W_863d0 = Some (Op ALU_AND 18 22 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_863d4 : bv 32 := 0x01796933.
Lemma F_863d4 : fetch_word Ubsan.M.loaded_segments (0x863d4 : word) = Some W_863d4.
Proof. vm_refl. Qed.
Lemma D_863d4 : decode_any W_863d4 = Some (Op ALU_OR 18 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_863d8 : bv 32 := 0x01478b33.
Lemma F_863d8 : fetch_word Ubsan.M.loaded_segments (0x863d8 : word) = Some W_863d8.
Proof. vm_refl. Qed.
Lemma D_863d8 : decode_any W_863d8 = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_863dc : bv 32 := 0x01252023.
Lemma F_863dc : fetch_word Ubsan.M.loaded_segments (0x863dc : word) = Some W_863dc.
Proof. vm_refl. Qed.
Lemma D_863dc : decode_any W_863dc = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_863e0 : bv 32 := 0x000b1463.
Lemma F_863e0 : fetch_word Ubsan.M.loaded_segments (0x863e0 : word) = Some W_863e0.
Proof. vm_refl. Qed.
Lemma D_863e0 : decode_any W_863e0 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_863e4 : bv 32 := 0x910fc06f.
Lemma F_863e4 : fetch_word Ubsan.M.loaded_segments (0x863e4 : word) = Some W_863e4.
Proof. vm_refl. Qed.
Lemma D_863e4 : decode_any W_863e4 = Some (Jal 0 2081040, 4%Z).
Proof. vm_refl. Qed.

Definition W_863e8 : bv 32 := 0x014b3933.
Lemma F_863e8 : fetch_word Ubsan.M.loaded_segments (0x863e8 : word) = Some W_863e8.
Proof. vm_refl. Qed.
Lemma D_863e8 : decode_any W_863e8 = Some (Op ALU_SLTU 18 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_863ec : bv 32 := 0x00e94933.
Lemma F_863ec : fetch_word Ubsan.M.loaded_segments (0x863ec : word) = Some W_863ec.
Proof. vm_refl. Qed.
Lemma D_863ec : decode_any W_863ec = Some (Op ALU_XOR 18 18 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_863f0 : bv 32 := 0x00194913.
Lemma F_863f0 : fetch_word Ubsan.M.loaded_segments (0x863f0 : word) = Some W_863f0.
Proof. vm_refl. Qed.
Lemma D_863f0 : decode_any W_863f0 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_863f4 : bv 32 := 0x00091463.
Lemma F_863f4 : fetch_word Ubsan.M.loaded_segments (0x863f4 : word) = Some W_863f4.
Proof. vm_refl. Qed.
Lemma D_863f4 : decode_any W_863f4 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_863f8 : bv 32 := 0x8fcfc06f.
Lemma F_863f8 : fetch_word Ubsan.M.loaded_segments (0x863f8 : word) = Some W_863f8.
Proof. vm_refl. Qed.
Lemma D_863f8 : decode_any W_863f8 = Some (Jal 0 2081020, 4%Z).
Proof. vm_refl. Qed.

Definition W_863fc : bv 32 := 0x00be0a33.
Lemma F_863fc : fetch_word Ubsan.M.loaded_segments (0x863fc : word) = Some W_863fc.
Proof. vm_refl. Qed.
Lemma D_863fc : decode_any W_863fc = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86400 : bv 32 := 0x000a1463.
Lemma F_86400 : fetch_word Ubsan.M.loaded_segments (0x86400 : word) = Some W_86400.
Proof. vm_refl. Qed.
Lemma D_86400 : decode_any W_86400 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86404 : bv 32 := 0x8f0fc06f.
Lemma F_86404 : fetch_word Ubsan.M.loaded_segments (0x86404 : word) = Some W_86404.
Proof. vm_refl. Qed.
Lemma D_86404 : decode_any W_86404 = Some (Jal 0 2081008, 4%Z).
Proof. vm_refl. Qed.

Definition W_86408 : bv 32 := 0x015a3933.
Lemma F_86408 : fetch_word Ubsan.M.loaded_segments (0x86408 : word) = Some W_86408.
Proof. vm_refl. Qed.
Lemma D_86408 : decode_any W_86408 = Some (Op ALU_SLTU 18 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_8640c : bv 32 := 0x07813a03.
Lemma F_8640c : fetch_word Ubsan.M.loaded_segments (0x8640c : word) = Some W_8640c.
Proof. vm_refl. Qed.
Lemma D_8640c : decode_any W_8640c = Some (Load SZ8 true 20 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86410 : bv 32 := 0x01494933.
Lemma F_86410 : fetch_word Ubsan.M.loaded_segments (0x86410 : word) = Some W_86410.
Proof. vm_refl. Qed.
Lemma D_86410 : decode_any W_86410 = Some (Op ALU_XOR 18 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86414 : bv 32 := 0x00194913.
Lemma F_86414 : fetch_word Ubsan.M.loaded_segments (0x86414 : word) = Some W_86414.
Proof. vm_refl. Qed.
Lemma D_86414 : decode_any W_86414 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86418 : bv 32 := 0x00091463.
Lemma F_86418 : fetch_word Ubsan.M.loaded_segments (0x86418 : word) = Some W_86418.
Proof. vm_refl. Qed.
Lemma D_86418 : decode_any W_86418 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8641c : bv 32 := 0x8d8fc06f.
Lemma F_8641c : fetch_word Ubsan.M.loaded_segments (0x8641c : word) = Some W_8641c.
Proof. vm_refl. Qed.
Lemma D_8641c : decode_any W_8641c = Some (Jal 0 2080984, 4%Z).
Proof. vm_refl. Qed.

Definition W_86420 : bv 32 := 0x0014849b.
Lemma F_86420 : fetch_word Ubsan.M.loaded_segments (0x86420 : word) = Some W_86420.
Proof. vm_refl. Qed.
Lemma D_86420 : decode_any W_86420 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86424 : bv 32 := 0x006585b3.
Lemma F_86424 : fetch_word Ubsan.M.loaded_segments (0x86424 : word) = Some W_86424.
Proof. vm_refl. Qed.
Lemma D_86424 : decode_any W_86424 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86428 : bv 32 := 0x00f50533.
Lemma F_86428 : fetch_word Ubsan.M.loaded_segments (0x86428 : word) = Some W_86428.
Proof. vm_refl. Qed.
Lemma D_86428 : decode_any W_86428 = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8642c : bv 32 := 0x000b0a13.
Lemma F_8642c : fetch_word Ubsan.M.loaded_segments (0x8642c : word) = Some W_8642c.
Proof. vm_refl. Qed.
Lemma D_8642c : decode_any W_8642c = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86430 : bv 32 := 0xf2049ae3.
Lemma F_86430 : fetch_word Ubsan.M.loaded_segments (0x86430 : word) = Some W_86430.
Proof. vm_refl. Qed.
Lemma D_86430 : decode_any W_86430 = Some (Branch BC_NE 9 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_86434 : bv 32 := 0x1840106f.
Lemma F_86434 : fetch_word Ubsan.M.loaded_segments (0x86434 : word) = Some W_86434.
Proof. vm_refl. Qed.
Lemma D_86434 : decode_any W_86434 = Some (Jal 0 4484, 4%Z).
Proof. vm_refl. Qed.

Definition W_86438 : bv 32 := 0x18008263.
Lemma F_86438 : fetch_word Ubsan.M.loaded_segments (0x86438 : word) = Some W_86438.
Proof. vm_refl. Qed.
Lemma D_86438 : decode_any W_86438 = Some (Branch BC_EQ 1 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_8643c : bv 32 := 0x00000593.
Lemma F_8643c : fetch_word Ubsan.M.loaded_segments (0x8643c : word) = Some W_8643c.
Proof. vm_refl. Qed.
Lemma D_8643c : decode_any W_8643c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86440 : bv 32 := 0xffffc613.
Lemma F_86440 : fetch_word Ubsan.M.loaded_segments (0x86440 : word) = Some W_86440.
Proof. vm_refl. Qed.
Lemma D_86440 : decode_any W_86440 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86444 : bv 32 := 0x00c13023.
Lemma F_86444 : fetch_word Ubsan.M.loaded_segments (0x86444 : word) = Some W_86444.
Proof. vm_refl. Qed.
Lemma D_86444 : decode_any W_86444 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86448 : bv 32 := 0xfffdc293.
Lemma F_86448 : fetch_word Ubsan.M.loaded_segments (0x86448 : word) = Some W_86448.
Proof. vm_refl. Qed.
Lemma D_86448 : decode_any W_86448 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8644c : bv 32 := 0x00271393.
Lemma F_8644c : fetch_word Ubsan.M.loaded_segments (0x8644c : word) = Some W_8644c.
Proof. vm_refl. Qed.
Lemma D_8644c : decode_any W_8644c = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86450 : bv 32 := 0x05813683.
Lemma F_86450 : fetch_word Ubsan.M.loaded_segments (0x86450 : word) = Some W_86450.
Proof. vm_refl. Qed.
Lemma D_86450 : decode_any W_86450 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_86454 : bv 32 := 0x00269693.
Lemma F_86454 : fetch_word Ubsan.M.loaded_segments (0x86454 : word) = Some W_86454.
Proof. vm_refl. Qed.
Lemma D_86454 : decode_any W_86454 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86458 : bv 32 := 0x003cfb93.
Lemma F_86458 : fetch_word Ubsan.M.loaded_segments (0x86458 : word) = Some W_86458.
Proof. vm_refl. Qed.
Lemma D_86458 : decode_any W_86458 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8645c : bv 32 := 0x0037f613.
Lemma F_8645c : fetch_word Ubsan.M.loaded_segments (0x8645c : word) = Some W_8645c.
Proof. vm_refl. Qed.
Lemma D_8645c : decode_any W_8645c = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86460 : bv 32 := 0x05013483.
Lemma F_86460 : fetch_word Ubsan.M.loaded_segments (0x86460 : word) = Some W_86460.
Proof. vm_refl. Qed.
Lemma D_86460 : decode_any W_86460 = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_86464 : bv 32 := 0x02813803.
Lemma F_86464 : fetch_word Ubsan.M.loaded_segments (0x86464 : word) = Some W_86464.
Proof. vm_refl. Qed.
Lemma D_86464 : decode_any W_86464 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86468 : bv 32 := 0x4098083b.
Lemma F_86468 : fetch_word Ubsan.M.loaded_segments (0x86468 : word) = Some W_86468.
Proof. vm_refl. Qed.
Lemma D_86468 : decode_any W_86468 = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8646c : bv 32 := 0x03813883.
Lemma F_8646c : fetch_word Ubsan.M.loaded_segments (0x8646c : word) = Some W_8646c.
Proof. vm_refl. Qed.
Lemma D_8646c : decode_any W_8646c = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_86470 : bv 32 := 0x03013e03.
Lemma F_86470 : fetch_word Ubsan.M.loaded_segments (0x86470 : word) = Some W_86470.
Proof. vm_refl. Qed.
Lemma D_86470 : decode_any W_86470 = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_86474 : bv 32 := 0x011e08b3.
Lemma F_86474 : fetch_word Ubsan.M.loaded_segments (0x86474 : word) = Some W_86474.
Proof. vm_refl. Qed.
Lemma D_86474 : decode_any W_86474 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86478 : bv 32 := 0x04813a03.
Lemma F_86478 : fetch_word Ubsan.M.loaded_segments (0x86478 : word) = Some W_86478.
Proof. vm_refl. Qed.
Lemma D_86478 : decode_any W_86478 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8647c : bv 32 := 0x43fa5e13.
Lemma F_8647c : fetch_word Ubsan.M.loaded_segments (0x8647c : word) = Some W_8647c.
Proof. vm_refl. Qed.
Lemma D_8647c : decode_any W_8647c = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86480 : bv 32 := 0x01013983.
Lemma F_86480 : fetch_word Ubsan.M.loaded_segments (0x86480 : word) = Some W_86480.
Proof. vm_refl. Qed.
Lemma D_86480 : decode_any W_86480 = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86484 : bv 32 := 0x0019f993.
Lemma F_86484 : fetch_word Ubsan.M.loaded_segments (0x86484 : word) = Some W_86484.
Proof. vm_refl. Qed.
Lemma D_86484 : decode_any W_86484 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86488 : bv 32 := 0x001d7c13.
Lemma F_86488 : fetch_word Ubsan.M.loaded_segments (0x86488 : word) = Some W_86488.
Proof. vm_refl. Qed.
Lemma D_86488 : decode_any W_86488 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8648c : bv 32 := 0x01f00093.
Lemma F_8648c : fetch_word Ubsan.M.loaded_segments (0x8648c : word) = Some W_8648c.
Proof. vm_refl. Qed.
Lemma D_8648c : decode_any W_8648c = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86490 : bv 32 := 0x014e7e33.
Lemma F_86490 : fetch_word Ubsan.M.loaded_segments (0x86490 : word) = Some W_86490.
Proof. vm_refl. Qed.
Lemma D_86490 : decode_any W_86490 = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86494 : bv 32 := 0x409888bb.
Lemma F_86494 : fetch_word Ubsan.M.loaded_segments (0x86494 : word) = Some W_86494.
Proof. vm_refl. Qed.
Lemma D_86494 : decode_any W_86494 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86498 : bv 32 := 0x00d78a33.
Lemma F_86498 : fetch_word Ubsan.M.loaded_segments (0x86498 : word) = Some W_86498.
Proof. vm_refl. Qed.
Lemma D_86498 : decode_any W_86498 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8649c : bv 32 := 0x00163b13.
Lemma F_8649c : fetch_word Ubsan.M.loaded_segments (0x8649c : word) = Some W_8649c.
Proof. vm_refl. Qed.
Lemma D_8649c : decode_any W_8649c = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_864a0 : bv 32 := 0x04013603.
Lemma F_864a0 : fetch_word Ubsan.M.loaded_segments (0x864a0 : word) = Some W_864a0.
Proof. vm_refl. Qed.
Lemma D_864a0 : decode_any W_864a0 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_864a4 : bv 32 := 0x40c8863b.
Lemma F_864a4 : fetch_word Ubsan.M.loaded_segments (0x864a4 : word) = Some W_864a4.
Proof. vm_refl. Qed.
Lemma D_864a4 : decode_any W_864a4 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_864a8 : bv 32 := 0x01c6063b.
Lemma F_864a8 : fetch_word Ubsan.M.loaded_segments (0x864a8 : word) = Some W_864a8.
Proof. vm_refl. Qed.
Lemma D_864a8 : decode_any W_864a8 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_864ac : bv 32 := 0x43f65893.
Lemma F_864ac : fetch_word Ubsan.M.loaded_segments (0x864ac : word) = Some W_864ac.
Proof. vm_refl. Qed.
Lemma D_864ac : decode_any W_864ac = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_864b0 : bv 32 := 0x00c8f633.
Lemma F_864b0 : fetch_word Ubsan.M.loaded_segments (0x864b0 : word) = Some W_864b0.
Proof. vm_refl. Qed.
Lemma D_864b0 : decode_any W_864b0 = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_864b4 : bv 32 := 0x40c80e3b.
Lemma F_864b4 : fetch_word Ubsan.M.loaded_segments (0x864b4 : word) = Some W_864b4.
Proof. vm_refl. Qed.
Lemma D_864b4 : decode_any W_864b4 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_864b8 : bv 32 := 0x00072493.
Lemma F_864b8 : fetch_word Ubsan.M.loaded_segments (0x864b8 : word) = Some W_864b8.
Proof. vm_refl. Qed.
Lemma D_864b8 : decode_any W_864b8 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_864bc : bv 32 := 0x000c8813.
Lemma F_864bc : fetch_word Ubsan.M.loaded_segments (0x864bc : word) = Some W_864bc.
Proof. vm_refl. Qed.
Lemma D_864bc : decode_any W_864bc = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_864c0 : bv 32 := 0x00b78d33.
Lemma F_864c0 : fetch_word Ubsan.M.loaded_segments (0x864c0 : word) = Some W_864c0.
Proof. vm_refl. Qed.
Lemma D_864c0 : decode_any W_864c0 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_864c4 : bv 32 := 0x01a03633.
Lemma F_864c4 : fetch_word Ubsan.M.loaded_segments (0x864c4 : word) = Some W_864c4.
Proof. vm_refl. Qed.
Lemma D_864c4 : decode_any W_864c4 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_864c8 : bv 32 := 0x00cb7633.
Lemma F_864c8 : fetch_word Ubsan.M.loaded_segments (0x864c8 : word) = Some W_864c8.
Proof. vm_refl. Qed.
Lemma D_864c8 : decode_any W_864c8 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_864cc : bv 32 := 0x04098a63.
Lemma F_864cc : fetch_word Ubsan.M.loaded_segments (0x864cc : word) = Some W_864cc.
Proof. vm_refl. Qed.
Lemma D_864cc : decode_any W_864cc = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_864d0 : bv 32 := 0x00061463.
Lemma F_864d0 : fetch_word Ubsan.M.loaded_segments (0x864d0 : word) = Some W_864d0.
Proof. vm_refl. Qed.
Lemma D_864d0 : decode_any W_864d0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_864d4 : bv 32 := 0x820fc06f.
Lemma F_864d4 : fetch_word Ubsan.M.loaded_segments (0x864d4 : word) = Some W_864d4.
Proof. vm_refl. Qed.
Lemma D_864d4 : decode_any W_864d4 = Some (Jal 0 2080800, 4%Z).
Proof. vm_refl. Qed.

Definition W_864d8 : bv 32 := 0x02000613.
Lemma F_864d8 : fetch_word Ubsan.M.loaded_segments (0x864d8 : word) = Some W_864d8.
Proof. vm_refl. Qed.
Lemma D_864d8 : decode_any W_864d8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_864dc : bv 32 := 0x00cf1463.
Lemma F_864dc : fetch_word Ubsan.M.loaded_segments (0x864dc : word) = Some W_864dc.
Proof. vm_refl. Qed.
Lemma D_864dc : decode_any W_864dc = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_864e0 : bv 32 := 0x814fc06f.
Lemma F_864e0 : fetch_word Ubsan.M.loaded_segments (0x864e0 : word) = Some W_864e0.
Proof. vm_refl. Qed.
Lemma D_864e0 : decode_any W_864e0 = Some (Jal 0 2080788, 4%Z).
Proof. vm_refl. Qed.

Definition W_864e4 : bv 32 := 0x000d2603.
Lemma F_864e4 : fetch_word Ubsan.M.loaded_segments (0x864e4 : word) = Some W_864e4.
Proof. vm_refl. Qed.
Lemma D_864e4 : decode_any W_864e4 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_864e8 : bv 32 := 0x01d61abb.
Lemma F_864e8 : fetch_word Ubsan.M.loaded_segments (0x864e8 : word) = Some W_864e8.
Proof. vm_refl. Qed.
Lemma D_864e8 : decode_any W_864e8 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_864ec : bv 32 := 0x040c1663.
Lemma F_864ec : fetch_word Ubsan.M.loaded_segments (0x864ec : word) = Some W_864ec.
Proof. vm_refl. Qed.
Lemma D_864ec : decode_any W_864ec = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_864f0 : bv 32 := 0xffb00613.
Lemma F_864f0 : fetch_word Ubsan.M.loaded_segments (0x864f0 : word) = Some W_864f0.
Proof. vm_refl. Qed.
Lemma D_864f0 : decode_any W_864f0 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_864f4 : bv 32 := 0x01a67463.
Lemma F_864f4 : fetch_word Ubsan.M.loaded_segments (0x864f4 : word) = Some W_864f4.
Proof. vm_refl. Qed.
Lemma D_864f4 : decode_any W_864f4 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_864f8 : bv 32 := 0xffdfb06f.
Lemma F_864f8 : fetch_word Ubsan.M.loaded_segments (0x864f8 : word) = Some W_864f8.
Proof. vm_refl. Qed.
Lemma D_864f8 : decode_any W_864f8 = Some (Jal 0 2080764, 4%Z).
Proof. vm_refl. Qed.

Definition W_864fc : bv 32 := 0x0080f463.
Lemma F_864fc : fetch_word Ubsan.M.loaded_segments (0x864fc : word) = Some W_864fc.
Proof. vm_refl. Qed.
Lemma D_864fc : decode_any W_864fc = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86500 : bv 32 := 0xff5fb06f.
Lemma F_86500 : fetch_word Ubsan.M.loaded_segments (0x86500 : word) = Some W_86500.
Proof. vm_refl. Qed.
Lemma D_86500 : decode_any W_86500 = Some (Jal 0 2080756, 4%Z).
Proof. vm_refl. Qed.

Definition W_86504 : bv 32 := 0x004d2603.
Lemma F_86504 : fetch_word Ubsan.M.loaded_segments (0x86504 : word) = Some W_86504.
Proof. vm_refl. Qed.
Lemma D_86504 : decode_any W_86504 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86508 : bv 32 := 0x00013883.
Lemma F_86508 : fetch_word Ubsan.M.loaded_segments (0x86508 : word) = Some W_86508.
Proof. vm_refl. Qed.
Lemma D_86508 : decode_any W_86508 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8650c : bv 32 := 0x011af8b3.
Lemma F_8650c : fetch_word Ubsan.M.loaded_segments (0x8650c : word) = Some W_8650c.
Proof. vm_refl. Qed.
Lemma D_8650c : decode_any W_8650c = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86510 : bv 32 := 0x0086563b.
Lemma F_86510 : fetch_word Ubsan.M.loaded_segments (0x86510 : word) = Some W_86510.
Proof. vm_refl. Qed.
Lemma D_86510 : decode_any W_86510 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86514 : bv 32 := 0x01f67633.
Lemma F_86514 : fetch_word Ubsan.M.loaded_segments (0x86514 : word) = Some W_86514.
Proof. vm_refl. Qed.
Lemma D_86514 : decode_any W_86514 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86518 : bv 32 := 0x01166ab3.
Lemma F_86518 : fetch_word Ubsan.M.loaded_segments (0x86518 : word) = Some W_86518.
Proof. vm_refl. Qed.
Lemma D_86518 : decode_any W_86518 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8651c : bv 32 := 0x01c0006f.
Lemma F_8651c : fetch_word Ubsan.M.loaded_segments (0x8651c : word) = Some W_8651c.
Proof. vm_refl. Qed.
Lemma D_8651c : decode_any W_8651c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86520 : bv 32 := 0x00061463.
Lemma F_86520 : fetch_word Ubsan.M.loaded_segments (0x86520 : word) = Some W_86520.
Proof. vm_refl. Qed.
Lemma D_86520 : decode_any W_86520 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86524 : bv 32 := 0xfd1fb06f.
Lemma F_86524 : fetch_word Ubsan.M.loaded_segments (0x86524 : word) = Some W_86524.
Proof. vm_refl. Qed.
Lemma D_86524 : decode_any W_86524 = Some (Jal 0 2080720, 4%Z).
Proof. vm_refl. Qed.

Definition W_86528 : bv 32 := 0x0080f463.
Lemma F_86528 : fetch_word Ubsan.M.loaded_segments (0x86528 : word) = Some W_86528.
Proof. vm_refl. Qed.
Lemma D_86528 : decode_any W_86528 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8652c : bv 32 := 0xfc9fb06f.
Lemma F_8652c : fetch_word Ubsan.M.loaded_segments (0x8652c : word) = Some W_8652c.
Proof. vm_refl. Qed.
Lemma D_8652c : decode_any W_8652c = Some (Jal 0 2080712, 4%Z).
Proof. vm_refl. Qed.

Definition W_86530 : bv 32 := 0x000d2603.
Lemma F_86530 : fetch_word Ubsan.M.loaded_segments (0x86530 : word) = Some W_86530.
Proof. vm_refl. Qed.
Lemma D_86530 : decode_any W_86530 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86534 : bv 32 := 0x00865abb.
Lemma F_86534 : fetch_word Ubsan.M.loaded_segments (0x86534 : word) = Some W_86534.
Proof. vm_refl. Qed.
Lemma D_86534 : decode_any W_86534 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86538 : bv 32 := 0x000b8463.
Lemma F_86538 : fetch_word Ubsan.M.loaded_segments (0x86538 : word) = Some W_86538.
Proof. vm_refl. Qed.
Lemma D_86538 : decode_any W_86538 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8653c : bv 32 := 0xfb9fb06f.
Lemma F_8653c : fetch_word Ubsan.M.loaded_segments (0x8653c : word) = Some W_8653c.
Proof. vm_refl. Qed.
Lemma D_8653c : decode_any W_8653c = Some (Jal 0 2080696, 4%Z).
Proof. vm_refl. Qed.

Definition W_86540 : bv 32 := 0x000c9463.
Lemma F_86540 : fetch_word Ubsan.M.loaded_segments (0x86540 : word) = Some W_86540.
Proof. vm_refl. Qed.
Lemma D_86540 : decode_any W_86540 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86544 : bv 32 := 0xfb1fb06f.
Lemma F_86544 : fetch_word Ubsan.M.loaded_segments (0x86544 : word) = Some W_86544.
Proof. vm_refl. Qed.
Lemma D_86544 : decode_any W_86544 = Some (Jal 0 2080688, 4%Z).
Proof. vm_refl. Qed.

Definition W_86548 : bv 32 := 0x000ca603.
Lemma F_86548 : fetch_word Ubsan.M.loaded_segments (0x86548 : word) = Some W_86548.
Proof. vm_refl. Qed.
Lemma D_86548 : decode_any W_86548 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8654c : bv 32 := 0x005678b3.
Lemma F_8654c : fetch_word Ubsan.M.loaded_segments (0x8654c : word) = Some W_8654c.
Proof. vm_refl. Qed.
Lemma D_8654c : decode_any W_8654c = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86550 : bv 32 := 0xfff64613.
Lemma F_86550 : fetch_word Ubsan.M.loaded_segments (0x86550 : word) = Some W_86550.
Proof. vm_refl. Qed.
Lemma D_86550 : decode_any W_86550 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86554 : bv 32 := 0x01b67633.
Lemma F_86554 : fetch_word Ubsan.M.loaded_segments (0x86554 : word) = Some W_86554.
Proof. vm_refl. Qed.
Lemma D_86554 : decode_any W_86554 = Some (Op ALU_AND 12 12 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86558 : bv 32 := 0x00caf633.
Lemma F_86558 : fetch_word Ubsan.M.loaded_segments (0x86558 : word) = Some W_86558.
Proof. vm_refl. Qed.
Lemma D_86558 : decode_any W_86558 = Some (Op ALU_AND 12 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8655c : bv 32 := 0x01166633.
Lemma F_8655c : fetch_word Ubsan.M.loaded_segments (0x8655c : word) = Some W_8655c.
Proof. vm_refl. Qed.
Lemma D_8655c : decode_any W_8655c = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86560 : bv 32 := 0x01038ab3.
Lemma F_86560 : fetch_word Ubsan.M.loaded_segments (0x86560 : word) = Some W_86560.
Proof. vm_refl. Qed.
Lemma D_86560 : decode_any W_86560 = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86564 : bv 32 := 0x00cca023.
Lemma F_86564 : fetch_word Ubsan.M.loaded_segments (0x86564 : word) = Some W_86564.
Proof. vm_refl. Qed.
Lemma D_86564 : decode_any W_86564 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86568 : bv 32 := 0x000a9463.
Lemma F_86568 : fetch_word Ubsan.M.loaded_segments (0x86568 : word) = Some W_86568.
Proof. vm_refl. Qed.
Lemma D_86568 : decode_any W_86568 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8656c : bv 32 := 0xf89fb06f.
Lemma F_8656c : fetch_word Ubsan.M.loaded_segments (0x8656c : word) = Some W_8656c.
Proof. vm_refl. Qed.
Lemma D_8656c : decode_any W_8656c = Some (Jal 0 2080648, 4%Z).
Proof. vm_refl. Qed.

Definition W_86570 : bv 32 := 0x010ab633.
Lemma F_86570 : fetch_word Ubsan.M.loaded_segments (0x86570 : word) = Some W_86570.
Proof. vm_refl. Qed.
Lemma D_86570 : decode_any W_86570 = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86574 : bv 32 := 0x00964633.
Lemma F_86574 : fetch_word Ubsan.M.loaded_segments (0x86574 : word) = Some W_86574.
Proof. vm_refl. Qed.
Lemma D_86574 : decode_any W_86574 = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86578 : bv 32 := 0x00164613.
Lemma F_86578 : fetch_word Ubsan.M.loaded_segments (0x86578 : word) = Some W_86578.
Proof. vm_refl. Qed.
Lemma D_86578 : decode_any W_86578 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8657c : bv 32 := 0x00061463.
Lemma F_8657c : fetch_word Ubsan.M.loaded_segments (0x8657c : word) = Some W_8657c.
Proof. vm_refl. Qed.
Lemma D_8657c : decode_any W_8657c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86580 : bv 32 := 0xf75fb06f.
Lemma F_86580 : fetch_word Ubsan.M.loaded_segments (0x86580 : word) = Some W_86580.
Proof. vm_refl. Qed.
Lemma D_86580 : decode_any W_86580 = Some (Jal 0 2080628, 4%Z).
Proof. vm_refl. Qed.

Definition W_86584 : bv 32 := 0x00ba0633.
Lemma F_86584 : fetch_word Ubsan.M.loaded_segments (0x86584 : word) = Some W_86584.
Proof. vm_refl. Qed.
Lemma D_86584 : decode_any W_86584 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86588 : bv 32 := 0x00061463.
Lemma F_86588 : fetch_word Ubsan.M.loaded_segments (0x86588 : word) = Some W_86588.
Proof. vm_refl. Qed.
Lemma D_86588 : decode_any W_86588 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8658c : bv 32 := 0xf69fb06f.
Lemma F_8658c : fetch_word Ubsan.M.loaded_segments (0x8658c : word) = Some W_8658c.
Proof. vm_refl. Qed.
Lemma D_8658c : decode_any W_8658c = Some (Jal 0 2080616, 4%Z).
Proof. vm_refl. Qed.

Definition W_86590 : bv 32 := 0x01a63633.
Lemma F_86590 : fetch_word Ubsan.M.loaded_segments (0x86590 : word) = Some W_86590.
Proof. vm_refl. Qed.
Lemma D_86590 : decode_any W_86590 = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86594 : bv 32 := 0x07813803.
Lemma F_86594 : fetch_word Ubsan.M.loaded_segments (0x86594 : word) = Some W_86594.
Proof. vm_refl. Qed.
Lemma D_86594 : decode_any W_86594 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86598 : bv 32 := 0x01064633.
Lemma F_86598 : fetch_word Ubsan.M.loaded_segments (0x86598 : word) = Some W_86598.
Proof. vm_refl. Qed.
Lemma D_86598 : decode_any W_86598 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8659c : bv 32 := 0x00164613.
Lemma F_8659c : fetch_word Ubsan.M.loaded_segments (0x8659c : word) = Some W_8659c.
Proof. vm_refl. Qed.
Lemma D_8659c : decode_any W_8659c = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_865a0 : bv 32 := 0x00061463.
Lemma F_865a0 : fetch_word Ubsan.M.loaded_segments (0x865a0 : word) = Some W_865a0.
Proof. vm_refl. Qed.
Lemma D_865a0 : decode_any W_865a0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_865a4 : bv 32 := 0xf51fb06f.
Lemma F_865a4 : fetch_word Ubsan.M.loaded_segments (0x865a4 : word) = Some W_865a4.
Proof. vm_refl. Qed.
Lemma D_865a4 : decode_any W_865a4 = Some (Jal 0 2080592, 4%Z).
Proof. vm_refl. Qed.

Definition W_865a8 : bv 32 := 0x001e0e1b.
Lemma F_865a8 : fetch_word Ubsan.M.loaded_segments (0x865a8 : word) = Some W_865a8.
Proof. vm_refl. Qed.
Lemma D_865a8 : decode_any W_865a8 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_865ac : bv 32 := 0x00d585b3.
Lemma F_865ac : fetch_word Ubsan.M.loaded_segments (0x865ac : word) = Some W_865ac.
Proof. vm_refl. Qed.
Lemma D_865ac : decode_any W_865ac = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_865b0 : bv 32 := 0x007c8cb3.
Lemma F_865b0 : fetch_word Ubsan.M.loaded_segments (0x865b0 : word) = Some W_865b0.
Proof. vm_refl. Qed.
Lemma D_865b0 : decode_any W_865b0 = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_865b4 : bv 32 := 0x000a8813.
Lemma F_865b4 : fetch_word Ubsan.M.loaded_segments (0x865b4 : word) = Some W_865b4.
Proof. vm_refl. Qed.
Lemma D_865b4 : decode_any W_865b4 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_865b8 : bv 32 := 0xf00e14e3.
Lemma F_865b8 : fetch_word Ubsan.M.loaded_segments (0x865b8 : word) = Some W_865b8.
Proof. vm_refl. Qed.
Lemma D_865b8 : decode_any W_865b8 = Some (Branch BC_NE 28 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_865bc : bv 32 := 0x02013583.
Lemma F_865bc : fetch_word Ubsan.M.loaded_segments (0x865bc : word) = Some W_865bc.
Proof. vm_refl. Qed.
Lemma D_865bc : decode_any W_865bc = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_865c0 : bv 32 := 0x16059e63.
Lemma F_865c0 : fetch_word Ubsan.M.loaded_segments (0x865c0 : word) = Some W_865c0.
Proof. vm_refl. Qed.
Lemma D_865c0 : decode_any W_865c0 = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_865c4 : bv 32 := 0xffffc693.
Lemma F_865c4 : fetch_word Ubsan.M.loaded_segments (0x865c4 : word) = Some W_865c4.
Proof. vm_refl. Qed.
Lemma D_865c4 : decode_any W_865c4 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_865c8 : bv 32 := 0x00271293.
Lemma F_865c8 : fetch_word Ubsan.M.loaded_segments (0x865c8 : word) = Some W_865c8.
Proof. vm_refl. Qed.
Lemma D_865c8 : decode_any W_865c8 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_865cc : bv 32 := 0x05813383.
Lemma F_865cc : fetch_word Ubsan.M.loaded_segments (0x865cc : word) = Some W_865cc.
Proof. vm_refl. Qed.
Lemma D_865cc : decode_any W_865cc = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_865d0 : bv 32 := 0x00239393.
Lemma F_865d0 : fetch_word Ubsan.M.loaded_segments (0x865d0 : word) = Some W_865d0.
Proof. vm_refl. Qed.
Lemma D_865d0 : decode_any W_865d0 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_865d4 : bv 32 := 0x00337613.
Lemma F_865d4 : fetch_word Ubsan.M.loaded_segments (0x865d4 : word) = Some W_865d4.
Proof. vm_refl. Qed.
Lemma D_865d4 : decode_any W_865d4 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_865d8 : bv 32 := 0x00397793.
Lemma F_865d8 : fetch_word Ubsan.M.loaded_segments (0x865d8 : word) = Some W_865d8.
Proof. vm_refl. Qed.
Lemma D_865d8 : decode_any W_865d8 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_865dc : bv 32 := 0x07013a03.
Lemma F_865dc : fetch_word Ubsan.M.loaded_segments (0x865dc : word) = Some W_865dc.
Proof. vm_refl. Qed.
Lemma D_865dc : decode_any W_865dc = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_865e0 : bv 32 := 0x002a1a13.
Lemma F_865e0 : fetch_word Ubsan.M.loaded_segments (0x865e0 : word) = Some W_865e0.
Proof. vm_refl. Qed.
Lemma D_865e0 : decode_any W_865e0 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_865e4 : bv 32 := 0x00072b93.
Lemma F_865e4 : fetch_word Ubsan.M.loaded_segments (0x865e4 : word) = Some W_865e4.
Proof. vm_refl. Qed.
Lemma D_865e4 : decode_any W_865e4 = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_865e8 : bv 32 := 0x02000c93.
Lemma F_865e8 : fetch_word Ubsan.M.loaded_segments (0x865e8 : word) = Some W_865e8.
Proof. vm_refl. Qed.
Lemma D_865e8 : decode_any W_865e8 = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_865ec : bv 32 := 0xffb00d13.
Lemma F_865ec : fetch_word Ubsan.M.loaded_segments (0x865ec : word) = Some W_865ec.
Proof. vm_refl. Qed.
Lemma D_865ec : decode_any W_865ec = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_865f0 : bv 32 := 0x0017b793.
Lemma F_865f0 : fetch_word Ubsan.M.loaded_segments (0x865f0 : word) = Some W_865f0.
Proof. vm_refl. Qed.
Lemma D_865f0 : decode_any W_865f0 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_865f4 : bv 32 := 0x02f13023.
Lemma F_865f4 : fetch_word Ubsan.M.loaded_segments (0x865f4 : word) = Some W_865f4.
Proof. vm_refl. Qed.
Lemma D_865f4 : decode_any W_865f4 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_865f8 : bv 32 := 0x00163613.
Lemma F_865f8 : fetch_word Ubsan.M.loaded_segments (0x865f8 : word) = Some W_865f8.
Proof. vm_refl. Qed.
Lemma D_865f8 : decode_any W_865f8 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_865fc : bv 32 := 0x00c13823.
Lemma F_865fc : fetch_word Ubsan.M.loaded_segments (0x865fc : word) = Some W_865fc.
Proof. vm_refl. Qed.
Lemma D_865fc : decode_any W_865fc = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86600 : bv 32 := 0x01f00993.
Lemma F_86600 : fetch_word Ubsan.M.loaded_segments (0x86600 : word) = Some W_86600.
Proof. vm_refl. Qed.
Lemma D_86600 : decode_any W_86600 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86604 : bv 32 := 0x00030b13.
Lemma F_86604 : fetch_word Ubsan.M.loaded_segments (0x86604 : word) = Some W_86604.
Proof. vm_refl. Qed.
Lemma D_86604 : decode_any W_86604 = Some (OpImm ALU_ADD 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86608 : bv 32 := 0x00090c13.
Lemma F_86608 : fetch_word Ubsan.M.loaded_segments (0x86608 : word) = Some W_86608.
Proof. vm_refl. Qed.
Lemma D_86608 : decode_any W_86608 = Some (OpImm ALU_ADD 24 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8660c : bv 32 := 0x07013603.
Lemma F_8660c : fetch_word Ubsan.M.loaded_segments (0x8660c : word) = Some W_8660c.
Proof. vm_refl. Qed.
Lemma D_8660c : decode_any W_8660c = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_86610 : bv 32 := 0x0a060e63.
Lemma F_86610 : fetch_word Ubsan.M.loaded_segments (0x86610 : word) = Some W_86610.
Proof. vm_refl. Qed.
Lemma D_86610 : decode_any W_86610 = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_86614 : bv 32 := 0x00000d93.
Lemma F_86614 : fetch_word Ubsan.M.loaded_segments (0x86614 : word) = Some W_86614.
Proof. vm_refl. Qed.
Lemma D_86614 : decode_any W_86614 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86618 : bv 32 := 0x00603833.
Lemma F_86618 : fetch_word Ubsan.M.loaded_segments (0x86618 : word) = Some W_86618.
Proof. vm_refl. Qed.
Lemma D_86618 : decode_any W_86618 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8661c : bv 32 := 0x01203e33.
Lemma F_8661c : fetch_word Ubsan.M.loaded_segments (0x8661c : word) = Some W_8661c.
Proof. vm_refl. Qed.
Lemma D_8661c : decode_any W_8661c = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86620 : bv 32 := 0x01013603.
Lemma F_86620 : fetch_word Ubsan.M.loaded_segments (0x86620 : word) = Some W_86620.
Proof. vm_refl. Qed.
Lemma D_86620 : decode_any W_86620 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86624 : bv 32 := 0x010674b3.
Lemma F_86624 : fetch_word Ubsan.M.loaded_segments (0x86624 : word) = Some W_86624.
Proof. vm_refl. Qed.
Lemma D_86624 : decode_any W_86624 = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86628 : bv 32 := 0x02013603.
Lemma F_86628 : fetch_word Ubsan.M.loaded_segments (0x86628 : word) = Some W_86628.
Proof. vm_refl. Qed.
Lemma D_86628 : decode_any W_86628 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8662c : bv 32 := 0x01c67ab3.
Lemma F_8662c : fetch_word Ubsan.M.loaded_segments (0x8662c : word) = Some W_8662c.
Proof. vm_refl. Qed.
Lemma D_8662c : decode_any W_8662c = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86630 : bv 32 := 0x01bb0633.
Lemma F_86630 : fetch_word Ubsan.M.loaded_segments (0x86630 : word) = Some W_86630.
Proof. vm_refl. Qed.
Lemma D_86630 : decode_any W_86630 = Some (Op ALU_ADD 12 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86634 : bv 32 := 0x00667463.
Lemma F_86634 : fetch_word Ubsan.M.loaded_segments (0x86634 : word) = Some W_86634.
Proof. vm_refl. Qed.
Lemma D_86634 : decode_any W_86634 = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86638 : bv 32 := 0xebdfb06f.
Lemma F_86638 : fetch_word Ubsan.M.loaded_segments (0x86638 : word) = Some W_86638.
Proof. vm_refl. Qed.
Lemma D_86638 : decode_any W_86638 = Some (Jal 0 2080444, 4%Z).
Proof. vm_refl. Qed.

Definition W_8663c : bv 32 := 0x00163613.
Lemma F_8663c : fetch_word Ubsan.M.loaded_segments (0x8663c : word) = Some W_8663c.
Proof. vm_refl. Qed.
Lemma D_8663c : decode_any W_8663c = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86640 : bv 32 := 0x00c84633.
Lemma F_86640 : fetch_word Ubsan.M.loaded_segments (0x86640 : word) = Some W_86640.
Proof. vm_refl. Qed.
Lemma D_86640 : decode_any W_86640 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86644 : bv 32 := 0x00061463.
Lemma F_86644 : fetch_word Ubsan.M.loaded_segments (0x86644 : word) = Some W_86644.
Proof. vm_refl. Qed.
Lemma D_86644 : decode_any W_86644 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86648 : bv 32 := 0xeadfb06f.
Lemma F_86648 : fetch_word Ubsan.M.loaded_segments (0x86648 : word) = Some W_86648.
Proof. vm_refl. Qed.
Lemma D_86648 : decode_any W_86648 = Some (Jal 0 2080428, 4%Z).
Proof. vm_refl. Qed.

Definition W_8664c : bv 32 := 0x00049463.
Lemma F_8664c : fetch_word Ubsan.M.loaded_segments (0x8664c : word) = Some W_8664c.
Proof. vm_refl. Qed.
Lemma D_8664c : decode_any W_8664c = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86650 : bv 32 := 0xea5fb06f.
Lemma F_86650 : fetch_word Ubsan.M.loaded_segments (0x86650 : word) = Some W_86650.
Proof. vm_refl. Qed.
Lemma D_86650 : decode_any W_86650 = Some (Jal 0 2080420, 4%Z).
Proof. vm_refl. Qed.

Definition W_86654 : bv 32 := 0x019f1463.
Lemma F_86654 : fetch_word Ubsan.M.loaded_segments (0x86654 : word) = Some W_86654.
Proof. vm_refl. Qed.
Lemma D_86654 : decode_any W_86654 = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86658 : bv 32 := 0xe9dfb06f.
Lemma F_86658 : fetch_word Ubsan.M.loaded_segments (0x86658 : word) = Some W_86658.
Proof. vm_refl. Qed.
Lemma D_86658 : decode_any W_86658 = Some (Jal 0 2080412, 4%Z).
Proof. vm_refl. Qed.

Definition W_8665c : bv 32 := 0x01b30633.
Lemma F_8665c : fetch_word Ubsan.M.loaded_segments (0x8665c : word) = Some W_8665c.
Proof. vm_refl. Qed.
Lemma D_8665c : decode_any W_8665c = Some (Op ALU_ADD 12 6 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86660 : bv 32 := 0x00cd7463.
Lemma F_86660 : fetch_word Ubsan.M.loaded_segments (0x86660 : word) = Some W_86660.
Proof. vm_refl. Qed.
Lemma D_86660 : decode_any W_86660 = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86664 : bv 32 := 0xe91fb06f.
Lemma F_86664 : fetch_word Ubsan.M.loaded_segments (0x86664 : word) = Some W_86664.
Proof. vm_refl. Qed.
Lemma D_86664 : decode_any W_86664 = Some (Jal 0 2080400, 4%Z).
Proof. vm_refl. Qed.

Definition W_86668 : bv 32 := 0x0089f463.
Lemma F_86668 : fetch_word Ubsan.M.loaded_segments (0x86668 : word) = Some W_86668.
Proof. vm_refl. Qed.
Lemma D_86668 : decode_any W_86668 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8666c : bv 32 := 0xe89fb06f.
Lemma F_8666c : fetch_word Ubsan.M.loaded_segments (0x8666c : word) = Some W_8666c.
Proof. vm_refl. Qed.
Lemma D_8666c : decode_any W_8666c = Some (Jal 0 2080392, 4%Z).
Proof. vm_refl. Qed.

Definition W_86670 : bv 32 := 0x01bc07b3.
Lemma F_86670 : fetch_word Ubsan.M.loaded_segments (0x86670 : word) = Some W_86670.
Proof. vm_refl. Qed.
Lemma D_86670 : decode_any W_86670 = Some (Op ALU_ADD 15 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86674 : bv 32 := 0x0127f463.
Lemma F_86674 : fetch_word Ubsan.M.loaded_segments (0x86674 : word) = Some W_86674.
Proof. vm_refl. Qed.
Lemma D_86674 : decode_any W_86674 = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86678 : bv 32 := 0xe7dfb06f.
Lemma F_86678 : fetch_word Ubsan.M.loaded_segments (0x86678 : word) = Some W_86678.
Proof. vm_refl. Qed.
Lemma D_86678 : decode_any W_86678 = Some (Jal 0 2080380, 4%Z).
Proof. vm_refl. Qed.

Definition W_8667c : bv 32 := 0x0017b793.
Lemma F_8667c : fetch_word Ubsan.M.loaded_segments (0x8667c : word) = Some W_8667c.
Proof. vm_refl. Qed.
Lemma D_8667c : decode_any W_8667c = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86680 : bv 32 := 0x00fe47b3.
Lemma F_86680 : fetch_word Ubsan.M.loaded_segments (0x86680 : word) = Some W_86680.
Proof. vm_refl. Qed.
Lemma D_86680 : decode_any W_86680 = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86684 : bv 32 := 0x00079463.
Lemma F_86684 : fetch_word Ubsan.M.loaded_segments (0x86684 : word) = Some W_86684.
Proof. vm_refl. Qed.
Lemma D_86684 : decode_any W_86684 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86688 : bv 32 := 0xe6dfb06f.
Lemma F_86688 : fetch_word Ubsan.M.loaded_segments (0x86688 : word) = Some W_86688.
Proof. vm_refl. Qed.
Lemma D_86688 : decode_any W_86688 = Some (Jal 0 2080364, 4%Z).
Proof. vm_refl. Qed.

Definition W_8668c : bv 32 := 0x000a9463.
Lemma F_8668c : fetch_word Ubsan.M.loaded_segments (0x8668c : word) = Some W_8668c.
Proof. vm_refl. Qed.
Lemma D_8668c : decode_any W_8668c = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86690 : bv 32 := 0xe65fb06f.
Lemma F_86690 : fetch_word Ubsan.M.loaded_segments (0x86690 : word) = Some W_86690.
Proof. vm_refl. Qed.
Lemma D_86690 : decode_any W_86690 = Some (Jal 0 2080356, 4%Z).
Proof. vm_refl. Qed.

Definition W_86694 : bv 32 := 0x00062783.
Lemma F_86694 : fetch_word Ubsan.M.loaded_segments (0x86694 : word) = Some W_86694.
Proof. vm_refl. Qed.
Lemma D_86694 : decode_any W_86694 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86698 : bv 32 := 0x00462603.
Lemma F_86698 : fetch_word Ubsan.M.loaded_segments (0x86698 : word) = Some W_86698.
Proof. vm_refl. Qed.
Lemma D_86698 : decode_any W_86698 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8669c : bv 32 := 0x01b908b3.
Lemma F_8669c : fetch_word Ubsan.M.loaded_segments (0x8669c : word) = Some W_8669c.
Proof. vm_refl. Qed.
Lemma D_8669c : decode_any W_8669c = Some (Op ALU_ADD 17 18 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_866a0 : bv 32 := 0x0008a083.
Lemma F_866a0 : fetch_word Ubsan.M.loaded_segments (0x866a0 : word) = Some W_866a0.
Proof. vm_refl. Qed.
Lemma D_866a0 : decode_any W_866a0 = Some (Load SZ4 true 1 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_866a4 : bv 32 := 0x01d797bb.
Lemma F_866a4 : fetch_word Ubsan.M.loaded_segments (0x866a4 : word) = Some W_866a4.
Proof. vm_refl. Qed.
Lemma D_866a4 : decode_any W_866a4 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_866a8 : bv 32 := 0x0086563b.
Lemma F_866a8 : fetch_word Ubsan.M.loaded_segments (0x866a8 : word) = Some W_866a8.
Proof. vm_refl. Qed.
Lemma D_866a8 : decode_any W_866a8 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_866ac : bv 32 := 0x00d7f7b3.
Lemma F_866ac : fetch_word Ubsan.M.loaded_segments (0x866ac : word) = Some W_866ac.
Proof. vm_refl. Qed.
Lemma D_866ac : decode_any W_866ac = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_866b0 : bv 32 := 0x01f67633.
Lemma F_866b0 : fetch_word Ubsan.M.loaded_segments (0x866b0 : word) = Some W_866b0.
Proof. vm_refl. Qed.
Lemma D_866b0 : decode_any W_866b0 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_866b4 : bv 32 := 0x00f66633.
Lemma F_866b4 : fetch_word Ubsan.M.loaded_segments (0x866b4 : word) = Some W_866b4.
Proof. vm_refl. Qed.
Lemma D_866b4 : decode_any W_866b4 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_866b8 : bv 32 := 0xfff0c793.
Lemma F_866b8 : fetch_word Ubsan.M.loaded_segments (0x866b8 : word) = Some W_866b8.
Proof. vm_refl. Qed.
Lemma D_866b8 : decode_any W_866b8 = Some (OpImm ALU_XOR 15 1 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_866bc : bv 32 := 0x00f67633.
Lemma F_866bc : fetch_word Ubsan.M.loaded_segments (0x866bc : word) = Some W_866bc.
Proof. vm_refl. Qed.
Lemma D_866bc : decode_any W_866bc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_866c0 : bv 32 := 0x004d8d93.
Lemma F_866c0 : fetch_word Ubsan.M.loaded_segments (0x866c0 : word) = Some W_866c0.
Proof. vm_refl. Qed.
Lemma D_866c0 : decode_any W_866c0 = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_866c4 : bv 32 := 0x00c8a023.
Lemma F_866c4 : fetch_word Ubsan.M.loaded_segments (0x866c4 : word) = Some W_866c4.
Proof. vm_refl. Qed.
Lemma D_866c4 : decode_any W_866c4 = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_866c8 : bv 32 := 0xf7ba14e3.
Lemma F_866c8 : fetch_word Ubsan.M.loaded_segments (0x866c8 : word) = Some W_866c8.
Proof. vm_refl. Qed.
Lemma D_866c8 : decode_any W_866c8 = Some (Branch BC_NE 20 27 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_866cc : bv 32 := 0x00590633.
Lemma F_866cc : fetch_word Ubsan.M.loaded_segments (0x866cc : word) = Some W_866cc.
Proof. vm_refl. Qed.
Lemma D_866cc : decode_any W_866cc = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_866d0 : bv 32 := 0x012037b3.
Lemma F_866d0 : fetch_word Ubsan.M.loaded_segments (0x866d0 : word) = Some W_866d0.
Proof. vm_refl. Qed.
Lemma D_866d0 : decode_any W_866d0 = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_866d4 : bv 32 := 0x00163813.
Lemma F_866d4 : fetch_word Ubsan.M.loaded_segments (0x866d4 : word) = Some W_866d4.
Proof. vm_refl. Qed.
Lemma D_866d4 : decode_any W_866d4 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_866d8 : bv 32 := 0x01079463.
Lemma F_866d8 : fetch_word Ubsan.M.loaded_segments (0x866d8 : word) = Some W_866d8.
Proof. vm_refl. Qed.
Lemma D_866d8 : decode_any W_866d8 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_866dc : bv 32 := 0xe19fb06f.
Lemma F_866dc : fetch_word Ubsan.M.loaded_segments (0x866dc : word) = Some W_866dc.
Proof. vm_refl. Qed.
Lemma D_866dc : decode_any W_866dc = Some (Jal 0 2080280, 4%Z).
Proof. vm_refl. Qed.

Definition W_866e0 : bv 32 := 0x01263633.
Lemma F_866e0 : fetch_word Ubsan.M.loaded_segments (0x866e0 : word) = Some W_866e0.
Proof. vm_refl. Qed.
Lemma D_866e0 : decode_any W_866e0 = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_866e4 : bv 32 := 0x01764633.
Lemma F_866e4 : fetch_word Ubsan.M.loaded_segments (0x866e4 : word) = Some W_866e4.
Proof. vm_refl. Qed.
Lemma D_866e4 : decode_any W_866e4 = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_866e8 : bv 32 := 0x00164613.
Lemma F_866e8 : fetch_word Ubsan.M.loaded_segments (0x866e8 : word) = Some W_866e8.
Proof. vm_refl. Qed.
Lemma D_866e8 : decode_any W_866e8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_866ec : bv 32 := 0x00061463.
Lemma F_866ec : fetch_word Ubsan.M.loaded_segments (0x866ec : word) = Some W_866ec.
Proof. vm_refl. Qed.
Lemma D_866ec : decode_any W_866ec = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_866f0 : bv 32 := 0xe05fb06f.
Lemma F_866f0 : fetch_word Ubsan.M.loaded_segments (0x866f0 : word) = Some W_866f0.
Proof. vm_refl. Qed.
Lemma D_866f0 : decode_any W_866f0 = Some (Jal 0 2080260, 4%Z).
Proof. vm_refl. Qed.

Definition W_866f4 : bv 32 := 0x00638633.
Lemma F_866f4 : fetch_word Ubsan.M.loaded_segments (0x866f4 : word) = Some W_866f4.
Proof. vm_refl. Qed.
Lemma D_866f4 : decode_any W_866f4 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_866f8 : bv 32 := 0x006037b3.
Lemma F_866f8 : fetch_word Ubsan.M.loaded_segments (0x866f8 : word) = Some W_866f8.
Proof. vm_refl. Qed.
Lemma D_866f8 : decode_any W_866f8 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_866fc : bv 32 := 0x00163813.
Lemma F_866fc : fetch_word Ubsan.M.loaded_segments (0x866fc : word) = Some W_866fc.
Proof. vm_refl. Qed.
Lemma D_866fc : decode_any W_866fc = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86700 : bv 32 := 0x01079463.
Lemma F_86700 : fetch_word Ubsan.M.loaded_segments (0x86700 : word) = Some W_86700.
Proof. vm_refl. Qed.
Lemma D_86700 : decode_any W_86700 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86704 : bv 32 := 0xdf1fb06f.
Lemma F_86704 : fetch_word Ubsan.M.loaded_segments (0x86704 : word) = Some W_86704.
Proof. vm_refl. Qed.
Lemma D_86704 : decode_any W_86704 = Some (Jal 0 2080240, 4%Z).
Proof. vm_refl. Qed.

Definition W_86708 : bv 32 := 0x006637b3.
Lemma F_86708 : fetch_word Ubsan.M.loaded_segments (0x86708 : word) = Some W_86708.
Proof. vm_refl. Qed.
Lemma D_86708 : decode_any W_86708 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8670c : bv 32 := 0x07813803.
Lemma F_8670c : fetch_word Ubsan.M.loaded_segments (0x8670c : word) = Some W_8670c.
Proof. vm_refl. Qed.
Lemma D_8670c : decode_any W_8670c = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86710 : bv 32 := 0x0107c7b3.
Lemma F_86710 : fetch_word Ubsan.M.loaded_segments (0x86710 : word) = Some W_86710.
Proof. vm_refl. Qed.
Lemma D_86710 : decode_any W_86710 = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86714 : bv 32 := 0x0017c793.
Lemma F_86714 : fetch_word Ubsan.M.loaded_segments (0x86714 : word) = Some W_86714.
Proof. vm_refl. Qed.
Lemma D_86714 : decode_any W_86714 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86718 : bv 32 := 0x00079463.
Lemma F_86718 : fetch_word Ubsan.M.loaded_segments (0x86718 : word) = Some W_86718.
Proof. vm_refl. Qed.
Lemma D_86718 : decode_any W_86718 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8671c : bv 32 := 0xdd9fb06f.
Lemma F_8671c : fetch_word Ubsan.M.loaded_segments (0x8671c : word) = Some W_8671c.
Proof. vm_refl. Qed.
Lemma D_8671c : decode_any W_8671c = Some (Jal 0 2080216, 4%Z).
Proof. vm_refl. Qed.

Definition W_86720 : bv 32 := 0x00590933.
Lemma F_86720 : fetch_word Ubsan.M.loaded_segments (0x86720 : word) = Some W_86720.
Proof. vm_refl. Qed.
Lemma D_86720 : decode_any W_86720 = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86724 : bv 32 := 0x0015859b.
Lemma F_86724 : fetch_word Ubsan.M.loaded_segments (0x86724 : word) = Some W_86724.
Proof. vm_refl. Qed.
Lemma D_86724 : decode_any W_86724 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86728 : bv 32 := 0x005c0c33.
Lemma F_86728 : fetch_word Ubsan.M.loaded_segments (0x86728 : word) = Some W_86728.
Proof. vm_refl. Qed.
Lemma D_86728 : decode_any W_86728 = Some (Op ALU_ADD 24 24 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8672c : bv 32 := 0x007b0b33.
Lemma F_8672c : fetch_word Ubsan.M.loaded_segments (0x8672c : word) = Some W_8672c.
Proof. vm_refl. Qed.
Lemma D_8672c : decode_any W_8672c = Some (Op ALU_ADD 22 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86730 : bv 32 := 0x00060313.
Lemma F_86730 : fetch_word Ubsan.M.loaded_segments (0x86730 : word) = Some W_86730.
Proof. vm_refl. Qed.
Lemma D_86730 : decode_any W_86730 = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86734 : bv 32 := 0x08013603.
Lemma F_86734 : fetch_word Ubsan.M.loaded_segments (0x86734 : word) = Some W_86734.
Proof. vm_refl. Qed.
Lemma D_86734 : decode_any W_86734 = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_86738 : bv 32 := 0xecc59ae3.
Lemma F_86738 : fetch_word Ubsan.M.loaded_segments (0x86738 : word) = Some W_86738.
Proof. vm_refl. Qed.
Lemma D_86738 : decode_any W_86738 = Some (Branch BC_NE 11 12 7892, 4%Z).
Proof. vm_refl. Qed.

Definition W_8673c : bv 32 := 0x01813583.
Lemma F_8673c : fetch_word Ubsan.M.loaded_segments (0x8673c : word) = Some W_8673c.
Proof. vm_refl. Qed.
Lemma D_8673c : decode_any W_8673c = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86740 : bv 32 := 0x66059ce3.
Lemma F_86740 : fetch_word Ubsan.M.loaded_segments (0x86740 : word) = Some W_86740.
Proof. vm_refl. Qed.
Lemma D_86740 : decode_any W_86740 = Some (Branch BC_NE 11 0 3704, 4%Z).
Proof. vm_refl. Qed.

Definition W_86744 : bv 32 := 0x06813583.
Lemma F_86744 : fetch_word Ubsan.M.loaded_segments (0x86744 : word) = Some W_86744.
Proof. vm_refl. Qed.
Lemma D_86744 : decode_any W_86744 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86748 : bv 32 := 0x0035f593.
Lemma F_86748 : fetch_word Ubsan.M.loaded_segments (0x86748 : word) = Some W_86748.
Proof. vm_refl. Qed.
Lemma D_86748 : decode_any W_86748 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8674c : bv 32 := 0x00058463.
Lemma F_8674c : fetch_word Ubsan.M.loaded_segments (0x8674c : word) = Some W_8674c.
Proof. vm_refl. Qed.
Lemma D_8674c : decode_any W_8674c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86750 : bv 32 := 0xda5fb06f.
Lemma F_86750 : fetch_word Ubsan.M.loaded_segments (0x86750 : word) = Some W_86750.
Proof. vm_refl. Qed.
Lemma D_86750 : decode_any W_86750 = Some (Jal 0 2080164, 4%Z).
Proof. vm_refl. Qed.

Definition W_86754 : bv 32 := 0xffffc613.
Lemma F_86754 : fetch_word Ubsan.M.loaded_segments (0x86754 : word) = Some W_86754.
Proof. vm_refl. Qed.
Lemma D_86754 : decode_any W_86754 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86758 : bv 32 := 0x06013683.
Lemma F_86758 : fetch_word Ubsan.M.loaded_segments (0x86758 : word) = Some W_86758.
Proof. vm_refl. Qed.
Lemma D_86758 : decode_any W_86758 = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8675c : bv 32 := 0xfff6c693.
Lemma F_8675c : fetch_word Ubsan.M.loaded_segments (0x8675c : word) = Some W_8675c.
Proof. vm_refl. Qed.
Lemma D_8675c : decode_any W_8675c = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86760 : bv 32 := 0x00271793.
Lemma F_86760 : fetch_word Ubsan.M.loaded_segments (0x86760 : word) = Some W_86760.
Proof. vm_refl. Qed.
Lemma D_86760 : decode_any W_86760 = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86764 : bv 32 := 0x05813303.
Lemma F_86764 : fetch_word Ubsan.M.loaded_segments (0x86764 : word) = Some W_86764.
Proof. vm_refl. Qed.
Lemma D_86764 : decode_any W_86764 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_86768 : bv 32 := 0x00231313.
Lemma F_86768 : fetch_word Ubsan.M.loaded_segments (0x86768 : word) = Some W_86768.
Proof. vm_refl. Qed.
Lemma D_86768 : decode_any W_86768 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8676c : bv 32 := 0x00357893.
Lemma F_8676c : fetch_word Ubsan.M.loaded_segments (0x8676c : word) = Some W_8676c.
Proof. vm_refl. Qed.
Lemma D_8676c : decode_any W_8676c = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86770 : bv 32 := 0x05013903.
Lemma F_86770 : fetch_word Ubsan.M.loaded_segments (0x86770 : word) = Some W_86770.
Proof. vm_refl. Qed.
Lemma D_86770 : decode_any W_86770 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_86774 : bv 32 := 0x02813803.
Lemma F_86774 : fetch_word Ubsan.M.loaded_segments (0x86774 : word) = Some W_86774.
Proof. vm_refl. Qed.
Lemma D_86774 : decode_any W_86774 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86778 : bv 32 := 0x412804bb.
Lemma F_86778 : fetch_word Ubsan.M.loaded_segments (0x86778 : word) = Some W_86778.
Proof. vm_refl. Qed.
Lemma D_86778 : decode_any W_86778 = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8677c : bv 32 := 0x03813383.
Lemma F_8677c : fetch_word Ubsan.M.loaded_segments (0x8677c : word) = Some W_8677c.
Proof. vm_refl. Qed.
Lemma D_8677c : decode_any W_8677c = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_86780 : bv 32 := 0x03013803.
Lemma F_86780 : fetch_word Ubsan.M.loaded_segments (0x86780 : word) = Some W_86780.
Proof. vm_refl. Qed.
Lemma D_86780 : decode_any W_86780 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_86784 : bv 32 := 0x007803b3.
Lemma F_86784 : fetch_word Ubsan.M.loaded_segments (0x86784 : word) = Some W_86784.
Proof. vm_refl. Qed.
Lemma D_86784 : decode_any W_86784 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86788 : bv 32 := 0x04813283.
Lemma F_86788 : fetch_word Ubsan.M.loaded_segments (0x86788 : word) = Some W_86788.
Proof. vm_refl. Qed.
Lemma D_86788 : decode_any W_86788 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8678c : bv 32 := 0x43f2d813.
Lemma F_8678c : fetch_word Ubsan.M.loaded_segments (0x8678c : word) = Some W_8678c.
Proof. vm_refl. Qed.
Lemma D_8678c : decode_any W_8678c = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86790 : bv 32 := 0x00587e33.
Lemma F_86790 : fetch_word Ubsan.M.loaded_segments (0x86790 : word) = Some W_86790.
Proof. vm_refl. Qed.
Lemma D_86790 : decode_any W_86790 = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86794 : bv 32 := 0x02000813.
Lemma F_86794 : fetch_word Ubsan.M.loaded_segments (0x86794 : word) = Some W_86794.
Proof. vm_refl. Qed.
Lemma D_86794 : decode_any W_86794 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86798 : bv 32 := 0x00813283.
Lemma F_86798 : fetch_word Ubsan.M.loaded_segments (0x86798 : word) = Some W_86798.
Proof. vm_refl. Qed.
Lemma D_86798 : decode_any W_86798 = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8679c : bv 32 := 0x0012f293.
Lemma F_8679c : fetch_word Ubsan.M.loaded_segments (0x8679c : word) = Some W_8679c.
Proof. vm_refl. Qed.
Lemma D_8679c : decode_any W_8679c = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_867a0 : bv 32 := 0x00072713.
Lemma F_867a0 : fetch_word Ubsan.M.loaded_segments (0x867a0 : word) = Some W_867a0.
Proof. vm_refl. Qed.
Lemma D_867a0 : decode_any W_867a0 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_867a4 : bv 32 := 0x01c38e33.
Lemma F_867a4 : fetch_word Ubsan.M.loaded_segments (0x867a4 : word) = Some W_867a4.
Proof. vm_refl. Qed.
Lemma D_867a4 : decode_any W_867a4 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_867a8 : bv 32 := 0xffb00393.
Lemma F_867a8 : fetch_word Ubsan.M.loaded_segments (0x867a8 : word) = Some W_867a8.
Proof. vm_refl. Qed.
Lemma D_867a8 : decode_any W_867a8 = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_867ac : bv 32 := 0x412e093b.
Lemma F_867ac : fetch_word Ubsan.M.loaded_segments (0x867ac : word) = Some W_867ac.
Proof. vm_refl. Qed.
Lemma D_867ac : decode_any W_867ac = Some (Op32 ALU_SUB 18 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_867b0 : bv 32 := 0x06813e03.
Lemma F_867b0 : fetch_word Ubsan.M.loaded_segments (0x867b0 : word) = Some W_867b0.
Proof. vm_refl. Qed.
Lemma D_867b0 : decode_any W_867b0 = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_867b4 : bv 32 := 0x006e0e33.
Lemma F_867b4 : fetch_word Ubsan.M.loaded_segments (0x867b4 : word) = Some W_867b4.
Proof. vm_refl. Qed.
Lemma D_867b4 : decode_any W_867b4 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_867b8 : bv 32 := 0x04013983.
Lemma F_867b8 : fetch_word Ubsan.M.loaded_segments (0x867b8 : word) = Some W_867b8.
Proof. vm_refl. Qed.
Lemma D_867b8 : decode_any W_867b8 = Some (Load SZ8 true 19 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_867bc : bv 32 := 0x4139093b.
Lemma F_867bc : fetch_word Ubsan.M.loaded_segments (0x867bc : word) = Some W_867bc.
Proof. vm_refl. Qed.
Lemma D_867bc : decode_any W_867bc = Some (Op32 ALU_SUB 18 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_867c0 : bv 32 := 0x43f95993.
Lemma F_867c0 : fetch_word Ubsan.M.loaded_segments (0x867c0 : word) = Some W_867c0.
Proof. vm_refl. Qed.
Lemma D_867c0 : decode_any W_867c0 = Some (ShiftImm ALU_SRA 19 18 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_867c4 : bv 32 := 0x0129f933.
Lemma F_867c4 : fetch_word Ubsan.M.loaded_segments (0x867c4 : word) = Some W_867c4.
Proof. vm_refl. Qed.
Lemma D_867c4 : decode_any W_867c4 = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_867c8 : bv 32 := 0x412484bb.
Lemma F_867c8 : fetch_word Ubsan.M.loaded_segments (0x867c8 : word) = Some W_867c8.
Proof. vm_refl. Qed.
Lemma D_867c8 : decode_any W_867c8 = Some (Op32 ALU_SUB 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_867cc : bv 32 := 0x01f00993.
Lemma F_867cc : fetch_word Ubsan.M.loaded_segments (0x867cc : word) = Some W_867cc.
Proof. vm_refl. Qed.
Lemma D_867cc : decode_any W_867cc = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_867d0 : bv 32 := 0x00050a13.
Lemma F_867d0 : fetch_word Ubsan.M.loaded_segments (0x867d0 : word) = Some W_867d0.
Proof. vm_refl. Qed.
Lemma D_867d0 : decode_any W_867d0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_867d4 : bv 32 := 0x06013c03.
Lemma F_867d4 : fetch_word Ubsan.M.loaded_segments (0x867d4 : word) = Some W_867d4.
Proof. vm_refl. Qed.
Lemma D_867d4 : decode_any W_867d4 = Some (Load SZ8 true 24 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_867d8 : bv 32 := 0x06813a83.
Lemma F_867d8 : fetch_word Ubsan.M.loaded_segments (0x867d8 : word) = Some W_867d8.
Proof. vm_refl. Qed.
Lemma D_867d8 : decode_any W_867d8 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_867dc : bv 32 := 0x00ba8ab3.
Lemma F_867dc : fetch_word Ubsan.M.loaded_segments (0x867dc : word) = Some W_867dc.
Proof. vm_refl. Qed.
Lemma D_867dc : decode_any W_867dc = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_867e0 : bv 32 := 0x000a9463.
Lemma F_867e0 : fetch_word Ubsan.M.loaded_segments (0x867e0 : word) = Some W_867e0.
Proof. vm_refl. Qed.
Lemma D_867e0 : decode_any W_867e0 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_867e4 : bv 32 := 0xd11fb06f.
Lemma F_867e4 : fetch_word Ubsan.M.loaded_segments (0x867e4 : word) = Some W_867e4.
Proof. vm_refl. Qed.
Lemma D_867e4 : decode_any W_867e4 = Some (Jal 0 2080016, 4%Z).
Proof. vm_refl. Qed.

Definition W_867e8 : bv 32 := 0x010f1463.
Lemma F_867e8 : fetch_word Ubsan.M.loaded_segments (0x867e8 : word) = Some W_867e8.
Proof. vm_refl. Qed.
Lemma D_867e8 : decode_any W_867e8 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_867ec : bv 32 := 0xd09fb06f.
Lemma F_867ec : fetch_word Ubsan.M.loaded_segments (0x867ec : word) = Some W_867ec.
Proof. vm_refl. Qed.
Lemma D_867ec : decode_any W_867ec = Some (Jal 0 2080008, 4%Z).
Proof. vm_refl. Qed.

Definition W_867f0 : bv 32 := 0x000aa903.
Lemma F_867f0 : fetch_word Ubsan.M.loaded_segments (0x867f0 : word) = Some W_867f0.
Proof. vm_refl. Qed.
Lemma D_867f0 : decode_any W_867f0 = Some (Load SZ4 true 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_867f4 : bv 32 := 0x01d91b3b.
Lemma F_867f4 : fetch_word Ubsan.M.loaded_segments (0x867f4 : word) = Some W_867f4.
Proof. vm_refl. Qed.
Lemma D_867f4 : decode_any W_867f4 = Some (Op32 ALU_SLL 22 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_867f8 : bv 32 := 0x02029463.
Lemma F_867f8 : fetch_word Ubsan.M.loaded_segments (0x867f8 : word) = Some W_867f8.
Proof. vm_refl. Qed.
Lemma D_867f8 : decode_any W_867f8 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_867fc : bv 32 := 0x0153f463.
Lemma F_867fc : fetch_word Ubsan.M.loaded_segments (0x867fc : word) = Some W_867fc.
Proof. vm_refl. Qed.
Lemma D_867fc : decode_any W_867fc = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86800 : bv 32 := 0xcf5fb06f.
Lemma F_86800 : fetch_word Ubsan.M.loaded_segments (0x86800 : word) = Some W_86800.
Proof. vm_refl. Qed.
Lemma D_86800 : decode_any W_86800 = Some (Jal 0 2079988, 4%Z).
Proof. vm_refl. Qed.

Definition W_86804 : bv 32 := 0x0089f463.
Lemma F_86804 : fetch_word Ubsan.M.loaded_segments (0x86804 : word) = Some W_86804.
Proof. vm_refl. Qed.
Lemma D_86804 : decode_any W_86804 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86808 : bv 32 := 0xcedfb06f.
Lemma F_86808 : fetch_word Ubsan.M.loaded_segments (0x86808 : word) = Some W_86808.
Proof. vm_refl. Qed.
Lemma D_86808 : decode_any W_86808 = Some (Jal 0 2079980, 4%Z).
Proof. vm_refl. Qed.

Definition W_8680c : bv 32 := 0x004aa903.
Lemma F_8680c : fetch_word Ubsan.M.loaded_segments (0x8680c : word) = Some W_8680c.
Proof. vm_refl. Qed.
Lemma D_8680c : decode_any W_8680c = Some (Load SZ4 true 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86810 : bv 32 := 0x00cb7b33.
Lemma F_86810 : fetch_word Ubsan.M.loaded_segments (0x86810 : word) = Some W_86810.
Proof. vm_refl. Qed.
Lemma D_86810 : decode_any W_86810 = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86814 : bv 32 := 0x0089593b.
Lemma F_86814 : fetch_word Ubsan.M.loaded_segments (0x86814 : word) = Some W_86814.
Proof. vm_refl. Qed.
Lemma D_86814 : decode_any W_86814 = Some (Op32 ALU_SRL 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86818 : bv 32 := 0x01f97933.
Lemma F_86818 : fetch_word Ubsan.M.loaded_segments (0x86818 : word) = Some W_86818.
Proof. vm_refl. Qed.
Lemma D_86818 : decode_any W_86818 = Some (Op ALU_AND 18 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_8681c : bv 32 := 0x01696b33.
Lemma F_8681c : fetch_word Ubsan.M.loaded_segments (0x8681c : word) = Some W_8681c.
Proof. vm_refl. Qed.
Lemma D_8681c : decode_any W_8681c = Some (Op ALU_OR 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_86820 : bv 32 := 0x00088463.
Lemma F_86820 : fetch_word Ubsan.M.loaded_segments (0x86820 : word) = Some W_86820.
Proof. vm_refl. Qed.
Lemma D_86820 : decode_any W_86820 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86824 : bv 32 := 0xcd1fb06f.
Lemma F_86824 : fetch_word Ubsan.M.loaded_segments (0x86824 : word) = Some W_86824.
Proof. vm_refl. Qed.
Lemma D_86824 : decode_any W_86824 = Some (Jal 0 2079952, 4%Z).
Proof. vm_refl. Qed.

Definition W_86828 : bv 32 := 0x00051463.
Lemma F_86828 : fetch_word Ubsan.M.loaded_segments (0x86828 : word) = Some W_86828.
Proof. vm_refl. Qed.
Lemma D_86828 : decode_any W_86828 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8682c : bv 32 := 0xcc9fb06f.
Lemma F_8682c : fetch_word Ubsan.M.loaded_segments (0x8682c : word) = Some W_8682c.
Proof. vm_refl. Qed.
Lemma D_8682c : decode_any W_8682c = Some (Jal 0 2079944, 4%Z).
Proof. vm_refl. Qed.

Definition W_86830 : bv 32 := 0x00052903.
Lemma F_86830 : fetch_word Ubsan.M.loaded_segments (0x86830 : word) = Some W_86830.
Proof. vm_refl. Qed.
Lemma D_86830 : decode_any W_86830 = Some (Load SZ4 true 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86834 : bv 32 := 0x00d97bb3.
Lemma F_86834 : fetch_word Ubsan.M.loaded_segments (0x86834 : word) = Some W_86834.
Proof. vm_refl. Qed.
Lemma D_86834 : decode_any W_86834 = Some (Op ALU_AND 23 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86838 : bv 32 := 0xfff94913.
Lemma F_86838 : fetch_word Ubsan.M.loaded_segments (0x86838 : word) = Some W_86838.
Proof. vm_refl. Qed.
Lemma D_86838 : decode_any W_86838 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8683c : bv 32 := 0x01897933.
Lemma F_8683c : fetch_word Ubsan.M.loaded_segments (0x8683c : word) = Some W_8683c.
Proof. vm_refl. Qed.
Lemma D_8683c : decode_any W_8683c = Some (Op ALU_AND 18 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86840 : bv 32 := 0x012b7933.
Lemma F_86840 : fetch_word Ubsan.M.loaded_segments (0x86840 : word) = Some W_86840.
Proof. vm_refl. Qed.
Lemma D_86840 : decode_any W_86840 = Some (Op ALU_AND 18 22 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86844 : bv 32 := 0x01796933.
Lemma F_86844 : fetch_word Ubsan.M.loaded_segments (0x86844 : word) = Some W_86844.
Proof. vm_refl. Qed.
Lemma D_86844 : decode_any W_86844 = Some (Op ALU_OR 18 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_86848 : bv 32 := 0x01478b33.
Lemma F_86848 : fetch_word Ubsan.M.loaded_segments (0x86848 : word) = Some W_86848.
Proof. vm_refl. Qed.
Lemma D_86848 : decode_any W_86848 = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8684c : bv 32 := 0x01252023.
Lemma F_8684c : fetch_word Ubsan.M.loaded_segments (0x8684c : word) = Some W_8684c.
Proof. vm_refl. Qed.
Lemma D_8684c : decode_any W_8684c = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86850 : bv 32 := 0x000b1463.
Lemma F_86850 : fetch_word Ubsan.M.loaded_segments (0x86850 : word) = Some W_86850.
Proof. vm_refl. Qed.
Lemma D_86850 : decode_any W_86850 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86854 : bv 32 := 0xca1fb06f.
Lemma F_86854 : fetch_word Ubsan.M.loaded_segments (0x86854 : word) = Some W_86854.
Proof. vm_refl. Qed.
Lemma D_86854 : decode_any W_86854 = Some (Jal 0 2079904, 4%Z).
Proof. vm_refl. Qed.

Definition W_86858 : bv 32 := 0x014b3933.
Lemma F_86858 : fetch_word Ubsan.M.loaded_segments (0x86858 : word) = Some W_86858.
Proof. vm_refl. Qed.
Lemma D_86858 : decode_any W_86858 = Some (Op ALU_SLTU 18 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8685c : bv 32 := 0x00e94933.
Lemma F_8685c : fetch_word Ubsan.M.loaded_segments (0x8685c : word) = Some W_8685c.
Proof. vm_refl. Qed.
Lemma D_8685c : decode_any W_8685c = Some (Op ALU_XOR 18 18 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_86860 : bv 32 := 0x00194913.
Lemma F_86860 : fetch_word Ubsan.M.loaded_segments (0x86860 : word) = Some W_86860.
Proof. vm_refl. Qed.
Lemma D_86860 : decode_any W_86860 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86864 : bv 32 := 0x00091463.
Lemma F_86864 : fetch_word Ubsan.M.loaded_segments (0x86864 : word) = Some W_86864.
Proof. vm_refl. Qed.
Lemma D_86864 : decode_any W_86864 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86868 : bv 32 := 0xc8dfb06f.
Lemma F_86868 : fetch_word Ubsan.M.loaded_segments (0x86868 : word) = Some W_86868.
Proof. vm_refl. Qed.
Lemma D_86868 : decode_any W_86868 = Some (Jal 0 2079884, 4%Z).
Proof. vm_refl. Qed.

Definition W_8686c : bv 32 := 0x00be0a33.
Lemma F_8686c : fetch_word Ubsan.M.loaded_segments (0x8686c : word) = Some W_8686c.
Proof. vm_refl. Qed.
Lemma D_8686c : decode_any W_8686c = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86870 : bv 32 := 0x000a1463.
Lemma F_86870 : fetch_word Ubsan.M.loaded_segments (0x86870 : word) = Some W_86870.
Proof. vm_refl. Qed.
Lemma D_86870 : decode_any W_86870 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86874 : bv 32 := 0xc81fb06f.
Lemma F_86874 : fetch_word Ubsan.M.loaded_segments (0x86874 : word) = Some W_86874.
Proof. vm_refl. Qed.
Lemma D_86874 : decode_any W_86874 = Some (Jal 0 2079872, 4%Z).
Proof. vm_refl. Qed.

Definition W_86878 : bv 32 := 0x015a3933.
Lemma F_86878 : fetch_word Ubsan.M.loaded_segments (0x86878 : word) = Some W_86878.
Proof. vm_refl. Qed.
Lemma D_86878 : decode_any W_86878 = Some (Op ALU_SLTU 18 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_8687c : bv 32 := 0x07813a03.
Lemma F_8687c : fetch_word Ubsan.M.loaded_segments (0x8687c : word) = Some W_8687c.
Proof. vm_refl. Qed.
Lemma D_8687c : decode_any W_8687c = Some (Load SZ8 true 20 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86880 : bv 32 := 0x01494933.
Lemma F_86880 : fetch_word Ubsan.M.loaded_segments (0x86880 : word) = Some W_86880.
Proof. vm_refl. Qed.
Lemma D_86880 : decode_any W_86880 = Some (Op ALU_XOR 18 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86884 : bv 32 := 0x00194913.
Lemma F_86884 : fetch_word Ubsan.M.loaded_segments (0x86884 : word) = Some W_86884.
Proof. vm_refl. Qed.
Lemma D_86884 : decode_any W_86884 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86888 : bv 32 := 0x00091463.
Lemma F_86888 : fetch_word Ubsan.M.loaded_segments (0x86888 : word) = Some W_86888.
Proof. vm_refl. Qed.
Lemma D_86888 : decode_any W_86888 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8688c : bv 32 := 0xc69fb06f.
Lemma F_8688c : fetch_word Ubsan.M.loaded_segments (0x8688c : word) = Some W_8688c.
Proof. vm_refl. Qed.
Lemma D_8688c : decode_any W_8688c = Some (Jal 0 2079848, 4%Z).
Proof. vm_refl. Qed.

Definition W_86890 : bv 32 := 0x0014849b.
Lemma F_86890 : fetch_word Ubsan.M.loaded_segments (0x86890 : word) = Some W_86890.
Proof. vm_refl. Qed.
Lemma D_86890 : decode_any W_86890 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86894 : bv 32 := 0x006585b3.
Lemma F_86894 : fetch_word Ubsan.M.loaded_segments (0x86894 : word) = Some W_86894.
Proof. vm_refl. Qed.
Lemma D_86894 : decode_any W_86894 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86898 : bv 32 := 0x00f50533.
Lemma F_86898 : fetch_word Ubsan.M.loaded_segments (0x86898 : word) = Some W_86898.
Proof. vm_refl. Qed.
Lemma D_86898 : decode_any W_86898 = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8689c : bv 32 := 0x000b0a13.
Lemma F_8689c : fetch_word Ubsan.M.loaded_segments (0x8689c : word) = Some W_8689c.
Proof. vm_refl. Qed.
Lemma D_8689c : decode_any W_8689c = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_868a0 : bv 32 := 0xf2049ce3.
Lemma F_868a0 : fetch_word Ubsan.M.loaded_segments (0x868a0 : word) = Some W_868a0.
Proof. vm_refl. Qed.
Lemma D_868a0 : decode_any W_868a0 = Some (Branch BC_NE 9 0 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_868a4 : bv 32 := 0x5150006f.
Lemma F_868a4 : fetch_word Ubsan.M.loaded_segments (0x868a4 : word) = Some W_868a4.
Proof. vm_refl. Qed.
Lemma D_868a4 : decode_any W_868a4 = Some (Jal 0 3348, 4%Z).
Proof. vm_refl. Qed.

Definition W_868a8 : bv 32 := 0x18008063.
Lemma F_868a8 : fetch_word Ubsan.M.loaded_segments (0x868a8 : word) = Some W_868a8.
Proof. vm_refl. Qed.
Lemma D_868a8 : decode_any W_868a8 = Some (Branch BC_EQ 1 0 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_868ac : bv 32 := 0x00000593.
Lemma F_868ac : fetch_word Ubsan.M.loaded_segments (0x868ac : word) = Some W_868ac.
Proof. vm_refl. Qed.
Lemma D_868ac : decode_any W_868ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_868b0 : bv 32 := 0xffffc613.
Lemma F_868b0 : fetch_word Ubsan.M.loaded_segments (0x868b0 : word) = Some W_868b0.
Proof. vm_refl. Qed.
Lemma D_868b0 : decode_any W_868b0 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_868b4 : bv 32 := 0x00c13023.
Lemma F_868b4 : fetch_word Ubsan.M.loaded_segments (0x868b4 : word) = Some W_868b4.
Proof. vm_refl. Qed.
Lemma D_868b4 : decode_any W_868b4 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_868b8 : bv 32 := 0xfffdc293.
Lemma F_868b8 : fetch_word Ubsan.M.loaded_segments (0x868b8 : word) = Some W_868b8.
Proof. vm_refl. Qed.
Lemma D_868b8 : decode_any W_868b8 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_868bc : bv 32 := 0x00271393.
Lemma F_868bc : fetch_word Ubsan.M.loaded_segments (0x868bc : word) = Some W_868bc.
Proof. vm_refl. Qed.
Lemma D_868bc : decode_any W_868bc = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_868c0 : bv 32 := 0x05813683.
Lemma F_868c0 : fetch_word Ubsan.M.loaded_segments (0x868c0 : word) = Some W_868c0.
Proof. vm_refl. Qed.
Lemma D_868c0 : decode_any W_868c0 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_868c4 : bv 32 := 0x00269693.
Lemma F_868c4 : fetch_word Ubsan.M.loaded_segments (0x868c4 : word) = Some W_868c4.
Proof. vm_refl. Qed.
Lemma D_868c4 : decode_any W_868c4 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_868c8 : bv 32 := 0x003cfb93.
Lemma F_868c8 : fetch_word Ubsan.M.loaded_segments (0x868c8 : word) = Some W_868c8.
Proof. vm_refl. Qed.
Lemma D_868c8 : decode_any W_868c8 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_868cc : bv 32 := 0x0037f613.
Lemma F_868cc : fetch_word Ubsan.M.loaded_segments (0x868cc : word) = Some W_868cc.
Proof. vm_refl. Qed.
Lemma D_868cc : decode_any W_868cc = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_868d0 : bv 32 := 0x05013483.
Lemma F_868d0 : fetch_word Ubsan.M.loaded_segments (0x868d0 : word) = Some W_868d0.
Proof. vm_refl. Qed.
Lemma D_868d0 : decode_any W_868d0 = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_868d4 : bv 32 := 0x02813803.
Lemma F_868d4 : fetch_word Ubsan.M.loaded_segments (0x868d4 : word) = Some W_868d4.
Proof. vm_refl. Qed.
Lemma D_868d4 : decode_any W_868d4 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_868d8 : bv 32 := 0x4098083b.
Lemma F_868d8 : fetch_word Ubsan.M.loaded_segments (0x868d8 : word) = Some W_868d8.
Proof. vm_refl. Qed.
Lemma D_868d8 : decode_any W_868d8 = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_868dc : bv 32 := 0x03813883.
Lemma F_868dc : fetch_word Ubsan.M.loaded_segments (0x868dc : word) = Some W_868dc.
Proof. vm_refl. Qed.
Lemma D_868dc : decode_any W_868dc = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_868e0 : bv 32 := 0x03013e03.
Lemma F_868e0 : fetch_word Ubsan.M.loaded_segments (0x868e0 : word) = Some W_868e0.
Proof. vm_refl. Qed.
Lemma D_868e0 : decode_any W_868e0 = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_868e4 : bv 32 := 0x011e08b3.
Lemma F_868e4 : fetch_word Ubsan.M.loaded_segments (0x868e4 : word) = Some W_868e4.
Proof. vm_refl. Qed.
Lemma D_868e4 : decode_any W_868e4 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_868e8 : bv 32 := 0x04813a03.
Lemma F_868e8 : fetch_word Ubsan.M.loaded_segments (0x868e8 : word) = Some W_868e8.
Proof. vm_refl. Qed.
Lemma D_868e8 : decode_any W_868e8 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_868ec : bv 32 := 0x43fa5e13.
Lemma F_868ec : fetch_word Ubsan.M.loaded_segments (0x868ec : word) = Some W_868ec.
Proof. vm_refl. Qed.
Lemma D_868ec : decode_any W_868ec = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_868f0 : bv 32 := 0x01013983.
Lemma F_868f0 : fetch_word Ubsan.M.loaded_segments (0x868f0 : word) = Some W_868f0.
Proof. vm_refl. Qed.
Lemma D_868f0 : decode_any W_868f0 = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_868f4 : bv 32 := 0x0019f993.
Lemma F_868f4 : fetch_word Ubsan.M.loaded_segments (0x868f4 : word) = Some W_868f4.
Proof. vm_refl. Qed.
Lemma D_868f4 : decode_any W_868f4 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_868f8 : bv 32 := 0x001d7c13.
Lemma F_868f8 : fetch_word Ubsan.M.loaded_segments (0x868f8 : word) = Some W_868f8.
Proof. vm_refl. Qed.
Lemma D_868f8 : decode_any W_868f8 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_868fc : bv 32 := 0x01f00093.
Lemma F_868fc : fetch_word Ubsan.M.loaded_segments (0x868fc : word) = Some W_868fc.
Proof. vm_refl. Qed.
Lemma D_868fc : decode_any W_868fc = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86900 : bv 32 := 0x014e7e33.
Lemma F_86900 : fetch_word Ubsan.M.loaded_segments (0x86900 : word) = Some W_86900.
Proof. vm_refl. Qed.
Lemma D_86900 : decode_any W_86900 = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86904 : bv 32 := 0x409888bb.
Lemma F_86904 : fetch_word Ubsan.M.loaded_segments (0x86904 : word) = Some W_86904.
Proof. vm_refl. Qed.
Lemma D_86904 : decode_any W_86904 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86908 : bv 32 := 0x00d78a33.
Lemma F_86908 : fetch_word Ubsan.M.loaded_segments (0x86908 : word) = Some W_86908.
Proof. vm_refl. Qed.
Lemma D_86908 : decode_any W_86908 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8690c : bv 32 := 0x00163b13.
Lemma F_8690c : fetch_word Ubsan.M.loaded_segments (0x8690c : word) = Some W_8690c.
Proof. vm_refl. Qed.
Lemma D_8690c : decode_any W_8690c = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86910 : bv 32 := 0x04013603.
Lemma F_86910 : fetch_word Ubsan.M.loaded_segments (0x86910 : word) = Some W_86910.
Proof. vm_refl. Qed.
Lemma D_86910 : decode_any W_86910 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86914 : bv 32 := 0x40c8863b.
Lemma F_86914 : fetch_word Ubsan.M.loaded_segments (0x86914 : word) = Some W_86914.
Proof. vm_refl. Qed.
Lemma D_86914 : decode_any W_86914 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86918 : bv 32 := 0x01c6063b.
Lemma F_86918 : fetch_word Ubsan.M.loaded_segments (0x86918 : word) = Some W_86918.
Proof. vm_refl. Qed.
Lemma D_86918 : decode_any W_86918 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8691c : bv 32 := 0x43f65893.
Lemma F_8691c : fetch_word Ubsan.M.loaded_segments (0x8691c : word) = Some W_8691c.
Proof. vm_refl. Qed.
Lemma D_8691c : decode_any W_8691c = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86920 : bv 32 := 0x00c8f633.
Lemma F_86920 : fetch_word Ubsan.M.loaded_segments (0x86920 : word) = Some W_86920.
Proof. vm_refl. Qed.
Lemma D_86920 : decode_any W_86920 = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86924 : bv 32 := 0x40c80e3b.
Lemma F_86924 : fetch_word Ubsan.M.loaded_segments (0x86924 : word) = Some W_86924.
Proof. vm_refl. Qed.
Lemma D_86924 : decode_any W_86924 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86928 : bv 32 := 0x00072493.
Lemma F_86928 : fetch_word Ubsan.M.loaded_segments (0x86928 : word) = Some W_86928.
Proof. vm_refl. Qed.
Lemma D_86928 : decode_any W_86928 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8692c : bv 32 := 0x000c8813.
Lemma F_8692c : fetch_word Ubsan.M.loaded_segments (0x8692c : word) = Some W_8692c.
Proof. vm_refl. Qed.
Lemma D_8692c : decode_any W_8692c = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86930 : bv 32 := 0x00b78d33.
Lemma F_86930 : fetch_word Ubsan.M.loaded_segments (0x86930 : word) = Some W_86930.
Proof. vm_refl. Qed.
Lemma D_86930 : decode_any W_86930 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86934 : bv 32 := 0x01a03633.
Lemma F_86934 : fetch_word Ubsan.M.loaded_segments (0x86934 : word) = Some W_86934.
Proof. vm_refl. Qed.
Lemma D_86934 : decode_any W_86934 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86938 : bv 32 := 0x00cb7633.
Lemma F_86938 : fetch_word Ubsan.M.loaded_segments (0x86938 : word) = Some W_86938.
Proof. vm_refl. Qed.
Lemma D_86938 : decode_any W_86938 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8693c : bv 32 := 0x04098a63.
Lemma F_8693c : fetch_word Ubsan.M.loaded_segments (0x8693c : word) = Some W_8693c.
Proof. vm_refl. Qed.
Lemma D_8693c : decode_any W_8693c = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_86940 : bv 32 := 0x00061463.
Lemma F_86940 : fetch_word Ubsan.M.loaded_segments (0x86940 : word) = Some W_86940.
Proof. vm_refl. Qed.
Lemma D_86940 : decode_any W_86940 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86944 : bv 32 := 0xbb1fb06f.
Lemma F_86944 : fetch_word Ubsan.M.loaded_segments (0x86944 : word) = Some W_86944.
Proof. vm_refl. Qed.
Lemma D_86944 : decode_any W_86944 = Some (Jal 0 2079664, 4%Z).
Proof. vm_refl. Qed.

Definition W_86948 : bv 32 := 0x02000613.
Lemma F_86948 : fetch_word Ubsan.M.loaded_segments (0x86948 : word) = Some W_86948.
Proof. vm_refl. Qed.
Lemma D_86948 : decode_any W_86948 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8694c : bv 32 := 0x00cf1463.
Lemma F_8694c : fetch_word Ubsan.M.loaded_segments (0x8694c : word) = Some W_8694c.
Proof. vm_refl. Qed.
Lemma D_8694c : decode_any W_8694c = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86950 : bv 32 := 0xba5fb06f.
Lemma F_86950 : fetch_word Ubsan.M.loaded_segments (0x86950 : word) = Some W_86950.
Proof. vm_refl. Qed.
Lemma D_86950 : decode_any W_86950 = Some (Jal 0 2079652, 4%Z).
Proof. vm_refl. Qed.

Definition W_86954 : bv 32 := 0x000d2603.
Lemma F_86954 : fetch_word Ubsan.M.loaded_segments (0x86954 : word) = Some W_86954.
Proof. vm_refl. Qed.
Lemma D_86954 : decode_any W_86954 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86958 : bv 32 := 0x01d61abb.
Lemma F_86958 : fetch_word Ubsan.M.loaded_segments (0x86958 : word) = Some W_86958.
Proof. vm_refl. Qed.
Lemma D_86958 : decode_any W_86958 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_8695c : bv 32 := 0x040c1663.
Lemma F_8695c : fetch_word Ubsan.M.loaded_segments (0x8695c : word) = Some W_8695c.
Proof. vm_refl. Qed.
Lemma D_8695c : decode_any W_8695c = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_86960 : bv 32 := 0xffb00613.
Lemma F_86960 : fetch_word Ubsan.M.loaded_segments (0x86960 : word) = Some W_86960.
Proof. vm_refl. Qed.
Lemma D_86960 : decode_any W_86960 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_86964 : bv 32 := 0x01a67463.
Lemma F_86964 : fetch_word Ubsan.M.loaded_segments (0x86964 : word) = Some W_86964.
Proof. vm_refl. Qed.
Lemma D_86964 : decode_any W_86964 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86968 : bv 32 := 0xb8dfb06f.
Lemma F_86968 : fetch_word Ubsan.M.loaded_segments (0x86968 : word) = Some W_86968.
Proof. vm_refl. Qed.
Lemma D_86968 : decode_any W_86968 = Some (Jal 0 2079628, 4%Z).
Proof. vm_refl. Qed.

Definition W_8696c : bv 32 := 0x0080f463.
Lemma F_8696c : fetch_word Ubsan.M.loaded_segments (0x8696c : word) = Some W_8696c.
Proof. vm_refl. Qed.
Lemma D_8696c : decode_any W_8696c = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86970 : bv 32 := 0xb85fb06f.
Lemma F_86970 : fetch_word Ubsan.M.loaded_segments (0x86970 : word) = Some W_86970.
Proof. vm_refl. Qed.
Lemma D_86970 : decode_any W_86970 = Some (Jal 0 2079620, 4%Z).
Proof. vm_refl. Qed.

Definition W_86974 : bv 32 := 0x004d2603.
Lemma F_86974 : fetch_word Ubsan.M.loaded_segments (0x86974 : word) = Some W_86974.
Proof. vm_refl. Qed.
Lemma D_86974 : decode_any W_86974 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86978 : bv 32 := 0x00013883.
Lemma F_86978 : fetch_word Ubsan.M.loaded_segments (0x86978 : word) = Some W_86978.
Proof. vm_refl. Qed.
Lemma D_86978 : decode_any W_86978 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8697c : bv 32 := 0x011af8b3.
Lemma F_8697c : fetch_word Ubsan.M.loaded_segments (0x8697c : word) = Some W_8697c.
Proof. vm_refl. Qed.
Lemma D_8697c : decode_any W_8697c = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86980 : bv 32 := 0x0086563b.
Lemma F_86980 : fetch_word Ubsan.M.loaded_segments (0x86980 : word) = Some W_86980.
Proof. vm_refl. Qed.
Lemma D_86980 : decode_any W_86980 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86984 : bv 32 := 0x01f67633.
Lemma F_86984 : fetch_word Ubsan.M.loaded_segments (0x86984 : word) = Some W_86984.
Proof. vm_refl. Qed.
Lemma D_86984 : decode_any W_86984 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86988 : bv 32 := 0x01166ab3.
Lemma F_86988 : fetch_word Ubsan.M.loaded_segments (0x86988 : word) = Some W_86988.
Proof. vm_refl. Qed.
Lemma D_86988 : decode_any W_86988 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8698c : bv 32 := 0x01c0006f.
Lemma F_8698c : fetch_word Ubsan.M.loaded_segments (0x8698c : word) = Some W_8698c.
Proof. vm_refl. Qed.
Lemma D_8698c : decode_any W_8698c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86990 : bv 32 := 0x00061463.
Lemma F_86990 : fetch_word Ubsan.M.loaded_segments (0x86990 : word) = Some W_86990.
Proof. vm_refl. Qed.
Lemma D_86990 : decode_any W_86990 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86994 : bv 32 := 0xb61fb06f.
Lemma F_86994 : fetch_word Ubsan.M.loaded_segments (0x86994 : word) = Some W_86994.
Proof. vm_refl. Qed.
Lemma D_86994 : decode_any W_86994 = Some (Jal 0 2079584, 4%Z).
Proof. vm_refl. Qed.

Definition W_86998 : bv 32 := 0x0080f463.
Lemma F_86998 : fetch_word Ubsan.M.loaded_segments (0x86998 : word) = Some W_86998.
Proof. vm_refl. Qed.
Lemma D_86998 : decode_any W_86998 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8699c : bv 32 := 0xb59fb06f.
Lemma F_8699c : fetch_word Ubsan.M.loaded_segments (0x8699c : word) = Some W_8699c.
Proof. vm_refl. Qed.
Lemma D_8699c : decode_any W_8699c = Some (Jal 0 2079576, 4%Z).
Proof. vm_refl. Qed.

Definition W_869a0 : bv 32 := 0x000d2603.
Lemma F_869a0 : fetch_word Ubsan.M.loaded_segments (0x869a0 : word) = Some W_869a0.
Proof. vm_refl. Qed.
Lemma D_869a0 : decode_any W_869a0 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_869a4 : bv 32 := 0x00865abb.
Lemma F_869a4 : fetch_word Ubsan.M.loaded_segments (0x869a4 : word) = Some W_869a4.
Proof. vm_refl. Qed.
Lemma D_869a4 : decode_any W_869a4 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_869a8 : bv 32 := 0x000b8463.
Lemma F_869a8 : fetch_word Ubsan.M.loaded_segments (0x869a8 : word) = Some W_869a8.
Proof. vm_refl. Qed.
Lemma D_869a8 : decode_any W_869a8 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_869ac : bv 32 := 0xb49fb06f.
Lemma F_869ac : fetch_word Ubsan.M.loaded_segments (0x869ac : word) = Some W_869ac.
Proof. vm_refl. Qed.
Lemma D_869ac : decode_any W_869ac = Some (Jal 0 2079560, 4%Z).
Proof. vm_refl. Qed.

Definition W_869b0 : bv 32 := 0x000c9463.
Lemma F_869b0 : fetch_word Ubsan.M.loaded_segments (0x869b0 : word) = Some W_869b0.
Proof. vm_refl. Qed.
Lemma D_869b0 : decode_any W_869b0 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_869b4 : bv 32 := 0xb41fb06f.
Lemma F_869b4 : fetch_word Ubsan.M.loaded_segments (0x869b4 : word) = Some W_869b4.
Proof. vm_refl. Qed.
Lemma D_869b4 : decode_any W_869b4 = Some (Jal 0 2079552, 4%Z).
Proof. vm_refl. Qed.

Definition W_869b8 : bv 32 := 0x000ca603.
Lemma F_869b8 : fetch_word Ubsan.M.loaded_segments (0x869b8 : word) = Some W_869b8.
Proof. vm_refl. Qed.
Lemma D_869b8 : decode_any W_869b8 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_869bc : bv 32 := 0x005678b3.
Lemma F_869bc : fetch_word Ubsan.M.loaded_segments (0x869bc : word) = Some W_869bc.
Proof. vm_refl. Qed.
Lemma D_869bc : decode_any W_869bc = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_869c0 : bv 32 := 0x01564633.
Lemma F_869c0 : fetch_word Ubsan.M.loaded_segments (0x869c0 : word) = Some W_869c0.
Proof. vm_refl. Qed.
Lemma D_869c0 : decode_any W_869c0 = Some (Op ALU_XOR 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_869c4 : bv 32 := 0x01b67633.
Lemma F_869c4 : fetch_word Ubsan.M.loaded_segments (0x869c4 : word) = Some W_869c4.
Proof. vm_refl. Qed.
Lemma D_869c4 : decode_any W_869c4 = Some (Op ALU_AND 12 12 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_869c8 : bv 32 := 0x01166633.
Lemma F_869c8 : fetch_word Ubsan.M.loaded_segments (0x869c8 : word) = Some W_869c8.
Proof. vm_refl. Qed.
Lemma D_869c8 : decode_any W_869c8 = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_869cc : bv 32 := 0x01038ab3.
Lemma F_869cc : fetch_word Ubsan.M.loaded_segments (0x869cc : word) = Some W_869cc.
Proof. vm_refl. Qed.
Lemma D_869cc : decode_any W_869cc = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_869d0 : bv 32 := 0x00cca023.
Lemma F_869d0 : fetch_word Ubsan.M.loaded_segments (0x869d0 : word) = Some W_869d0.
Proof. vm_refl. Qed.
Lemma D_869d0 : decode_any W_869d0 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_869d4 : bv 32 := 0x000a9463.
Lemma F_869d4 : fetch_word Ubsan.M.loaded_segments (0x869d4 : word) = Some W_869d4.
Proof. vm_refl. Qed.
Lemma D_869d4 : decode_any W_869d4 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_869d8 : bv 32 := 0xb1dfb06f.
Lemma F_869d8 : fetch_word Ubsan.M.loaded_segments (0x869d8 : word) = Some W_869d8.
Proof. vm_refl. Qed.
Lemma D_869d8 : decode_any W_869d8 = Some (Jal 0 2079516, 4%Z).
Proof. vm_refl. Qed.

Definition W_869dc : bv 32 := 0x010ab633.
Lemma F_869dc : fetch_word Ubsan.M.loaded_segments (0x869dc : word) = Some W_869dc.
Proof. vm_refl. Qed.
Lemma D_869dc : decode_any W_869dc = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_869e0 : bv 32 := 0x00964633.
Lemma F_869e0 : fetch_word Ubsan.M.loaded_segments (0x869e0 : word) = Some W_869e0.
Proof. vm_refl. Qed.
Lemma D_869e0 : decode_any W_869e0 = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_869e4 : bv 32 := 0x00164613.
Lemma F_869e4 : fetch_word Ubsan.M.loaded_segments (0x869e4 : word) = Some W_869e4.
Proof. vm_refl. Qed.
Lemma D_869e4 : decode_any W_869e4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_869e8 : bv 32 := 0x00061463.
Lemma F_869e8 : fetch_word Ubsan.M.loaded_segments (0x869e8 : word) = Some W_869e8.
Proof. vm_refl. Qed.
Lemma D_869e8 : decode_any W_869e8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_869ec : bv 32 := 0xb09fb06f.
Lemma F_869ec : fetch_word Ubsan.M.loaded_segments (0x869ec : word) = Some W_869ec.
Proof. vm_refl. Qed.
Lemma D_869ec : decode_any W_869ec = Some (Jal 0 2079496, 4%Z).
Proof. vm_refl. Qed.

Definition W_869f0 : bv 32 := 0x00ba0633.
Lemma F_869f0 : fetch_word Ubsan.M.loaded_segments (0x869f0 : word) = Some W_869f0.
Proof. vm_refl. Qed.
Lemma D_869f0 : decode_any W_869f0 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_869f4 : bv 32 := 0x00061463.
Lemma F_869f4 : fetch_word Ubsan.M.loaded_segments (0x869f4 : word) = Some W_869f4.
Proof. vm_refl. Qed.
Lemma D_869f4 : decode_any W_869f4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_869f8 : bv 32 := 0xafdfb06f.
Lemma F_869f8 : fetch_word Ubsan.M.loaded_segments (0x869f8 : word) = Some W_869f8.
Proof. vm_refl. Qed.
Lemma D_869f8 : decode_any W_869f8 = Some (Jal 0 2079484, 4%Z).
Proof. vm_refl. Qed.

Definition W_869fc : bv 32 := 0x01a63633.
Lemma F_869fc : fetch_word Ubsan.M.loaded_segments (0x869fc : word) = Some W_869fc.
Proof. vm_refl. Qed.
Lemma D_869fc : decode_any W_869fc = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a00 : bv 32 := 0x07813803.
Lemma F_86a00 : fetch_word Ubsan.M.loaded_segments (0x86a00 : word) = Some W_86a00.
Proof. vm_refl. Qed.
Lemma D_86a00 : decode_any W_86a00 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a04 : bv 32 := 0x01064633.
Lemma F_86a04 : fetch_word Ubsan.M.loaded_segments (0x86a04 : word) = Some W_86a04.
Proof. vm_refl. Qed.
Lemma D_86a04 : decode_any W_86a04 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a08 : bv 32 := 0x00164613.
Lemma F_86a08 : fetch_word Ubsan.M.loaded_segments (0x86a08 : word) = Some W_86a08.
Proof. vm_refl. Qed.
Lemma D_86a08 : decode_any W_86a08 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a0c : bv 32 := 0x00061463.
Lemma F_86a0c : fetch_word Ubsan.M.loaded_segments (0x86a0c : word) = Some W_86a0c.
Proof. vm_refl. Qed.
Lemma D_86a0c : decode_any W_86a0c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a10 : bv 32 := 0xae5fb06f.
Lemma F_86a10 : fetch_word Ubsan.M.loaded_segments (0x86a10 : word) = Some W_86a10.
Proof. vm_refl. Qed.
Lemma D_86a10 : decode_any W_86a10 = Some (Jal 0 2079460, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a14 : bv 32 := 0x001e0e1b.
Lemma F_86a14 : fetch_word Ubsan.M.loaded_segments (0x86a14 : word) = Some W_86a14.
Proof. vm_refl. Qed.
Lemma D_86a14 : decode_any W_86a14 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a18 : bv 32 := 0x00d585b3.
Lemma F_86a18 : fetch_word Ubsan.M.loaded_segments (0x86a18 : word) = Some W_86a18.
Proof. vm_refl. Qed.
Lemma D_86a18 : decode_any W_86a18 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a1c : bv 32 := 0x007c8cb3.
Lemma F_86a1c : fetch_word Ubsan.M.loaded_segments (0x86a1c : word) = Some W_86a1c.
Proof. vm_refl. Qed.
Lemma D_86a1c : decode_any W_86a1c = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a20 : bv 32 := 0x000a8813.
Lemma F_86a20 : fetch_word Ubsan.M.loaded_segments (0x86a20 : word) = Some W_86a20.
Proof. vm_refl. Qed.
Lemma D_86a20 : decode_any W_86a20 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a24 : bv 32 := 0xf00e16e3.
Lemma F_86a24 : fetch_word Ubsan.M.loaded_segments (0x86a24 : word) = Some W_86a24.
Proof. vm_refl. Qed.
Lemma D_86a24 : decode_any W_86a24 = Some (Branch BC_NE 28 0 7948, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a28 : bv 32 := 0x02013583.
Lemma F_86a28 : fetch_word Ubsan.M.loaded_segments (0x86a28 : word) = Some W_86a28.
Proof. vm_refl. Qed.
Lemma D_86a28 : decode_any W_86a28 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a2c : bv 32 := 0x16059c63.
Lemma F_86a2c : fetch_word Ubsan.M.loaded_segments (0x86a2c : word) = Some W_86a2c.
Proof. vm_refl. Qed.
Lemma D_86a2c : decode_any W_86a2c = Some (Branch BC_NE 11 0 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a30 : bv 32 := 0xffffc693.
Lemma F_86a30 : fetch_word Ubsan.M.loaded_segments (0x86a30 : word) = Some W_86a30.
Proof. vm_refl. Qed.
Lemma D_86a30 : decode_any W_86a30 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a34 : bv 32 := 0x00271293.
Lemma F_86a34 : fetch_word Ubsan.M.loaded_segments (0x86a34 : word) = Some W_86a34.
Proof. vm_refl. Qed.
Lemma D_86a34 : decode_any W_86a34 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a38 : bv 32 := 0x05813383.
Lemma F_86a38 : fetch_word Ubsan.M.loaded_segments (0x86a38 : word) = Some W_86a38.
Proof. vm_refl. Qed.
Lemma D_86a38 : decode_any W_86a38 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a3c : bv 32 := 0x00239393.
Lemma F_86a3c : fetch_word Ubsan.M.loaded_segments (0x86a3c : word) = Some W_86a3c.
Proof. vm_refl. Qed.
Lemma D_86a3c : decode_any W_86a3c = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a40 : bv 32 := 0x00337613.
Lemma F_86a40 : fetch_word Ubsan.M.loaded_segments (0x86a40 : word) = Some W_86a40.
Proof. vm_refl. Qed.
Lemma D_86a40 : decode_any W_86a40 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a44 : bv 32 := 0x00397793.
Lemma F_86a44 : fetch_word Ubsan.M.loaded_segments (0x86a44 : word) = Some W_86a44.
Proof. vm_refl. Qed.
Lemma D_86a44 : decode_any W_86a44 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a48 : bv 32 := 0x07013a03.
Lemma F_86a48 : fetch_word Ubsan.M.loaded_segments (0x86a48 : word) = Some W_86a48.
Proof. vm_refl. Qed.
Lemma D_86a48 : decode_any W_86a48 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a4c : bv 32 := 0x002a1a13.
Lemma F_86a4c : fetch_word Ubsan.M.loaded_segments (0x86a4c : word) = Some W_86a4c.
Proof. vm_refl. Qed.
Lemma D_86a4c : decode_any W_86a4c = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a50 : bv 32 := 0x00072b93.
Lemma F_86a50 : fetch_word Ubsan.M.loaded_segments (0x86a50 : word) = Some W_86a50.
Proof. vm_refl. Qed.
Lemma D_86a50 : decode_any W_86a50 = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a54 : bv 32 := 0x02000c93.
Lemma F_86a54 : fetch_word Ubsan.M.loaded_segments (0x86a54 : word) = Some W_86a54.
Proof. vm_refl. Qed.
Lemma D_86a54 : decode_any W_86a54 = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a58 : bv 32 := 0xffb00d13.
Lemma F_86a58 : fetch_word Ubsan.M.loaded_segments (0x86a58 : word) = Some W_86a58.
Proof. vm_refl. Qed.
Lemma D_86a58 : decode_any W_86a58 = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a5c : bv 32 := 0x0017b793.
Lemma F_86a5c : fetch_word Ubsan.M.loaded_segments (0x86a5c : word) = Some W_86a5c.
Proof. vm_refl. Qed.
Lemma D_86a5c : decode_any W_86a5c = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a60 : bv 32 := 0x02f13023.
Lemma F_86a60 : fetch_word Ubsan.M.loaded_segments (0x86a60 : word) = Some W_86a60.
Proof. vm_refl. Qed.
Lemma D_86a60 : decode_any W_86a60 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a64 : bv 32 := 0x00163613.
Lemma F_86a64 : fetch_word Ubsan.M.loaded_segments (0x86a64 : word) = Some W_86a64.
Proof. vm_refl. Qed.
Lemma D_86a64 : decode_any W_86a64 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a68 : bv 32 := 0x00c13823.
Lemma F_86a68 : fetch_word Ubsan.M.loaded_segments (0x86a68 : word) = Some W_86a68.
Proof. vm_refl. Qed.
Lemma D_86a68 : decode_any W_86a68 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a6c : bv 32 := 0x01f00093.
Lemma F_86a6c : fetch_word Ubsan.M.loaded_segments (0x86a6c : word) = Some W_86a6c.
Proof. vm_refl. Qed.
Lemma D_86a6c : decode_any W_86a6c = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a70 : bv 32 := 0x00030b13.
Lemma F_86a70 : fetch_word Ubsan.M.loaded_segments (0x86a70 : word) = Some W_86a70.
Proof. vm_refl. Qed.
Lemma D_86a70 : decode_any W_86a70 = Some (OpImm ALU_ADD 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a74 : bv 32 := 0x00090c13.
Lemma F_86a74 : fetch_word Ubsan.M.loaded_segments (0x86a74 : word) = Some W_86a74.
Proof. vm_refl. Qed.
Lemma D_86a74 : decode_any W_86a74 = Some (OpImm ALU_ADD 24 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a78 : bv 32 := 0x07013603.
Lemma F_86a78 : fetch_word Ubsan.M.loaded_segments (0x86a78 : word) = Some W_86a78.
Proof. vm_refl. Qed.
Lemma D_86a78 : decode_any W_86a78 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a7c : bv 32 := 0x0a060c63.
Lemma F_86a7c : fetch_word Ubsan.M.loaded_segments (0x86a7c : word) = Some W_86a7c.
Proof. vm_refl. Qed.
Lemma D_86a7c : decode_any W_86a7c = Some (Branch BC_EQ 12 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a80 : bv 32 := 0x00000993.
Lemma F_86a80 : fetch_word Ubsan.M.loaded_segments (0x86a80 : word) = Some W_86a80.
Proof. vm_refl. Qed.
Lemma D_86a80 : decode_any W_86a80 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a84 : bv 32 := 0x00603833.
Lemma F_86a84 : fetch_word Ubsan.M.loaded_segments (0x86a84 : word) = Some W_86a84.
Proof. vm_refl. Qed.
Lemma D_86a84 : decode_any W_86a84 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a88 : bv 32 := 0x01203e33.
Lemma F_86a88 : fetch_word Ubsan.M.loaded_segments (0x86a88 : word) = Some W_86a88.
Proof. vm_refl. Qed.
Lemma D_86a88 : decode_any W_86a88 = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a8c : bv 32 := 0x01013603.
Lemma F_86a8c : fetch_word Ubsan.M.loaded_segments (0x86a8c : word) = Some W_86a8c.
Proof. vm_refl. Qed.
Lemma D_86a8c : decode_any W_86a8c = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a90 : bv 32 := 0x010674b3.
Lemma F_86a90 : fetch_word Ubsan.M.loaded_segments (0x86a90 : word) = Some W_86a90.
Proof. vm_refl. Qed.
Lemma D_86a90 : decode_any W_86a90 = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a94 : bv 32 := 0x02013603.
Lemma F_86a94 : fetch_word Ubsan.M.loaded_segments (0x86a94 : word) = Some W_86a94.
Proof. vm_refl. Qed.
Lemma D_86a94 : decode_any W_86a94 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a98 : bv 32 := 0x01c67ab3.
Lemma F_86a98 : fetch_word Ubsan.M.loaded_segments (0x86a98 : word) = Some W_86a98.
Proof. vm_refl. Qed.
Lemma D_86a98 : decode_any W_86a98 = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86a9c : bv 32 := 0x013b0633.
Lemma F_86a9c : fetch_word Ubsan.M.loaded_segments (0x86a9c : word) = Some W_86a9c.
Proof. vm_refl. Qed.
Lemma D_86a9c : decode_any W_86a9c = Some (Op ALU_ADD 12 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86aa0 : bv 32 := 0x00667463.
Lemma F_86aa0 : fetch_word Ubsan.M.loaded_segments (0x86aa0 : word) = Some W_86aa0.
Proof. vm_refl. Qed.
Lemma D_86aa0 : decode_any W_86aa0 = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86aa4 : bv 32 := 0xa51fb06f.
Lemma F_86aa4 : fetch_word Ubsan.M.loaded_segments (0x86aa4 : word) = Some W_86aa4.
Proof. vm_refl. Qed.
Lemma D_86aa4 : decode_any W_86aa4 = Some (Jal 0 2079312, 4%Z).
Proof. vm_refl. Qed.

Definition W_86aa8 : bv 32 := 0x00163613.
Lemma F_86aa8 : fetch_word Ubsan.M.loaded_segments (0x86aa8 : word) = Some W_86aa8.
Proof. vm_refl. Qed.
Lemma D_86aa8 : decode_any W_86aa8 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86aac : bv 32 := 0x00c84633.
Lemma F_86aac : fetch_word Ubsan.M.loaded_segments (0x86aac : word) = Some W_86aac.
Proof. vm_refl. Qed.
Lemma D_86aac : decode_any W_86aac = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ab0 : bv 32 := 0x00061463.
Lemma F_86ab0 : fetch_word Ubsan.M.loaded_segments (0x86ab0 : word) = Some W_86ab0.
Proof. vm_refl. Qed.
Lemma D_86ab0 : decode_any W_86ab0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ab4 : bv 32 := 0xa41fb06f.
Lemma F_86ab4 : fetch_word Ubsan.M.loaded_segments (0x86ab4 : word) = Some W_86ab4.
Proof. vm_refl. Qed.
Lemma D_86ab4 : decode_any W_86ab4 = Some (Jal 0 2079296, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ab8 : bv 32 := 0x00049463.
Lemma F_86ab8 : fetch_word Ubsan.M.loaded_segments (0x86ab8 : word) = Some W_86ab8.
Proof. vm_refl. Qed.
Lemma D_86ab8 : decode_any W_86ab8 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86abc : bv 32 := 0xa39fb06f.
Lemma F_86abc : fetch_word Ubsan.M.loaded_segments (0x86abc : word) = Some W_86abc.
Proof. vm_refl. Qed.
Lemma D_86abc : decode_any W_86abc = Some (Jal 0 2079288, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ac0 : bv 32 := 0x019f1463.
Lemma F_86ac0 : fetch_word Ubsan.M.loaded_segments (0x86ac0 : word) = Some W_86ac0.
Proof. vm_refl. Qed.
Lemma D_86ac0 : decode_any W_86ac0 = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ac4 : bv 32 := 0xa31fb06f.
Lemma F_86ac4 : fetch_word Ubsan.M.loaded_segments (0x86ac4 : word) = Some W_86ac4.
Proof. vm_refl. Qed.
Lemma D_86ac4 : decode_any W_86ac4 = Some (Jal 0 2079280, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ac8 : bv 32 := 0x01330633.
Lemma F_86ac8 : fetch_word Ubsan.M.loaded_segments (0x86ac8 : word) = Some W_86ac8.
Proof. vm_refl. Qed.
Lemma D_86ac8 : decode_any W_86ac8 = Some (Op ALU_ADD 12 6 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86acc : bv 32 := 0x00cd7463.
Lemma F_86acc : fetch_word Ubsan.M.loaded_segments (0x86acc : word) = Some W_86acc.
Proof. vm_refl. Qed.
Lemma D_86acc : decode_any W_86acc = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ad0 : bv 32 := 0xa25fb06f.
Lemma F_86ad0 : fetch_word Ubsan.M.loaded_segments (0x86ad0 : word) = Some W_86ad0.
Proof. vm_refl. Qed.
Lemma D_86ad0 : decode_any W_86ad0 = Some (Jal 0 2079268, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ad4 : bv 32 := 0x0080f463.
Lemma F_86ad4 : fetch_word Ubsan.M.loaded_segments (0x86ad4 : word) = Some W_86ad4.
Proof. vm_refl. Qed.
Lemma D_86ad4 : decode_any W_86ad4 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ad8 : bv 32 := 0xa1dfb06f.
Lemma F_86ad8 : fetch_word Ubsan.M.loaded_segments (0x86ad8 : word) = Some W_86ad8.
Proof. vm_refl. Qed.
Lemma D_86ad8 : decode_any W_86ad8 = Some (Jal 0 2079260, 4%Z).
Proof. vm_refl. Qed.

Definition W_86adc : bv 32 := 0x013c07b3.
Lemma F_86adc : fetch_word Ubsan.M.loaded_segments (0x86adc : word) = Some W_86adc.
Proof. vm_refl. Qed.
Lemma D_86adc : decode_any W_86adc = Some (Op ALU_ADD 15 24 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ae0 : bv 32 := 0x0127f463.
Lemma F_86ae0 : fetch_word Ubsan.M.loaded_segments (0x86ae0 : word) = Some W_86ae0.
Proof. vm_refl. Qed.
Lemma D_86ae0 : decode_any W_86ae0 = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ae4 : bv 32 := 0xa11fb06f.
Lemma F_86ae4 : fetch_word Ubsan.M.loaded_segments (0x86ae4 : word) = Some W_86ae4.
Proof. vm_refl. Qed.
Lemma D_86ae4 : decode_any W_86ae4 = Some (Jal 0 2079248, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ae8 : bv 32 := 0x0017b793.
Lemma F_86ae8 : fetch_word Ubsan.M.loaded_segments (0x86ae8 : word) = Some W_86ae8.
Proof. vm_refl. Qed.
Lemma D_86ae8 : decode_any W_86ae8 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86aec : bv 32 := 0x00fe47b3.
Lemma F_86aec : fetch_word Ubsan.M.loaded_segments (0x86aec : word) = Some W_86aec.
Proof. vm_refl. Qed.
Lemma D_86aec : decode_any W_86aec = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86af0 : bv 32 := 0x00079463.
Lemma F_86af0 : fetch_word Ubsan.M.loaded_segments (0x86af0 : word) = Some W_86af0.
Proof. vm_refl. Qed.
Lemma D_86af0 : decode_any W_86af0 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86af4 : bv 32 := 0xa01fb06f.
Lemma F_86af4 : fetch_word Ubsan.M.loaded_segments (0x86af4 : word) = Some W_86af4.
Proof. vm_refl. Qed.
Lemma D_86af4 : decode_any W_86af4 = Some (Jal 0 2079232, 4%Z).
Proof. vm_refl. Qed.

Definition W_86af8 : bv 32 := 0x000a9463.
Lemma F_86af8 : fetch_word Ubsan.M.loaded_segments (0x86af8 : word) = Some W_86af8.
Proof. vm_refl. Qed.
Lemma D_86af8 : decode_any W_86af8 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86afc : bv 32 := 0x9f9fb06f.
Lemma F_86afc : fetch_word Ubsan.M.loaded_segments (0x86afc : word) = Some W_86afc.
Proof. vm_refl. Qed.
Lemma D_86afc : decode_any W_86afc = Some (Jal 0 2079224, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b00 : bv 32 := 0x00062783.
Lemma F_86b00 : fetch_word Ubsan.M.loaded_segments (0x86b00 : word) = Some W_86b00.
Proof. vm_refl. Qed.
Lemma D_86b00 : decode_any W_86b00 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b04 : bv 32 := 0x00462603.
Lemma F_86b04 : fetch_word Ubsan.M.loaded_segments (0x86b04 : word) = Some W_86b04.
Proof. vm_refl. Qed.
Lemma D_86b04 : decode_any W_86b04 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b08 : bv 32 := 0x013908b3.
Lemma F_86b08 : fetch_word Ubsan.M.loaded_segments (0x86b08 : word) = Some W_86b08.
Proof. vm_refl. Qed.
Lemma D_86b08 : decode_any W_86b08 = Some (Op ALU_ADD 17 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b0c : bv 32 := 0x0008ad83.
Lemma F_86b0c : fetch_word Ubsan.M.loaded_segments (0x86b0c : word) = Some W_86b0c.
Proof. vm_refl. Qed.
Lemma D_86b0c : decode_any W_86b0c = Some (Load SZ4 true 27 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b10 : bv 32 := 0x01d797bb.
Lemma F_86b10 : fetch_word Ubsan.M.loaded_segments (0x86b10 : word) = Some W_86b10.
Proof. vm_refl. Qed.
Lemma D_86b10 : decode_any W_86b10 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b14 : bv 32 := 0x0086563b.
Lemma F_86b14 : fetch_word Ubsan.M.loaded_segments (0x86b14 : word) = Some W_86b14.
Proof. vm_refl. Qed.
Lemma D_86b14 : decode_any W_86b14 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b18 : bv 32 := 0x00d7f7b3.
Lemma F_86b18 : fetch_word Ubsan.M.loaded_segments (0x86b18 : word) = Some W_86b18.
Proof. vm_refl. Qed.
Lemma D_86b18 : decode_any W_86b18 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b1c : bv 32 := 0x01f67633.
Lemma F_86b1c : fetch_word Ubsan.M.loaded_segments (0x86b1c : word) = Some W_86b1c.
Proof. vm_refl. Qed.
Lemma D_86b1c : decode_any W_86b1c = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b20 : bv 32 := 0x00f66633.
Lemma F_86b20 : fetch_word Ubsan.M.loaded_segments (0x86b20 : word) = Some W_86b20.
Proof. vm_refl. Qed.
Lemma D_86b20 : decode_any W_86b20 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b24 : bv 32 := 0x00cdc633.
Lemma F_86b24 : fetch_word Ubsan.M.loaded_segments (0x86b24 : word) = Some W_86b24.
Proof. vm_refl. Qed.
Lemma D_86b24 : decode_any W_86b24 = Some (Op ALU_XOR 12 27 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b28 : bv 32 := 0x00498993.
Lemma F_86b28 : fetch_word Ubsan.M.loaded_segments (0x86b28 : word) = Some W_86b28.
Proof. vm_refl. Qed.
Lemma D_86b28 : decode_any W_86b28 = Some (OpImm ALU_ADD 19 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b2c : bv 32 := 0x00c8a023.
Lemma F_86b2c : fetch_word Ubsan.M.loaded_segments (0x86b2c : word) = Some W_86b2c.
Proof. vm_refl. Qed.
Lemma D_86b2c : decode_any W_86b2c = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b30 : bv 32 := 0xf73a16e3.
Lemma F_86b30 : fetch_word Ubsan.M.loaded_segments (0x86b30 : word) = Some W_86b30.
Proof. vm_refl. Qed.
Lemma D_86b30 : decode_any W_86b30 = Some (Branch BC_NE 20 19 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b34 : bv 32 := 0x00590633.
Lemma F_86b34 : fetch_word Ubsan.M.loaded_segments (0x86b34 : word) = Some W_86b34.
Proof. vm_refl. Qed.
Lemma D_86b34 : decode_any W_86b34 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b38 : bv 32 := 0x012037b3.
Lemma F_86b38 : fetch_word Ubsan.M.loaded_segments (0x86b38 : word) = Some W_86b38.
Proof. vm_refl. Qed.
Lemma D_86b38 : decode_any W_86b38 = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b3c : bv 32 := 0x00163813.
Lemma F_86b3c : fetch_word Ubsan.M.loaded_segments (0x86b3c : word) = Some W_86b3c.
Proof. vm_refl. Qed.
Lemma D_86b3c : decode_any W_86b3c = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b40 : bv 32 := 0x01079463.
Lemma F_86b40 : fetch_word Ubsan.M.loaded_segments (0x86b40 : word) = Some W_86b40.
Proof. vm_refl. Qed.
Lemma D_86b40 : decode_any W_86b40 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b44 : bv 32 := 0x9b1fb06f.
Lemma F_86b44 : fetch_word Ubsan.M.loaded_segments (0x86b44 : word) = Some W_86b44.
Proof. vm_refl. Qed.
Lemma D_86b44 : decode_any W_86b44 = Some (Jal 0 2079152, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b48 : bv 32 := 0x01263633.
Lemma F_86b48 : fetch_word Ubsan.M.loaded_segments (0x86b48 : word) = Some W_86b48.
Proof. vm_refl. Qed.
Lemma D_86b48 : decode_any W_86b48 = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b4c : bv 32 := 0x01764633.
Lemma F_86b4c : fetch_word Ubsan.M.loaded_segments (0x86b4c : word) = Some W_86b4c.
Proof. vm_refl. Qed.
Lemma D_86b4c : decode_any W_86b4c = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b50 : bv 32 := 0x00164613.
Lemma F_86b50 : fetch_word Ubsan.M.loaded_segments (0x86b50 : word) = Some W_86b50.
Proof. vm_refl. Qed.
Lemma D_86b50 : decode_any W_86b50 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b54 : bv 32 := 0x00061463.
Lemma F_86b54 : fetch_word Ubsan.M.loaded_segments (0x86b54 : word) = Some W_86b54.
Proof. vm_refl. Qed.
Lemma D_86b54 : decode_any W_86b54 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b58 : bv 32 := 0x99dfb06f.
Lemma F_86b58 : fetch_word Ubsan.M.loaded_segments (0x86b58 : word) = Some W_86b58.
Proof. vm_refl. Qed.
Lemma D_86b58 : decode_any W_86b58 = Some (Jal 0 2079132, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b5c : bv 32 := 0x00638633.
Lemma F_86b5c : fetch_word Ubsan.M.loaded_segments (0x86b5c : word) = Some W_86b5c.
Proof. vm_refl. Qed.
Lemma D_86b5c : decode_any W_86b5c = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b60 : bv 32 := 0x006037b3.
Lemma F_86b60 : fetch_word Ubsan.M.loaded_segments (0x86b60 : word) = Some W_86b60.
Proof. vm_refl. Qed.
Lemma D_86b60 : decode_any W_86b60 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b64 : bv 32 := 0x00163813.
Lemma F_86b64 : fetch_word Ubsan.M.loaded_segments (0x86b64 : word) = Some W_86b64.
Proof. vm_refl. Qed.
Lemma D_86b64 : decode_any W_86b64 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b68 : bv 32 := 0x01079463.
Lemma F_86b68 : fetch_word Ubsan.M.loaded_segments (0x86b68 : word) = Some W_86b68.
Proof. vm_refl. Qed.
Lemma D_86b68 : decode_any W_86b68 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b6c : bv 32 := 0x989fb06f.
Lemma F_86b6c : fetch_word Ubsan.M.loaded_segments (0x86b6c : word) = Some W_86b6c.
Proof. vm_refl. Qed.
Lemma D_86b6c : decode_any W_86b6c = Some (Jal 0 2079112, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b70 : bv 32 := 0x006637b3.
Lemma F_86b70 : fetch_word Ubsan.M.loaded_segments (0x86b70 : word) = Some W_86b70.
Proof. vm_refl. Qed.
Lemma D_86b70 : decode_any W_86b70 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b74 : bv 32 := 0x07813803.
Lemma F_86b74 : fetch_word Ubsan.M.loaded_segments (0x86b74 : word) = Some W_86b74.
Proof. vm_refl. Qed.
Lemma D_86b74 : decode_any W_86b74 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b78 : bv 32 := 0x0107c7b3.
Lemma F_86b78 : fetch_word Ubsan.M.loaded_segments (0x86b78 : word) = Some W_86b78.
Proof. vm_refl. Qed.
Lemma D_86b78 : decode_any W_86b78 = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b7c : bv 32 := 0x0017c793.
Lemma F_86b7c : fetch_word Ubsan.M.loaded_segments (0x86b7c : word) = Some W_86b7c.
Proof. vm_refl. Qed.
Lemma D_86b7c : decode_any W_86b7c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b80 : bv 32 := 0x00079463.
Lemma F_86b80 : fetch_word Ubsan.M.loaded_segments (0x86b80 : word) = Some W_86b80.
Proof. vm_refl. Qed.
Lemma D_86b80 : decode_any W_86b80 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b84 : bv 32 := 0x971fb06f.
Lemma F_86b84 : fetch_word Ubsan.M.loaded_segments (0x86b84 : word) = Some W_86b84.
Proof. vm_refl. Qed.
Lemma D_86b84 : decode_any W_86b84 = Some (Jal 0 2079088, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b88 : bv 32 := 0x00590933.
Lemma F_86b88 : fetch_word Ubsan.M.loaded_segments (0x86b88 : word) = Some W_86b88.
Proof. vm_refl. Qed.
Lemma D_86b88 : decode_any W_86b88 = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b8c : bv 32 := 0x0015859b.
Lemma F_86b8c : fetch_word Ubsan.M.loaded_segments (0x86b8c : word) = Some W_86b8c.
Proof. vm_refl. Qed.
Lemma D_86b8c : decode_any W_86b8c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b90 : bv 32 := 0x005c0c33.
Lemma F_86b90 : fetch_word Ubsan.M.loaded_segments (0x86b90 : word) = Some W_86b90.
Proof. vm_refl. Qed.
Lemma D_86b90 : decode_any W_86b90 = Some (Op ALU_ADD 24 24 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b94 : bv 32 := 0x007b0b33.
Lemma F_86b94 : fetch_word Ubsan.M.loaded_segments (0x86b94 : word) = Some W_86b94.
Proof. vm_refl. Qed.
Lemma D_86b94 : decode_any W_86b94 = Some (Op ALU_ADD 22 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b98 : bv 32 := 0x00060313.
Lemma F_86b98 : fetch_word Ubsan.M.loaded_segments (0x86b98 : word) = Some W_86b98.
Proof. vm_refl. Qed.
Lemma D_86b98 : decode_any W_86b98 = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b9c : bv 32 := 0x08013603.
Lemma F_86b9c : fetch_word Ubsan.M.loaded_segments (0x86b9c : word) = Some W_86b9c.
Proof. vm_refl. Qed.
Lemma D_86b9c : decode_any W_86b9c = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ba0 : bv 32 := 0xecc59ce3.
Lemma F_86ba0 : fetch_word Ubsan.M.loaded_segments (0x86ba0 : word) = Some W_86ba0.
Proof. vm_refl. Qed.
Lemma D_86ba0 : decode_any W_86ba0 = Some (Branch BC_NE 11 12 7896, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ba4 : bv 32 := 0x01813583.
Lemma F_86ba4 : fetch_word Ubsan.M.loaded_segments (0x86ba4 : word) = Some W_86ba4.
Proof. vm_refl. Qed.
Lemma D_86ba4 : decode_any W_86ba4 = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ba8 : bv 32 := 0x200598e3.
Lemma F_86ba8 : fetch_word Ubsan.M.loaded_segments (0x86ba8 : word) = Some W_86ba8.
Proof. vm_refl. Qed.
Lemma D_86ba8 : decode_any W_86ba8 = Some (Branch BC_NE 11 0 2576, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bac : bv 32 := 0x06813583.
Lemma F_86bac : fetch_word Ubsan.M.loaded_segments (0x86bac : word) = Some W_86bac.
Proof. vm_refl. Qed.
Lemma D_86bac : decode_any W_86bac = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bb0 : bv 32 := 0x0035f593.
Lemma F_86bb0 : fetch_word Ubsan.M.loaded_segments (0x86bb0 : word) = Some W_86bb0.
Proof. vm_refl. Qed.
Lemma D_86bb0 : decode_any W_86bb0 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bb4 : bv 32 := 0x00058463.
Lemma F_86bb4 : fetch_word Ubsan.M.loaded_segments (0x86bb4 : word) = Some W_86bb4.
Proof. vm_refl. Qed.
Lemma D_86bb4 : decode_any W_86bb4 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bb8 : bv 32 := 0x93dfb06f.
Lemma F_86bb8 : fetch_word Ubsan.M.loaded_segments (0x86bb8 : word) = Some W_86bb8.
Proof. vm_refl. Qed.
Lemma D_86bb8 : decode_any W_86bb8 = Some (Jal 0 2079036, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bbc : bv 32 := 0xffffc613.
Lemma F_86bbc : fetch_word Ubsan.M.loaded_segments (0x86bbc : word) = Some W_86bbc.
Proof. vm_refl. Qed.
Lemma D_86bbc : decode_any W_86bbc = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bc0 : bv 32 := 0x06013683.
Lemma F_86bc0 : fetch_word Ubsan.M.loaded_segments (0x86bc0 : word) = Some W_86bc0.
Proof. vm_refl. Qed.
Lemma D_86bc0 : decode_any W_86bc0 = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bc4 : bv 32 := 0xfff6c693.
Lemma F_86bc4 : fetch_word Ubsan.M.loaded_segments (0x86bc4 : word) = Some W_86bc4.
Proof. vm_refl. Qed.
Lemma D_86bc4 : decode_any W_86bc4 = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bc8 : bv 32 := 0x00271793.
Lemma F_86bc8 : fetch_word Ubsan.M.loaded_segments (0x86bc8 : word) = Some W_86bc8.
Proof. vm_refl. Qed.
Lemma D_86bc8 : decode_any W_86bc8 = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bcc : bv 32 := 0x05813303.
Lemma F_86bcc : fetch_word Ubsan.M.loaded_segments (0x86bcc : word) = Some W_86bcc.
Proof. vm_refl. Qed.
Lemma D_86bcc : decode_any W_86bcc = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bd0 : bv 32 := 0x00231313.
Lemma F_86bd0 : fetch_word Ubsan.M.loaded_segments (0x86bd0 : word) = Some W_86bd0.
Proof. vm_refl. Qed.
Lemma D_86bd0 : decode_any W_86bd0 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bd4 : bv 32 := 0x00357893.
Lemma F_86bd4 : fetch_word Ubsan.M.loaded_segments (0x86bd4 : word) = Some W_86bd4.
Proof. vm_refl. Qed.
Lemma D_86bd4 : decode_any W_86bd4 = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bd8 : bv 32 := 0x05013903.
Lemma F_86bd8 : fetch_word Ubsan.M.loaded_segments (0x86bd8 : word) = Some W_86bd8.
Proof. vm_refl. Qed.
Lemma D_86bd8 : decode_any W_86bd8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bdc : bv 32 := 0x02813803.
Lemma F_86bdc : fetch_word Ubsan.M.loaded_segments (0x86bdc : word) = Some W_86bdc.
Proof. vm_refl. Qed.
Lemma D_86bdc : decode_any W_86bdc = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86be0 : bv 32 := 0x412804bb.
Lemma F_86be0 : fetch_word Ubsan.M.loaded_segments (0x86be0 : word) = Some W_86be0.
Proof. vm_refl. Qed.
Lemma D_86be0 : decode_any W_86be0 = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86be4 : bv 32 := 0x03813383.
Lemma F_86be4 : fetch_word Ubsan.M.loaded_segments (0x86be4 : word) = Some W_86be4.
Proof. vm_refl. Qed.
Lemma D_86be4 : decode_any W_86be4 = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_86be8 : bv 32 := 0x03013803.
Lemma F_86be8 : fetch_word Ubsan.M.loaded_segments (0x86be8 : word) = Some W_86be8.
Proof. vm_refl. Qed.
Lemma D_86be8 : decode_any W_86be8 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bec : bv 32 := 0x007803b3.
Lemma F_86bec : fetch_word Ubsan.M.loaded_segments (0x86bec : word) = Some W_86bec.
Proof. vm_refl. Qed.
Lemma D_86bec : decode_any W_86bec = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bf0 : bv 32 := 0x04813283.
Lemma F_86bf0 : fetch_word Ubsan.M.loaded_segments (0x86bf0 : word) = Some W_86bf0.
Proof. vm_refl. Qed.
Lemma D_86bf0 : decode_any W_86bf0 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bf4 : bv 32 := 0x43f2d813.
Lemma F_86bf4 : fetch_word Ubsan.M.loaded_segments (0x86bf4 : word) = Some W_86bf4.
Proof. vm_refl. Qed.
Lemma D_86bf4 : decode_any W_86bf4 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bf8 : bv 32 := 0x00587e33.
Lemma F_86bf8 : fetch_word Ubsan.M.loaded_segments (0x86bf8 : word) = Some W_86bf8.
Proof. vm_refl. Qed.
Lemma D_86bf8 : decode_any W_86bf8 = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bfc : bv 32 := 0x02000813.
Lemma F_86bfc : fetch_word Ubsan.M.loaded_segments (0x86bfc : word) = Some W_86bfc.
Proof. vm_refl. Qed.
Lemma D_86bfc : decode_any W_86bfc = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c00 : bv 32 := 0x00813283.
Lemma F_86c00 : fetch_word Ubsan.M.loaded_segments (0x86c00 : word) = Some W_86c00.
Proof. vm_refl. Qed.
Lemma D_86c00 : decode_any W_86c00 = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c04 : bv 32 := 0x0012f293.
Lemma F_86c04 : fetch_word Ubsan.M.loaded_segments (0x86c04 : word) = Some W_86c04.
Proof. vm_refl. Qed.
Lemma D_86c04 : decode_any W_86c04 = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c08 : bv 32 := 0x00072713.
Lemma F_86c08 : fetch_word Ubsan.M.loaded_segments (0x86c08 : word) = Some W_86c08.
Proof. vm_refl. Qed.
Lemma D_86c08 : decode_any W_86c08 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c0c : bv 32 := 0x01c38e33.
Lemma F_86c0c : fetch_word Ubsan.M.loaded_segments (0x86c0c : word) = Some W_86c0c.
Proof. vm_refl. Qed.
Lemma D_86c0c : decode_any W_86c0c = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c10 : bv 32 := 0xffb00393.
Lemma F_86c10 : fetch_word Ubsan.M.loaded_segments (0x86c10 : word) = Some W_86c10.
Proof. vm_refl. Qed.
Lemma D_86c10 : decode_any W_86c10 = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c14 : bv 32 := 0x412e093b.
Lemma F_86c14 : fetch_word Ubsan.M.loaded_segments (0x86c14 : word) = Some W_86c14.
Proof. vm_refl. Qed.
Lemma D_86c14 : decode_any W_86c14 = Some (Op32 ALU_SUB 18 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c18 : bv 32 := 0x06813e03.
Lemma F_86c18 : fetch_word Ubsan.M.loaded_segments (0x86c18 : word) = Some W_86c18.
Proof. vm_refl. Qed.
Lemma D_86c18 : decode_any W_86c18 = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c1c : bv 32 := 0x006e0e33.
Lemma F_86c1c : fetch_word Ubsan.M.loaded_segments (0x86c1c : word) = Some W_86c1c.
Proof. vm_refl. Qed.
Lemma D_86c1c : decode_any W_86c1c = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c20 : bv 32 := 0x04013983.
Lemma F_86c20 : fetch_word Ubsan.M.loaded_segments (0x86c20 : word) = Some W_86c20.
Proof. vm_refl. Qed.
Lemma D_86c20 : decode_any W_86c20 = Some (Load SZ8 true 19 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c24 : bv 32 := 0x4139093b.
Lemma F_86c24 : fetch_word Ubsan.M.loaded_segments (0x86c24 : word) = Some W_86c24.
Proof. vm_refl. Qed.
Lemma D_86c24 : decode_any W_86c24 = Some (Op32 ALU_SUB 18 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c28 : bv 32 := 0x43f95993.
Lemma F_86c28 : fetch_word Ubsan.M.loaded_segments (0x86c28 : word) = Some W_86c28.
Proof. vm_refl. Qed.
Lemma D_86c28 : decode_any W_86c28 = Some (ShiftImm ALU_SRA 19 18 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c2c : bv 32 := 0x0129f933.
Lemma F_86c2c : fetch_word Ubsan.M.loaded_segments (0x86c2c : word) = Some W_86c2c.
Proof. vm_refl. Qed.
Lemma D_86c2c : decode_any W_86c2c = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c30 : bv 32 := 0x412484bb.
Lemma F_86c30 : fetch_word Ubsan.M.loaded_segments (0x86c30 : word) = Some W_86c30.
Proof. vm_refl. Qed.
Lemma D_86c30 : decode_any W_86c30 = Some (Op32 ALU_SUB 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c34 : bv 32 := 0x01f00993.
Lemma F_86c34 : fetch_word Ubsan.M.loaded_segments (0x86c34 : word) = Some W_86c34.
Proof. vm_refl. Qed.
Lemma D_86c34 : decode_any W_86c34 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c38 : bv 32 := 0x00050a13.
Lemma F_86c38 : fetch_word Ubsan.M.loaded_segments (0x86c38 : word) = Some W_86c38.
Proof. vm_refl. Qed.
Lemma D_86c38 : decode_any W_86c38 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c3c : bv 32 := 0x06813a83.
Lemma F_86c3c : fetch_word Ubsan.M.loaded_segments (0x86c3c : word) = Some W_86c3c.
Proof. vm_refl. Qed.
Lemma D_86c3c : decode_any W_86c3c = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c40 : bv 32 := 0x00ba8ab3.
Lemma F_86c40 : fetch_word Ubsan.M.loaded_segments (0x86c40 : word) = Some W_86c40.
Proof. vm_refl. Qed.
Lemma D_86c40 : decode_any W_86c40 = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c44 : bv 32 := 0x000a9463.
Lemma F_86c44 : fetch_word Ubsan.M.loaded_segments (0x86c44 : word) = Some W_86c44.
Proof. vm_refl. Qed.
Lemma D_86c44 : decode_any W_86c44 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c48 : bv 32 := 0x8adfb06f.
Lemma F_86c48 : fetch_word Ubsan.M.loaded_segments (0x86c48 : word) = Some W_86c48.
Proof. vm_refl. Qed.
Lemma D_86c48 : decode_any W_86c48 = Some (Jal 0 2078892, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c4c : bv 32 := 0x010f1463.
Lemma F_86c4c : fetch_word Ubsan.M.loaded_segments (0x86c4c : word) = Some W_86c4c.
Proof. vm_refl. Qed.
Lemma D_86c4c : decode_any W_86c4c = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c50 : bv 32 := 0x8a5fb06f.
Lemma F_86c50 : fetch_word Ubsan.M.loaded_segments (0x86c50 : word) = Some W_86c50.
Proof. vm_refl. Qed.
Lemma D_86c50 : decode_any W_86c50 = Some (Jal 0 2078884, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c54 : bv 32 := 0x000aa903.
Lemma F_86c54 : fetch_word Ubsan.M.loaded_segments (0x86c54 : word) = Some W_86c54.
Proof. vm_refl. Qed.
Lemma D_86c54 : decode_any W_86c54 = Some (Load SZ4 true 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c58 : bv 32 := 0x01d91b3b.
Lemma F_86c58 : fetch_word Ubsan.M.loaded_segments (0x86c58 : word) = Some W_86c58.
Proof. vm_refl. Qed.
Lemma D_86c58 : decode_any W_86c58 = Some (Op32 ALU_SLL 22 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c5c : bv 32 := 0x02029463.
Lemma F_86c5c : fetch_word Ubsan.M.loaded_segments (0x86c5c : word) = Some W_86c5c.
Proof. vm_refl. Qed.
Lemma D_86c5c : decode_any W_86c5c = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c60 : bv 32 := 0x0153f463.
Lemma F_86c60 : fetch_word Ubsan.M.loaded_segments (0x86c60 : word) = Some W_86c60.
Proof. vm_refl. Qed.
Lemma D_86c60 : decode_any W_86c60 = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c64 : bv 32 := 0x891fb06f.
Lemma F_86c64 : fetch_word Ubsan.M.loaded_segments (0x86c64 : word) = Some W_86c64.
Proof. vm_refl. Qed.
Lemma D_86c64 : decode_any W_86c64 = Some (Jal 0 2078864, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c68 : bv 32 := 0x0089f463.
Lemma F_86c68 : fetch_word Ubsan.M.loaded_segments (0x86c68 : word) = Some W_86c68.
Proof. vm_refl. Qed.
Lemma D_86c68 : decode_any W_86c68 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c6c : bv 32 := 0x889fb06f.
Lemma F_86c6c : fetch_word Ubsan.M.loaded_segments (0x86c6c : word) = Some W_86c6c.
Proof. vm_refl. Qed.
Lemma D_86c6c : decode_any W_86c6c = Some (Jal 0 2078856, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c70 : bv 32 := 0x004aa903.
Lemma F_86c70 : fetch_word Ubsan.M.loaded_segments (0x86c70 : word) = Some W_86c70.
Proof. vm_refl. Qed.
Lemma D_86c70 : decode_any W_86c70 = Some (Load SZ4 true 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c74 : bv 32 := 0x00cb7b33.
Lemma F_86c74 : fetch_word Ubsan.M.loaded_segments (0x86c74 : word) = Some W_86c74.
Proof. vm_refl. Qed.
Lemma D_86c74 : decode_any W_86c74 = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c78 : bv 32 := 0x0089593b.
Lemma F_86c78 : fetch_word Ubsan.M.loaded_segments (0x86c78 : word) = Some W_86c78.
Proof. vm_refl. Qed.
Lemma D_86c78 : decode_any W_86c78 = Some (Op32 ALU_SRL 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c7c : bv 32 := 0x01f97933.
Lemma F_86c7c : fetch_word Ubsan.M.loaded_segments (0x86c7c : word) = Some W_86c7c.
Proof. vm_refl. Qed.
Lemma D_86c7c : decode_any W_86c7c = Some (Op ALU_AND 18 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c80 : bv 32 := 0x01696b33.
Lemma F_86c80 : fetch_word Ubsan.M.loaded_segments (0x86c80 : word) = Some W_86c80.
Proof. vm_refl. Qed.
Lemma D_86c80 : decode_any W_86c80 = Some (Op ALU_OR 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c84 : bv 32 := 0x00088463.
Lemma F_86c84 : fetch_word Ubsan.M.loaded_segments (0x86c84 : word) = Some W_86c84.
Proof. vm_refl. Qed.
Lemma D_86c84 : decode_any W_86c84 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c88 : bv 32 := 0x86dfb06f.
Lemma F_86c88 : fetch_word Ubsan.M.loaded_segments (0x86c88 : word) = Some W_86c88.
Proof. vm_refl. Qed.
Lemma D_86c88 : decode_any W_86c88 = Some (Jal 0 2078828, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c8c : bv 32 := 0x00051463.
Lemma F_86c8c : fetch_word Ubsan.M.loaded_segments (0x86c8c : word) = Some W_86c8c.
Proof. vm_refl. Qed.
Lemma D_86c8c : decode_any W_86c8c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c90 : bv 32 := 0x865fb06f.
Lemma F_86c90 : fetch_word Ubsan.M.loaded_segments (0x86c90 : word) = Some W_86c90.
Proof. vm_refl. Qed.
Lemma D_86c90 : decode_any W_86c90 = Some (Jal 0 2078820, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c94 : bv 32 := 0x00052903.
Lemma F_86c94 : fetch_word Ubsan.M.loaded_segments (0x86c94 : word) = Some W_86c94.
Proof. vm_refl. Qed.
Lemma D_86c94 : decode_any W_86c94 = Some (Load SZ4 true 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c98 : bv 32 := 0x00d97bb3.
Lemma F_86c98 : fetch_word Ubsan.M.loaded_segments (0x86c98 : word) = Some W_86c98.
Proof. vm_refl. Qed.
Lemma D_86c98 : decode_any W_86c98 = Some (Op ALU_AND 23 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c9c : bv 32 := 0x01694933.
Lemma F_86c9c : fetch_word Ubsan.M.loaded_segments (0x86c9c : word) = Some W_86c9c.
Proof. vm_refl. Qed.
Lemma D_86c9c : decode_any W_86c9c = Some (Op ALU_XOR 18 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ca0 : bv 32 := 0x06013b03.
Lemma F_86ca0 : fetch_word Ubsan.M.loaded_segments (0x86ca0 : word) = Some W_86ca0.
Proof. vm_refl. Qed.
Lemma D_86ca0 : decode_any W_86ca0 = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ca4 : bv 32 := 0x01697933.
Lemma F_86ca4 : fetch_word Ubsan.M.loaded_segments (0x86ca4 : word) = Some W_86ca4.
Proof. vm_refl. Qed.
Lemma D_86ca4 : decode_any W_86ca4 = Some (Op ALU_AND 18 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ca8 : bv 32 := 0x01796933.
Lemma F_86ca8 : fetch_word Ubsan.M.loaded_segments (0x86ca8 : word) = Some W_86ca8.
Proof. vm_refl. Qed.
Lemma D_86ca8 : decode_any W_86ca8 = Some (Op ALU_OR 18 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cac : bv 32 := 0x01478b33.
Lemma F_86cac : fetch_word Ubsan.M.loaded_segments (0x86cac : word) = Some W_86cac.
Proof. vm_refl. Qed.
Lemma D_86cac : decode_any W_86cac = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cb0 : bv 32 := 0x01252023.
Lemma F_86cb0 : fetch_word Ubsan.M.loaded_segments (0x86cb0 : word) = Some W_86cb0.
Proof. vm_refl. Qed.
Lemma D_86cb0 : decode_any W_86cb0 = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cb4 : bv 32 := 0x000b1463.
Lemma F_86cb4 : fetch_word Ubsan.M.loaded_segments (0x86cb4 : word) = Some W_86cb4.
Proof. vm_refl. Qed.
Lemma D_86cb4 : decode_any W_86cb4 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cb8 : bv 32 := 0x83dfb06f.
Lemma F_86cb8 : fetch_word Ubsan.M.loaded_segments (0x86cb8 : word) = Some W_86cb8.
Proof. vm_refl. Qed.
Lemma D_86cb8 : decode_any W_86cb8 = Some (Jal 0 2078780, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cbc : bv 32 := 0x014b3933.
Lemma F_86cbc : fetch_word Ubsan.M.loaded_segments (0x86cbc : word) = Some W_86cbc.
Proof. vm_refl. Qed.
Lemma D_86cbc : decode_any W_86cbc = Some (Op ALU_SLTU 18 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cc0 : bv 32 := 0x00e94933.
Lemma F_86cc0 : fetch_word Ubsan.M.loaded_segments (0x86cc0 : word) = Some W_86cc0.
Proof. vm_refl. Qed.
Lemma D_86cc0 : decode_any W_86cc0 = Some (Op ALU_XOR 18 18 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cc4 : bv 32 := 0x00194913.
Lemma F_86cc4 : fetch_word Ubsan.M.loaded_segments (0x86cc4 : word) = Some W_86cc4.
Proof. vm_refl. Qed.
Lemma D_86cc4 : decode_any W_86cc4 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cc8 : bv 32 := 0x00091463.
Lemma F_86cc8 : fetch_word Ubsan.M.loaded_segments (0x86cc8 : word) = Some W_86cc8.
Proof. vm_refl. Qed.
Lemma D_86cc8 : decode_any W_86cc8 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ccc : bv 32 := 0x829fb06f.
Lemma F_86ccc : fetch_word Ubsan.M.loaded_segments (0x86ccc : word) = Some W_86ccc.
Proof. vm_refl. Qed.
Lemma D_86ccc : decode_any W_86ccc = Some (Jal 0 2078760, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cd0 : bv 32 := 0x00be0a33.
Lemma F_86cd0 : fetch_word Ubsan.M.loaded_segments (0x86cd0 : word) = Some W_86cd0.
Proof. vm_refl. Qed.
Lemma D_86cd0 : decode_any W_86cd0 = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cd4 : bv 32 := 0x000a1463.
Lemma F_86cd4 : fetch_word Ubsan.M.loaded_segments (0x86cd4 : word) = Some W_86cd4.
Proof. vm_refl. Qed.
Lemma D_86cd4 : decode_any W_86cd4 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cd8 : bv 32 := 0x81dfb06f.
Lemma F_86cd8 : fetch_word Ubsan.M.loaded_segments (0x86cd8 : word) = Some W_86cd8.
Proof. vm_refl. Qed.
Lemma D_86cd8 : decode_any W_86cd8 = Some (Jal 0 2078748, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cdc : bv 32 := 0x015a3933.
Lemma F_86cdc : fetch_word Ubsan.M.loaded_segments (0x86cdc : word) = Some W_86cdc.
Proof. vm_refl. Qed.
Lemma D_86cdc : decode_any W_86cdc = Some (Op ALU_SLTU 18 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ce0 : bv 32 := 0x07813a03.
Lemma F_86ce0 : fetch_word Ubsan.M.loaded_segments (0x86ce0 : word) = Some W_86ce0.
Proof. vm_refl. Qed.
Lemma D_86ce0 : decode_any W_86ce0 = Some (Load SZ8 true 20 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ce4 : bv 32 := 0x01494933.
Lemma F_86ce4 : fetch_word Ubsan.M.loaded_segments (0x86ce4 : word) = Some W_86ce4.
Proof. vm_refl. Qed.
Lemma D_86ce4 : decode_any W_86ce4 = Some (Op ALU_XOR 18 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ce8 : bv 32 := 0x00194913.
Lemma F_86ce8 : fetch_word Ubsan.M.loaded_segments (0x86ce8 : word) = Some W_86ce8.
Proof. vm_refl. Qed.
Lemma D_86ce8 : decode_any W_86ce8 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cec : bv 32 := 0x00091463.
Lemma F_86cec : fetch_word Ubsan.M.loaded_segments (0x86cec : word) = Some W_86cec.
Proof. vm_refl. Qed.
Lemma D_86cec : decode_any W_86cec = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cf0 : bv 32 := 0x805fb06f.
Lemma F_86cf0 : fetch_word Ubsan.M.loaded_segments (0x86cf0 : word) = Some W_86cf0.
Proof. vm_refl. Qed.
Lemma D_86cf0 : decode_any W_86cf0 = Some (Jal 0 2078724, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cf4 : bv 32 := 0x0014849b.
Lemma F_86cf4 : fetch_word Ubsan.M.loaded_segments (0x86cf4 : word) = Some W_86cf4.
Proof. vm_refl. Qed.
Lemma D_86cf4 : decode_any W_86cf4 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cf8 : bv 32 := 0x006585b3.
Lemma F_86cf8 : fetch_word Ubsan.M.loaded_segments (0x86cf8 : word) = Some W_86cf8.
Proof. vm_refl. Qed.
Lemma D_86cf8 : decode_any W_86cf8 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86cfc : bv 32 := 0x00f50533.
Lemma F_86cfc : fetch_word Ubsan.M.loaded_segments (0x86cfc : word) = Some W_86cfc.
Proof. vm_refl. Qed.
Lemma D_86cfc : decode_any W_86cfc = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d00 : bv 32 := 0x000b0a13.
Lemma F_86d00 : fetch_word Ubsan.M.loaded_segments (0x86d00 : word) = Some W_86d00.
Proof. vm_refl. Qed.
Lemma D_86d00 : decode_any W_86d00 = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d04 : bv 32 := 0xf2049ce3.
Lemma F_86d04 : fetch_word Ubsan.M.loaded_segments (0x86d04 : word) = Some W_86d04.
Proof. vm_refl. Qed.
Lemma D_86d04 : decode_any W_86d04 = Some (Branch BC_NE 9 0 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d08 : bv 32 := 0x0b10006f.
Lemma F_86d08 : fetch_word Ubsan.M.loaded_segments (0x86d08 : word) = Some W_86d08.
Proof. vm_refl. Qed.
Lemma D_86d08 : decode_any W_86d08 = Some (Jal 0 2224, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d0c : bv 32 := 0x16008c63.
Lemma F_86d0c : fetch_word Ubsan.M.loaded_segments (0x86d0c : word) = Some W_86d0c.
Proof. vm_refl. Qed.
Lemma D_86d0c : decode_any W_86d0c = Some (Branch BC_EQ 1 0 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d10 : bv 32 := 0x00000593.
Lemma F_86d10 : fetch_word Ubsan.M.loaded_segments (0x86d10 : word) = Some W_86d10.
Proof. vm_refl. Qed.
Lemma D_86d10 : decode_any W_86d10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d14 : bv 32 := 0xffffca93.
Lemma F_86d14 : fetch_word Ubsan.M.loaded_segments (0x86d14 : word) = Some W_86d14.
Proof. vm_refl. Qed.
Lemma D_86d14 : decode_any W_86d14 = Some (OpImm ALU_XOR 21 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d18 : bv 32 := 0xfffdc293.
Lemma F_86d18 : fetch_word Ubsan.M.loaded_segments (0x86d18 : word) = Some W_86d18.
Proof. vm_refl. Qed.
Lemma D_86d18 : decode_any W_86d18 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d1c : bv 32 := 0x00271393.
Lemma F_86d1c : fetch_word Ubsan.M.loaded_segments (0x86d1c : word) = Some W_86d1c.
Proof. vm_refl. Qed.
Lemma D_86d1c : decode_any W_86d1c = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d20 : bv 32 := 0x05813683.
Lemma F_86d20 : fetch_word Ubsan.M.loaded_segments (0x86d20 : word) = Some W_86d20.
Proof. vm_refl. Qed.
Lemma D_86d20 : decode_any W_86d20 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d24 : bv 32 := 0x00269693.
Lemma F_86d24 : fetch_word Ubsan.M.loaded_segments (0x86d24 : word) = Some W_86d24.
Proof. vm_refl. Qed.
Lemma D_86d24 : decode_any W_86d24 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d28 : bv 32 := 0x003cfb93.
Lemma F_86d28 : fetch_word Ubsan.M.loaded_segments (0x86d28 : word) = Some W_86d28.
Proof. vm_refl. Qed.
Lemma D_86d28 : decode_any W_86d28 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d2c : bv 32 := 0x0037f613.
Lemma F_86d2c : fetch_word Ubsan.M.loaded_segments (0x86d2c : word) = Some W_86d2c.
Proof. vm_refl. Qed.
Lemma D_86d2c : decode_any W_86d2c = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d30 : bv 32 := 0x05013883.
Lemma F_86d30 : fetch_word Ubsan.M.loaded_segments (0x86d30 : word) = Some W_86d30.
Proof. vm_refl. Qed.
Lemma D_86d30 : decode_any W_86d30 = Some (Load SZ8 true 17 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d34 : bv 32 := 0x02813803.
Lemma F_86d34 : fetch_word Ubsan.M.loaded_segments (0x86d34 : word) = Some W_86d34.
Proof. vm_refl. Qed.
Lemma D_86d34 : decode_any W_86d34 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d38 : bv 32 := 0x4118083b.
Lemma F_86d38 : fetch_word Ubsan.M.loaded_segments (0x86d38 : word) = Some W_86d38.
Proof. vm_refl. Qed.
Lemma D_86d38 : decode_any W_86d38 = Some (Op32 ALU_SUB 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d3c : bv 32 := 0x03813e03.
Lemma F_86d3c : fetch_word Ubsan.M.loaded_segments (0x86d3c : word) = Some W_86d3c.
Proof. vm_refl. Qed.
Lemma D_86d3c : decode_any W_86d3c = Some (Load SZ8 true 28 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d40 : bv 32 := 0x03013483.
Lemma F_86d40 : fetch_word Ubsan.M.loaded_segments (0x86d40 : word) = Some W_86d40.
Proof. vm_refl. Qed.
Lemma D_86d40 : decode_any W_86d40 = Some (Load SZ8 true 9 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d44 : bv 32 := 0x01c48e33.
Lemma F_86d44 : fetch_word Ubsan.M.loaded_segments (0x86d44 : word) = Some W_86d44.
Proof. vm_refl. Qed.
Lemma D_86d44 : decode_any W_86d44 = Some (Op ALU_ADD 28 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d48 : bv 32 := 0x04813a03.
Lemma F_86d48 : fetch_word Ubsan.M.loaded_segments (0x86d48 : word) = Some W_86d48.
Proof. vm_refl. Qed.
Lemma D_86d48 : decode_any W_86d48 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d4c : bv 32 := 0x43fa5493.
Lemma F_86d4c : fetch_word Ubsan.M.loaded_segments (0x86d4c : word) = Some W_86d4c.
Proof. vm_refl. Qed.
Lemma D_86d4c : decode_any W_86d4c = Some (ShiftImm ALU_SRA 9 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d50 : bv 32 := 0x01013983.
Lemma F_86d50 : fetch_word Ubsan.M.loaded_segments (0x86d50 : word) = Some W_86d50.
Proof. vm_refl. Qed.
Lemma D_86d50 : decode_any W_86d50 = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d54 : bv 32 := 0x0019f993.
Lemma F_86d54 : fetch_word Ubsan.M.loaded_segments (0x86d54 : word) = Some W_86d54.
Proof. vm_refl. Qed.
Lemma D_86d54 : decode_any W_86d54 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d58 : bv 32 := 0x001d7c13.
Lemma F_86d58 : fetch_word Ubsan.M.loaded_segments (0x86d58 : word) = Some W_86d58.
Proof. vm_refl. Qed.
Lemma D_86d58 : decode_any W_86d58 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d5c : bv 32 := 0x01f00093.
Lemma F_86d5c : fetch_word Ubsan.M.loaded_segments (0x86d5c : word) = Some W_86d5c.
Proof. vm_refl. Qed.
Lemma D_86d5c : decode_any W_86d5c = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d60 : bv 32 := 0x0144f4b3.
Lemma F_86d60 : fetch_word Ubsan.M.loaded_segments (0x86d60 : word) = Some W_86d60.
Proof. vm_refl. Qed.
Lemma D_86d60 : decode_any W_86d60 = Some (Op ALU_AND 9 9 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d64 : bv 32 := 0x411e0e3b.
Lemma F_86d64 : fetch_word Ubsan.M.loaded_segments (0x86d64 : word) = Some W_86d64.
Proof. vm_refl. Qed.
Lemma D_86d64 : decode_any W_86d64 = Some (Op32 ALU_SUB 28 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d68 : bv 32 := 0x000a8893.
Lemma F_86d68 : fetch_word Ubsan.M.loaded_segments (0x86d68 : word) = Some W_86d68.
Proof. vm_refl. Qed.
Lemma D_86d68 : decode_any W_86d68 = Some (OpImm ALU_ADD 17 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d6c : bv 32 := 0x00d78a33.
Lemma F_86d6c : fetch_word Ubsan.M.loaded_segments (0x86d6c : word) = Some W_86d6c.
Proof. vm_refl. Qed.
Lemma D_86d6c : decode_any W_86d6c = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d70 : bv 32 := 0x00163b13.
Lemma F_86d70 : fetch_word Ubsan.M.loaded_segments (0x86d70 : word) = Some W_86d70.
Proof. vm_refl. Qed.
Lemma D_86d70 : decode_any W_86d70 = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d74 : bv 32 := 0x04013603.
Lemma F_86d74 : fetch_word Ubsan.M.loaded_segments (0x86d74 : word) = Some W_86d74.
Proof. vm_refl. Qed.
Lemma D_86d74 : decode_any W_86d74 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d78 : bv 32 := 0x40ce063b.
Lemma F_86d78 : fetch_word Ubsan.M.loaded_segments (0x86d78 : word) = Some W_86d78.
Proof. vm_refl. Qed.
Lemma D_86d78 : decode_any W_86d78 = Some (Op32 ALU_SUB 12 28 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d7c : bv 32 := 0x0096063b.
Lemma F_86d7c : fetch_word Ubsan.M.loaded_segments (0x86d7c : word) = Some W_86d7c.
Proof. vm_refl. Qed.
Lemma D_86d7c : decode_any W_86d7c = Some (Op32 ALU_ADD 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d80 : bv 32 := 0x43f65e13.
Lemma F_86d80 : fetch_word Ubsan.M.loaded_segments (0x86d80 : word) = Some W_86d80.
Proof. vm_refl. Qed.
Lemma D_86d80 : decode_any W_86d80 = Some (ShiftImm ALU_SRA 28 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d84 : bv 32 := 0x00ce7633.
Lemma F_86d84 : fetch_word Ubsan.M.loaded_segments (0x86d84 : word) = Some W_86d84.
Proof. vm_refl. Qed.
Lemma D_86d84 : decode_any W_86d84 = Some (Op ALU_AND 12 28 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d88 : bv 32 := 0x40c80e3b.
Lemma F_86d88 : fetch_word Ubsan.M.loaded_segments (0x86d88 : word) = Some W_86d88.
Proof. vm_refl. Qed.
Lemma D_86d88 : decode_any W_86d88 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d8c : bv 32 := 0x00072493.
Lemma F_86d8c : fetch_word Ubsan.M.loaded_segments (0x86d8c : word) = Some W_86d8c.
Proof. vm_refl. Qed.
Lemma D_86d8c : decode_any W_86d8c = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d90 : bv 32 := 0x000c8813.
Lemma F_86d90 : fetch_word Ubsan.M.loaded_segments (0x86d90 : word) = Some W_86d90.
Proof. vm_refl. Qed.
Lemma D_86d90 : decode_any W_86d90 = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d94 : bv 32 := 0x00b78d33.
Lemma F_86d94 : fetch_word Ubsan.M.loaded_segments (0x86d94 : word) = Some W_86d94.
Proof. vm_refl. Qed.
Lemma D_86d94 : decode_any W_86d94 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d98 : bv 32 := 0x01a03633.
Lemma F_86d98 : fetch_word Ubsan.M.loaded_segments (0x86d98 : word) = Some W_86d98.
Proof. vm_refl. Qed.
Lemma D_86d98 : decode_any W_86d98 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86d9c : bv 32 := 0x00cb7633.
Lemma F_86d9c : fetch_word Ubsan.M.loaded_segments (0x86d9c : word) = Some W_86d9c.
Proof. vm_refl. Qed.
Lemma D_86d9c : decode_any W_86d9c = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86da0 : bv 32 := 0x04098863.
Lemma F_86da0 : fetch_word Ubsan.M.loaded_segments (0x86da0 : word) = Some W_86da0.
Proof. vm_refl. Qed.
Lemma D_86da0 : decode_any W_86da0 = Some (Branch BC_EQ 19 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_86da4 : bv 32 := 0x00061463.
Lemma F_86da4 : fetch_word Ubsan.M.loaded_segments (0x86da4 : word) = Some W_86da4.
Proof. vm_refl. Qed.
Lemma D_86da4 : decode_any W_86da4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86da8 : bv 32 := 0xf4cfb06f.
Lemma F_86da8 : fetch_word Ubsan.M.loaded_segments (0x86da8 : word) = Some W_86da8.
Proof. vm_refl. Qed.
Lemma D_86da8 : decode_any W_86da8 = Some (Jal 0 2078540, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dac : bv 32 := 0x02000613.
Lemma F_86dac : fetch_word Ubsan.M.loaded_segments (0x86dac : word) = Some W_86dac.
Proof. vm_refl. Qed.
Lemma D_86dac : decode_any W_86dac = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86db0 : bv 32 := 0x00cf1463.
Lemma F_86db0 : fetch_word Ubsan.M.loaded_segments (0x86db0 : word) = Some W_86db0.
Proof. vm_refl. Qed.
Lemma D_86db0 : decode_any W_86db0 = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86db4 : bv 32 := 0xf40fb06f.
Lemma F_86db4 : fetch_word Ubsan.M.loaded_segments (0x86db4 : word) = Some W_86db4.
Proof. vm_refl. Qed.
Lemma D_86db4 : decode_any W_86db4 = Some (Jal 0 2078528, 4%Z).
Proof. vm_refl. Qed.

Definition W_86db8 : bv 32 := 0x000d2603.
Lemma F_86db8 : fetch_word Ubsan.M.loaded_segments (0x86db8 : word) = Some W_86db8.
Proof. vm_refl. Qed.
Lemma D_86db8 : decode_any W_86db8 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dbc : bv 32 := 0x01d61abb.
Lemma F_86dbc : fetch_word Ubsan.M.loaded_segments (0x86dbc : word) = Some W_86dbc.
Proof. vm_refl. Qed.
Lemma D_86dbc : decode_any W_86dbc = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dc0 : bv 32 := 0x040c1463.
Lemma F_86dc0 : fetch_word Ubsan.M.loaded_segments (0x86dc0 : word) = Some W_86dc0.
Proof. vm_refl. Qed.
Lemma D_86dc0 : decode_any W_86dc0 = Some (Branch BC_NE 24 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dc4 : bv 32 := 0xffb00613.
Lemma F_86dc4 : fetch_word Ubsan.M.loaded_segments (0x86dc4 : word) = Some W_86dc4.
Proof. vm_refl. Qed.
Lemma D_86dc4 : decode_any W_86dc4 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dc8 : bv 32 := 0x01a67463.
Lemma F_86dc8 : fetch_word Ubsan.M.loaded_segments (0x86dc8 : word) = Some W_86dc8.
Proof. vm_refl. Qed.
Lemma D_86dc8 : decode_any W_86dc8 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dcc : bv 32 := 0xf28fb06f.
Lemma F_86dcc : fetch_word Ubsan.M.loaded_segments (0x86dcc : word) = Some W_86dcc.
Proof. vm_refl. Qed.
Lemma D_86dcc : decode_any W_86dcc = Some (Jal 0 2078504, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dd0 : bv 32 := 0x0080f463.
Lemma F_86dd0 : fetch_word Ubsan.M.loaded_segments (0x86dd0 : word) = Some W_86dd0.
Proof. vm_refl. Qed.
Lemma D_86dd0 : decode_any W_86dd0 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dd4 : bv 32 := 0xf20fb06f.
Lemma F_86dd4 : fetch_word Ubsan.M.loaded_segments (0x86dd4 : word) = Some W_86dd4.
Proof. vm_refl. Qed.
Lemma D_86dd4 : decode_any W_86dd4 = Some (Jal 0 2078496, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dd8 : bv 32 := 0x004d2603.
Lemma F_86dd8 : fetch_word Ubsan.M.loaded_segments (0x86dd8 : word) = Some W_86dd8.
Proof. vm_refl. Qed.
Lemma D_86dd8 : decode_any W_86dd8 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ddc : bv 32 := 0x011afab3.
Lemma F_86ddc : fetch_word Ubsan.M.loaded_segments (0x86ddc : word) = Some W_86ddc.
Proof. vm_refl. Qed.
Lemma D_86ddc : decode_any W_86ddc = Some (Op ALU_AND 21 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_86de0 : bv 32 := 0x0086563b.
Lemma F_86de0 : fetch_word Ubsan.M.loaded_segments (0x86de0 : word) = Some W_86de0.
Proof. vm_refl. Qed.
Lemma D_86de0 : decode_any W_86de0 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86de4 : bv 32 := 0x01f67633.
Lemma F_86de4 : fetch_word Ubsan.M.loaded_segments (0x86de4 : word) = Some W_86de4.
Proof. vm_refl. Qed.
Lemma D_86de4 : decode_any W_86de4 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86de8 : bv 32 := 0x01566ab3.
Lemma F_86de8 : fetch_word Ubsan.M.loaded_segments (0x86de8 : word) = Some W_86de8.
Proof. vm_refl. Qed.
Lemma D_86de8 : decode_any W_86de8 = Some (Op ALU_OR 21 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dec : bv 32 := 0x01c0006f.
Lemma F_86dec : fetch_word Ubsan.M.loaded_segments (0x86dec : word) = Some W_86dec.
Proof. vm_refl. Qed.
Lemma D_86dec : decode_any W_86dec = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86df0 : bv 32 := 0x00061463.
Lemma F_86df0 : fetch_word Ubsan.M.loaded_segments (0x86df0 : word) = Some W_86df0.
Proof. vm_refl. Qed.
Lemma D_86df0 : decode_any W_86df0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86df4 : bv 32 := 0xf00fb06f.
Lemma F_86df4 : fetch_word Ubsan.M.loaded_segments (0x86df4 : word) = Some W_86df4.
Proof. vm_refl. Qed.
Lemma D_86df4 : decode_any W_86df4 = Some (Jal 0 2078464, 4%Z).
Proof. vm_refl. Qed.

Definition W_86df8 : bv 32 := 0x0080f463.
Lemma F_86df8 : fetch_word Ubsan.M.loaded_segments (0x86df8 : word) = Some W_86df8.
Proof. vm_refl. Qed.
Lemma D_86df8 : decode_any W_86df8 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86dfc : bv 32 := 0xef8fb06f.
Lemma F_86dfc : fetch_word Ubsan.M.loaded_segments (0x86dfc : word) = Some W_86dfc.
Proof. vm_refl. Qed.
Lemma D_86dfc : decode_any W_86dfc = Some (Jal 0 2078456, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e00 : bv 32 := 0x000d2603.
Lemma F_86e00 : fetch_word Ubsan.M.loaded_segments (0x86e00 : word) = Some W_86e00.
Proof. vm_refl. Qed.
Lemma D_86e00 : decode_any W_86e00 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e04 : bv 32 := 0x00865abb.
Lemma F_86e04 : fetch_word Ubsan.M.loaded_segments (0x86e04 : word) = Some W_86e04.
Proof. vm_refl. Qed.
Lemma D_86e04 : decode_any W_86e04 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e08 : bv 32 := 0x000b8463.
Lemma F_86e08 : fetch_word Ubsan.M.loaded_segments (0x86e08 : word) = Some W_86e08.
Proof. vm_refl. Qed.
Lemma D_86e08 : decode_any W_86e08 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e0c : bv 32 := 0xee8fb06f.
Lemma F_86e0c : fetch_word Ubsan.M.loaded_segments (0x86e0c : word) = Some W_86e0c.
Proof. vm_refl. Qed.
Lemma D_86e0c : decode_any W_86e0c = Some (Jal 0 2078440, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e10 : bv 32 := 0x000c9463.
Lemma F_86e10 : fetch_word Ubsan.M.loaded_segments (0x86e10 : word) = Some W_86e10.
Proof. vm_refl. Qed.
Lemma D_86e10 : decode_any W_86e10 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e14 : bv 32 := 0xee0fb06f.
Lemma F_86e14 : fetch_word Ubsan.M.loaded_segments (0x86e14 : word) = Some W_86e14.
Proof. vm_refl. Qed.
Lemma D_86e14 : decode_any W_86e14 = Some (Jal 0 2078432, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e18 : bv 32 := 0x000ca603.
Lemma F_86e18 : fetch_word Ubsan.M.loaded_segments (0x86e18 : word) = Some W_86e18.
Proof. vm_refl. Qed.
Lemma D_86e18 : decode_any W_86e18 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e1c : bv 32 := 0x01bafab3.
Lemma F_86e1c : fetch_word Ubsan.M.loaded_segments (0x86e1c : word) = Some W_86e1c.
Proof. vm_refl. Qed.
Lemma D_86e1c : decode_any W_86e1c = Some (Op ALU_AND 21 21 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e20 : bv 32 := 0x00567633.
Lemma F_86e20 : fetch_word Ubsan.M.loaded_segments (0x86e20 : word) = Some W_86e20.
Proof. vm_refl. Qed.
Lemma D_86e20 : decode_any W_86e20 = Some (Op ALU_AND 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e24 : bv 32 := 0x01566633.
Lemma F_86e24 : fetch_word Ubsan.M.loaded_segments (0x86e24 : word) = Some W_86e24.
Proof. vm_refl. Qed.
Lemma D_86e24 : decode_any W_86e24 = Some (Op ALU_OR 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e28 : bv 32 := 0x01038ab3.
Lemma F_86e28 : fetch_word Ubsan.M.loaded_segments (0x86e28 : word) = Some W_86e28.
Proof. vm_refl. Qed.
Lemma D_86e28 : decode_any W_86e28 = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e2c : bv 32 := 0x00cca023.
Lemma F_86e2c : fetch_word Ubsan.M.loaded_segments (0x86e2c : word) = Some W_86e2c.
Proof. vm_refl. Qed.
Lemma D_86e2c : decode_any W_86e2c = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e30 : bv 32 := 0x000a9463.
Lemma F_86e30 : fetch_word Ubsan.M.loaded_segments (0x86e30 : word) = Some W_86e30.
Proof. vm_refl. Qed.
Lemma D_86e30 : decode_any W_86e30 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e34 : bv 32 := 0xec0fb06f.
Lemma F_86e34 : fetch_word Ubsan.M.loaded_segments (0x86e34 : word) = Some W_86e34.
Proof. vm_refl. Qed.
Lemma D_86e34 : decode_any W_86e34 = Some (Jal 0 2078400, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e38 : bv 32 := 0x010ab633.
Lemma F_86e38 : fetch_word Ubsan.M.loaded_segments (0x86e38 : word) = Some W_86e38.
Proof. vm_refl. Qed.
Lemma D_86e38 : decode_any W_86e38 = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e3c : bv 32 := 0x00964633.
Lemma F_86e3c : fetch_word Ubsan.M.loaded_segments (0x86e3c : word) = Some W_86e3c.
Proof. vm_refl. Qed.
Lemma D_86e3c : decode_any W_86e3c = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e40 : bv 32 := 0x00164613.
Lemma F_86e40 : fetch_word Ubsan.M.loaded_segments (0x86e40 : word) = Some W_86e40.
Proof. vm_refl. Qed.
Lemma D_86e40 : decode_any W_86e40 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e44 : bv 32 := 0x00061463.
Lemma F_86e44 : fetch_word Ubsan.M.loaded_segments (0x86e44 : word) = Some W_86e44.
Proof. vm_refl. Qed.
Lemma D_86e44 : decode_any W_86e44 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e48 : bv 32 := 0xeacfb06f.
Lemma F_86e48 : fetch_word Ubsan.M.loaded_segments (0x86e48 : word) = Some W_86e48.
Proof. vm_refl. Qed.
Lemma D_86e48 : decode_any W_86e48 = Some (Jal 0 2078380, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e4c : bv 32 := 0x00ba0633.
Lemma F_86e4c : fetch_word Ubsan.M.loaded_segments (0x86e4c : word) = Some W_86e4c.
Proof. vm_refl. Qed.
Lemma D_86e4c : decode_any W_86e4c = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e50 : bv 32 := 0x00061463.
Lemma F_86e50 : fetch_word Ubsan.M.loaded_segments (0x86e50 : word) = Some W_86e50.
Proof. vm_refl. Qed.
Lemma D_86e50 : decode_any W_86e50 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e54 : bv 32 := 0xea0fb06f.
Lemma F_86e54 : fetch_word Ubsan.M.loaded_segments (0x86e54 : word) = Some W_86e54.
Proof. vm_refl. Qed.
Lemma D_86e54 : decode_any W_86e54 = Some (Jal 0 2078368, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e58 : bv 32 := 0x01a63633.
Lemma F_86e58 : fetch_word Ubsan.M.loaded_segments (0x86e58 : word) = Some W_86e58.
Proof. vm_refl. Qed.
Lemma D_86e58 : decode_any W_86e58 = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e5c : bv 32 := 0x07813803.
Lemma F_86e5c : fetch_word Ubsan.M.loaded_segments (0x86e5c : word) = Some W_86e5c.
Proof. vm_refl. Qed.
Lemma D_86e5c : decode_any W_86e5c = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e60 : bv 32 := 0x01064633.
Lemma F_86e60 : fetch_word Ubsan.M.loaded_segments (0x86e60 : word) = Some W_86e60.
Proof. vm_refl. Qed.
Lemma D_86e60 : decode_any W_86e60 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e64 : bv 32 := 0x00164613.
Lemma F_86e64 : fetch_word Ubsan.M.loaded_segments (0x86e64 : word) = Some W_86e64.
Proof. vm_refl. Qed.
Lemma D_86e64 : decode_any W_86e64 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e68 : bv 32 := 0x00061463.
Lemma F_86e68 : fetch_word Ubsan.M.loaded_segments (0x86e68 : word) = Some W_86e68.
Proof. vm_refl. Qed.
Lemma D_86e68 : decode_any W_86e68 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e6c : bv 32 := 0xe88fb06f.
Lemma F_86e6c : fetch_word Ubsan.M.loaded_segments (0x86e6c : word) = Some W_86e6c.
Proof. vm_refl. Qed.
Lemma D_86e6c : decode_any W_86e6c = Some (Jal 0 2078344, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e70 : bv 32 := 0x001e0e1b.
Lemma F_86e70 : fetch_word Ubsan.M.loaded_segments (0x86e70 : word) = Some W_86e70.
Proof. vm_refl. Qed.
Lemma D_86e70 : decode_any W_86e70 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e74 : bv 32 := 0x00d585b3.
Lemma F_86e74 : fetch_word Ubsan.M.loaded_segments (0x86e74 : word) = Some W_86e74.
Proof. vm_refl. Qed.
Lemma D_86e74 : decode_any W_86e74 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e78 : bv 32 := 0x007c8cb3.
Lemma F_86e78 : fetch_word Ubsan.M.loaded_segments (0x86e78 : word) = Some W_86e78.
Proof. vm_refl. Qed.
Lemma D_86e78 : decode_any W_86e78 = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e7c : bv 32 := 0x000a8813.
Lemma F_86e7c : fetch_word Ubsan.M.loaded_segments (0x86e7c : word) = Some W_86e7c.
Proof. vm_refl. Qed.
Lemma D_86e7c : decode_any W_86e7c = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e80 : bv 32 := 0xf00e1ae3.
Lemma F_86e80 : fetch_word Ubsan.M.loaded_segments (0x86e80 : word) = Some W_86e80.
Proof. vm_refl. Qed.
Lemma D_86e80 : decode_any W_86e80 = Some (Branch BC_NE 28 0 7956, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e84 : bv 32 := 0x02013583.
Lemma F_86e84 : fetch_word Ubsan.M.loaded_segments (0x86e84 : word) = Some W_86e84.
Proof. vm_refl. Qed.
Lemma D_86e84 : decode_any W_86e84 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e88 : bv 32 := 0x16059063.
Lemma F_86e88 : fetch_word Ubsan.M.loaded_segments (0x86e88 : word) = Some W_86e88.
Proof. vm_refl. Qed.
Lemma D_86e88 : decode_any W_86e88 = Some (Branch BC_NE 11 0 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e8c : bv 32 := 0xffffc693.
Lemma F_86e8c : fetch_word Ubsan.M.loaded_segments (0x86e8c : word) = Some W_86e8c.
Proof. vm_refl. Qed.
Lemma D_86e8c : decode_any W_86e8c = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e90 : bv 32 := 0x00271293.
Lemma F_86e90 : fetch_word Ubsan.M.loaded_segments (0x86e90 : word) = Some W_86e90.
Proof. vm_refl. Qed.
Lemma D_86e90 : decode_any W_86e90 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e94 : bv 32 := 0x05813383.
Lemma F_86e94 : fetch_word Ubsan.M.loaded_segments (0x86e94 : word) = Some W_86e94.
Proof. vm_refl. Qed.
Lemma D_86e94 : decode_any W_86e94 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e98 : bv 32 := 0x00239393.
Lemma F_86e98 : fetch_word Ubsan.M.loaded_segments (0x86e98 : word) = Some W_86e98.
Proof. vm_refl. Qed.
Lemma D_86e98 : decode_any W_86e98 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86e9c : bv 32 := 0x00337613.
Lemma F_86e9c : fetch_word Ubsan.M.loaded_segments (0x86e9c : word) = Some W_86e9c.
Proof. vm_refl. Qed.
Lemma D_86e9c : decode_any W_86e9c = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ea0 : bv 32 := 0x00397793.
Lemma F_86ea0 : fetch_word Ubsan.M.loaded_segments (0x86ea0 : word) = Some W_86ea0.
Proof. vm_refl. Qed.
Lemma D_86ea0 : decode_any W_86ea0 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ea4 : bv 32 := 0x07013a03.
Lemma F_86ea4 : fetch_word Ubsan.M.loaded_segments (0x86ea4 : word) = Some W_86ea4.
Proof. vm_refl. Qed.
Lemma D_86ea4 : decode_any W_86ea4 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ea8 : bv 32 := 0x002a1a13.
Lemma F_86ea8 : fetch_word Ubsan.M.loaded_segments (0x86ea8 : word) = Some W_86ea8.
Proof. vm_refl. Qed.
Lemma D_86ea8 : decode_any W_86ea8 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_86eac : bv 32 := 0x00072993.
Lemma F_86eac : fetch_word Ubsan.M.loaded_segments (0x86eac : word) = Some W_86eac.
Proof. vm_refl. Qed.
Lemma D_86eac : decode_any W_86eac = Some (OpImm ALU_SLT 19 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86eb0 : bv 32 := 0x02000b93.
Lemma F_86eb0 : fetch_word Ubsan.M.loaded_segments (0x86eb0 : word) = Some W_86eb0.
Proof. vm_refl. Qed.
Lemma D_86eb0 : decode_any W_86eb0 = Some (OpImm ALU_ADD 23 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86eb4 : bv 32 := 0xffb00b13.
Lemma F_86eb4 : fetch_word Ubsan.M.loaded_segments (0x86eb4 : word) = Some W_86eb4.
Proof. vm_refl. Qed.
Lemma D_86eb4 : decode_any W_86eb4 = Some (OpImm ALU_ADD 22 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_86eb8 : bv 32 := 0x0017b893.
Lemma F_86eb8 : fetch_word Ubsan.M.loaded_segments (0x86eb8 : word) = Some W_86eb8.
Proof. vm_refl. Qed.
Lemma D_86eb8 : decode_any W_86eb8 = Some (OpImm ALU_SLTU 17 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ebc : bv 32 := 0x00163c93.
Lemma F_86ebc : fetch_word Ubsan.M.loaded_segments (0x86ebc : word) = Some W_86ebc.
Proof. vm_refl. Qed.
Lemma D_86ebc : decode_any W_86ebc = Some (OpImm ALU_SLTU 25 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ec0 : bv 32 := 0x01f00d13.
Lemma F_86ec0 : fetch_word Ubsan.M.loaded_segments (0x86ec0 : word) = Some W_86ec0.
Proof. vm_refl. Qed.
Lemma D_86ec0 : decode_any W_86ec0 = Some (OpImm ALU_ADD 26 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ec4 : bv 32 := 0x00030d93.
Lemma F_86ec4 : fetch_word Ubsan.M.loaded_segments (0x86ec4 : word) = Some W_86ec4.
Proof. vm_refl. Qed.
Lemma D_86ec4 : decode_any W_86ec4 = Some (OpImm ALU_ADD 27 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ec8 : bv 32 := 0x00090093.
Lemma F_86ec8 : fetch_word Ubsan.M.loaded_segments (0x86ec8 : word) = Some W_86ec8.
Proof. vm_refl. Qed.
Lemma D_86ec8 : decode_any W_86ec8 = Some (OpImm ALU_ADD 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ecc : bv 32 := 0x07013603.
Lemma F_86ecc : fetch_word Ubsan.M.loaded_segments (0x86ecc : word) = Some W_86ecc.
Proof. vm_refl. Qed.
Lemma D_86ecc : decode_any W_86ecc = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ed0 : bv 32 := 0x0a060463.
Lemma F_86ed0 : fetch_word Ubsan.M.loaded_segments (0x86ed0 : word) = Some W_86ed0.
Proof. vm_refl. Qed.
Lemma D_86ed0 : decode_any W_86ed0 = Some (Branch BC_EQ 12 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ed4 : bv 32 := 0x00000c13.
Lemma F_86ed4 : fetch_word Ubsan.M.loaded_segments (0x86ed4 : word) = Some W_86ed4.
Proof. vm_refl. Qed.
Lemma D_86ed4 : decode_any W_86ed4 = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ed8 : bv 32 := 0x00603833.
Lemma F_86ed8 : fetch_word Ubsan.M.loaded_segments (0x86ed8 : word) = Some W_86ed8.
Proof. vm_refl. Qed.
Lemma D_86ed8 : decode_any W_86ed8 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86edc : bv 32 := 0x01203e33.
Lemma F_86edc : fetch_word Ubsan.M.loaded_segments (0x86edc : word) = Some W_86edc.
Proof. vm_refl. Qed.
Lemma D_86edc : decode_any W_86edc = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ee0 : bv 32 := 0x010cf4b3.
Lemma F_86ee0 : fetch_word Ubsan.M.loaded_segments (0x86ee0 : word) = Some W_86ee0.
Proof. vm_refl. Qed.
Lemma D_86ee0 : decode_any W_86ee0 = Some (Op ALU_AND 9 25 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ee4 : bv 32 := 0x01c8fab3.
Lemma F_86ee4 : fetch_word Ubsan.M.loaded_segments (0x86ee4 : word) = Some W_86ee4.
Proof. vm_refl. Qed.
Lemma D_86ee4 : decode_any W_86ee4 = Some (Op ALU_AND 21 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ee8 : bv 32 := 0x018d8633.
Lemma F_86ee8 : fetch_word Ubsan.M.loaded_segments (0x86ee8 : word) = Some W_86ee8.
Proof. vm_refl. Qed.
Lemma D_86ee8 : decode_any W_86ee8 = Some (Op ALU_ADD 12 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86eec : bv 32 := 0x00667463.
Lemma F_86eec : fetch_word Ubsan.M.loaded_segments (0x86eec : word) = Some W_86eec.
Proof. vm_refl. Qed.
Lemma D_86eec : decode_any W_86eec = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ef0 : bv 32 := 0xe04fb06f.
Lemma F_86ef0 : fetch_word Ubsan.M.loaded_segments (0x86ef0 : word) = Some W_86ef0.
Proof. vm_refl. Qed.
Lemma D_86ef0 : decode_any W_86ef0 = Some (Jal 0 2078212, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ef4 : bv 32 := 0x00163613.
Lemma F_86ef4 : fetch_word Ubsan.M.loaded_segments (0x86ef4 : word) = Some W_86ef4.
Proof. vm_refl. Qed.
Lemma D_86ef4 : decode_any W_86ef4 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ef8 : bv 32 := 0x00c84633.
Lemma F_86ef8 : fetch_word Ubsan.M.loaded_segments (0x86ef8 : word) = Some W_86ef8.
Proof. vm_refl. Qed.
Lemma D_86ef8 : decode_any W_86ef8 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86efc : bv 32 := 0x00061463.
Lemma F_86efc : fetch_word Ubsan.M.loaded_segments (0x86efc : word) = Some W_86efc.
Proof. vm_refl. Qed.
Lemma D_86efc : decode_any W_86efc = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f00 : bv 32 := 0xdf4fb06f.
Lemma F_86f00 : fetch_word Ubsan.M.loaded_segments (0x86f00 : word) = Some W_86f00.
Proof. vm_refl. Qed.
Lemma D_86f00 : decode_any W_86f00 = Some (Jal 0 2078196, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f04 : bv 32 := 0x00049463.
Lemma F_86f04 : fetch_word Ubsan.M.loaded_segments (0x86f04 : word) = Some W_86f04.
Proof. vm_refl. Qed.
Lemma D_86f04 : decode_any W_86f04 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f08 : bv 32 := 0xdecfb06f.
Lemma F_86f08 : fetch_word Ubsan.M.loaded_segments (0x86f08 : word) = Some W_86f08.
Proof. vm_refl. Qed.
Lemma D_86f08 : decode_any W_86f08 = Some (Jal 0 2078188, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f0c : bv 32 := 0x017f1463.
Lemma F_86f0c : fetch_word Ubsan.M.loaded_segments (0x86f0c : word) = Some W_86f0c.
Proof. vm_refl. Qed.
Lemma D_86f0c : decode_any W_86f0c = Some (Branch BC_NE 30 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f10 : bv 32 := 0xde4fb06f.
Lemma F_86f10 : fetch_word Ubsan.M.loaded_segments (0x86f10 : word) = Some W_86f10.
Proof. vm_refl. Qed.
Lemma D_86f10 : decode_any W_86f10 = Some (Jal 0 2078180, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f14 : bv 32 := 0x01830633.
Lemma F_86f14 : fetch_word Ubsan.M.loaded_segments (0x86f14 : word) = Some W_86f14.
Proof. vm_refl. Qed.
Lemma D_86f14 : decode_any W_86f14 = Some (Op ALU_ADD 12 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f18 : bv 32 := 0x00cb7463.
Lemma F_86f18 : fetch_word Ubsan.M.loaded_segments (0x86f18 : word) = Some W_86f18.
Proof. vm_refl. Qed.
Lemma D_86f18 : decode_any W_86f18 = Some (Branch BC_GEU 22 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f1c : bv 32 := 0xdd8fb06f.
Lemma F_86f1c : fetch_word Ubsan.M.loaded_segments (0x86f1c : word) = Some W_86f1c.
Proof. vm_refl. Qed.
Lemma D_86f1c : decode_any W_86f1c = Some (Jal 0 2078168, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f20 : bv 32 := 0x008d7463.
Lemma F_86f20 : fetch_word Ubsan.M.loaded_segments (0x86f20 : word) = Some W_86f20.
Proof. vm_refl. Qed.
Lemma D_86f20 : decode_any W_86f20 = Some (Branch BC_GEU 26 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f24 : bv 32 := 0xdd0fb06f.
Lemma F_86f24 : fetch_word Ubsan.M.loaded_segments (0x86f24 : word) = Some W_86f24.
Proof. vm_refl. Qed.
Lemma D_86f24 : decode_any W_86f24 = Some (Jal 0 2078160, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f28 : bv 32 := 0x018087b3.
Lemma F_86f28 : fetch_word Ubsan.M.loaded_segments (0x86f28 : word) = Some W_86f28.
Proof. vm_refl. Qed.
Lemma D_86f28 : decode_any W_86f28 = Some (Op ALU_ADD 15 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f2c : bv 32 := 0x0127f463.
Lemma F_86f2c : fetch_word Ubsan.M.loaded_segments (0x86f2c : word) = Some W_86f2c.
Proof. vm_refl. Qed.
Lemma D_86f2c : decode_any W_86f2c = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f30 : bv 32 := 0xdc4fb06f.
Lemma F_86f30 : fetch_word Ubsan.M.loaded_segments (0x86f30 : word) = Some W_86f30.
Proof. vm_refl. Qed.
Lemma D_86f30 : decode_any W_86f30 = Some (Jal 0 2078148, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f34 : bv 32 := 0x0017b793.
Lemma F_86f34 : fetch_word Ubsan.M.loaded_segments (0x86f34 : word) = Some W_86f34.
Proof. vm_refl. Qed.
Lemma D_86f34 : decode_any W_86f34 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f38 : bv 32 := 0x00fe47b3.
Lemma F_86f38 : fetch_word Ubsan.M.loaded_segments (0x86f38 : word) = Some W_86f38.
Proof. vm_refl. Qed.
Lemma D_86f38 : decode_any W_86f38 = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f3c : bv 32 := 0x00079463.
Lemma F_86f3c : fetch_word Ubsan.M.loaded_segments (0x86f3c : word) = Some W_86f3c.
Proof. vm_refl. Qed.
Lemma D_86f3c : decode_any W_86f3c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f40 : bv 32 := 0xdb4fb06f.
Lemma F_86f40 : fetch_word Ubsan.M.loaded_segments (0x86f40 : word) = Some W_86f40.
Proof. vm_refl. Qed.
Lemma D_86f40 : decode_any W_86f40 = Some (Jal 0 2078132, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f44 : bv 32 := 0x000a9463.
Lemma F_86f44 : fetch_word Ubsan.M.loaded_segments (0x86f44 : word) = Some W_86f44.
Proof. vm_refl. Qed.
Lemma D_86f44 : decode_any W_86f44 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f48 : bv 32 := 0xdacfb06f.
Lemma F_86f48 : fetch_word Ubsan.M.loaded_segments (0x86f48 : word) = Some W_86f48.
Proof. vm_refl. Qed.
Lemma D_86f48 : decode_any W_86f48 = Some (Jal 0 2078124, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f4c : bv 32 := 0x00062783.
Lemma F_86f4c : fetch_word Ubsan.M.loaded_segments (0x86f4c : word) = Some W_86f4c.
Proof. vm_refl. Qed.
Lemma D_86f4c : decode_any W_86f4c = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f50 : bv 32 := 0x00462603.
Lemma F_86f50 : fetch_word Ubsan.M.loaded_segments (0x86f50 : word) = Some W_86f50.
Proof. vm_refl. Qed.
Lemma D_86f50 : decode_any W_86f50 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f54 : bv 32 := 0x01d797bb.
Lemma F_86f54 : fetch_word Ubsan.M.loaded_segments (0x86f54 : word) = Some W_86f54.
Proof. vm_refl. Qed.
Lemma D_86f54 : decode_any W_86f54 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f58 : bv 32 := 0x0086563b.
Lemma F_86f58 : fetch_word Ubsan.M.loaded_segments (0x86f58 : word) = Some W_86f58.
Proof. vm_refl. Qed.
Lemma D_86f58 : decode_any W_86f58 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f5c : bv 32 := 0x00d7f7b3.
Lemma F_86f5c : fetch_word Ubsan.M.loaded_segments (0x86f5c : word) = Some W_86f5c.
Proof. vm_refl. Qed.
Lemma D_86f5c : decode_any W_86f5c = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f60 : bv 32 := 0x01f67633.
Lemma F_86f60 : fetch_word Ubsan.M.loaded_segments (0x86f60 : word) = Some W_86f60.
Proof. vm_refl. Qed.
Lemma D_86f60 : decode_any W_86f60 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f64 : bv 32 := 0x00f66633.
Lemma F_86f64 : fetch_word Ubsan.M.loaded_segments (0x86f64 : word) = Some W_86f64.
Proof. vm_refl. Qed.
Lemma D_86f64 : decode_any W_86f64 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f68 : bv 32 := 0x018907b3.
Lemma F_86f68 : fetch_word Ubsan.M.loaded_segments (0x86f68 : word) = Some W_86f68.
Proof. vm_refl. Qed.
Lemma D_86f68 : decode_any W_86f68 = Some (Op ALU_ADD 15 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f6c : bv 32 := 0x004c0c13.
Lemma F_86f6c : fetch_word Ubsan.M.loaded_segments (0x86f6c : word) = Some W_86f6c.
Proof. vm_refl. Qed.
Lemma D_86f6c : decode_any W_86f6c = Some (OpImm ALU_ADD 24 24 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f70 : bv 32 := 0x00c7a023.
Lemma F_86f70 : fetch_word Ubsan.M.loaded_segments (0x86f70 : word) = Some W_86f70.
Proof. vm_refl. Qed.
Lemma D_86f70 : decode_any W_86f70 = Some (Store SZ4 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f74 : bv 32 := 0xf78a1ae3.
Lemma F_86f74 : fetch_word Ubsan.M.loaded_segments (0x86f74 : word) = Some W_86f74.
Proof. vm_refl. Qed.
Lemma D_86f74 : decode_any W_86f74 = Some (Branch BC_NE 20 24 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f78 : bv 32 := 0x00590633.
Lemma F_86f78 : fetch_word Ubsan.M.loaded_segments (0x86f78 : word) = Some W_86f78.
Proof. vm_refl. Qed.
Lemma D_86f78 : decode_any W_86f78 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f7c : bv 32 := 0x012037b3.
Lemma F_86f7c : fetch_word Ubsan.M.loaded_segments (0x86f7c : word) = Some W_86f7c.
Proof. vm_refl. Qed.
Lemma D_86f7c : decode_any W_86f7c = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f80 : bv 32 := 0x00163813.
Lemma F_86f80 : fetch_word Ubsan.M.loaded_segments (0x86f80 : word) = Some W_86f80.
Proof. vm_refl. Qed.
Lemma D_86f80 : decode_any W_86f80 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f84 : bv 32 := 0x01079463.
Lemma F_86f84 : fetch_word Ubsan.M.loaded_segments (0x86f84 : word) = Some W_86f84.
Proof. vm_refl. Qed.
Lemma D_86f84 : decode_any W_86f84 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f88 : bv 32 := 0xd6cfb06f.
Lemma F_86f88 : fetch_word Ubsan.M.loaded_segments (0x86f88 : word) = Some W_86f88.
Proof. vm_refl. Qed.
Lemma D_86f88 : decode_any W_86f88 = Some (Jal 0 2078060, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f8c : bv 32 := 0x01263633.
Lemma F_86f8c : fetch_word Ubsan.M.loaded_segments (0x86f8c : word) = Some W_86f8c.
Proof. vm_refl. Qed.
Lemma D_86f8c : decode_any W_86f8c = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f90 : bv 32 := 0x01364633.
Lemma F_86f90 : fetch_word Ubsan.M.loaded_segments (0x86f90 : word) = Some W_86f90.
Proof. vm_refl. Qed.
Lemma D_86f90 : decode_any W_86f90 = Some (Op ALU_XOR 12 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f94 : bv 32 := 0x00164613.
Lemma F_86f94 : fetch_word Ubsan.M.loaded_segments (0x86f94 : word) = Some W_86f94.
Proof. vm_refl. Qed.
Lemma D_86f94 : decode_any W_86f94 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f98 : bv 32 := 0x00061463.
Lemma F_86f98 : fetch_word Ubsan.M.loaded_segments (0x86f98 : word) = Some W_86f98.
Proof. vm_refl. Qed.
Lemma D_86f98 : decode_any W_86f98 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86f9c : bv 32 := 0xd58fb06f.
Lemma F_86f9c : fetch_word Ubsan.M.loaded_segments (0x86f9c : word) = Some W_86f9c.
Proof. vm_refl. Qed.
Lemma D_86f9c : decode_any W_86f9c = Some (Jal 0 2078040, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fa0 : bv 32 := 0x00638633.
Lemma F_86fa0 : fetch_word Ubsan.M.loaded_segments (0x86fa0 : word) = Some W_86fa0.
Proof. vm_refl. Qed.
Lemma D_86fa0 : decode_any W_86fa0 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fa4 : bv 32 := 0x006037b3.
Lemma F_86fa4 : fetch_word Ubsan.M.loaded_segments (0x86fa4 : word) = Some W_86fa4.
Proof. vm_refl. Qed.
Lemma D_86fa4 : decode_any W_86fa4 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fa8 : bv 32 := 0x00163813.
Lemma F_86fa8 : fetch_word Ubsan.M.loaded_segments (0x86fa8 : word) = Some W_86fa8.
Proof. vm_refl. Qed.
Lemma D_86fa8 : decode_any W_86fa8 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fac : bv 32 := 0x01079463.
Lemma F_86fac : fetch_word Ubsan.M.loaded_segments (0x86fac : word) = Some W_86fac.
Proof. vm_refl. Qed.
Lemma D_86fac : decode_any W_86fac = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fb0 : bv 32 := 0xd44fb06f.
Lemma F_86fb0 : fetch_word Ubsan.M.loaded_segments (0x86fb0 : word) = Some W_86fb0.
Proof. vm_refl. Qed.
Lemma D_86fb0 : decode_any W_86fb0 = Some (Jal 0 2078020, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fb4 : bv 32 := 0x006637b3.
Lemma F_86fb4 : fetch_word Ubsan.M.loaded_segments (0x86fb4 : word) = Some W_86fb4.
Proof. vm_refl. Qed.
Lemma D_86fb4 : decode_any W_86fb4 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fb8 : bv 32 := 0x07813803.
Lemma F_86fb8 : fetch_word Ubsan.M.loaded_segments (0x86fb8 : word) = Some W_86fb8.
Proof. vm_refl. Qed.
Lemma D_86fb8 : decode_any W_86fb8 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fbc : bv 32 := 0x0107c7b3.
Lemma F_86fbc : fetch_word Ubsan.M.loaded_segments (0x86fbc : word) = Some W_86fbc.
Proof. vm_refl. Qed.
Lemma D_86fbc : decode_any W_86fbc = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fc0 : bv 32 := 0x0017c793.
Lemma F_86fc0 : fetch_word Ubsan.M.loaded_segments (0x86fc0 : word) = Some W_86fc0.
Proof. vm_refl. Qed.
Lemma D_86fc0 : decode_any W_86fc0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fc4 : bv 32 := 0x00079463.
Lemma F_86fc4 : fetch_word Ubsan.M.loaded_segments (0x86fc4 : word) = Some W_86fc4.
Proof. vm_refl. Qed.
Lemma D_86fc4 : decode_any W_86fc4 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fc8 : bv 32 := 0xd2cfb06f.
Lemma F_86fc8 : fetch_word Ubsan.M.loaded_segments (0x86fc8 : word) = Some W_86fc8.
Proof. vm_refl. Qed.
Lemma D_86fc8 : decode_any W_86fc8 = Some (Jal 0 2077996, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fcc : bv 32 := 0x00590933.
Lemma F_86fcc : fetch_word Ubsan.M.loaded_segments (0x86fcc : word) = Some W_86fcc.
Proof. vm_refl. Qed.
Lemma D_86fcc : decode_any W_86fcc = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fd0 : bv 32 := 0x0015859b.
Lemma F_86fd0 : fetch_word Ubsan.M.loaded_segments (0x86fd0 : word) = Some W_86fd0.
Proof. vm_refl. Qed.
Lemma D_86fd0 : decode_any W_86fd0 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fd4 : bv 32 := 0x005080b3.
Lemma F_86fd4 : fetch_word Ubsan.M.loaded_segments (0x86fd4 : word) = Some W_86fd4.
Proof. vm_refl. Qed.
Lemma D_86fd4 : decode_any W_86fd4 = Some (Op ALU_ADD 1 1 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fd8 : bv 32 := 0x007d8db3.
Lemma F_86fd8 : fetch_word Ubsan.M.loaded_segments (0x86fd8 : word) = Some W_86fd8.
Proof. vm_refl. Qed.
Lemma D_86fd8 : decode_any W_86fd8 = Some (Op ALU_ADD 27 27 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fdc : bv 32 := 0x00060313.
Lemma F_86fdc : fetch_word Ubsan.M.loaded_segments (0x86fdc : word) = Some W_86fdc.
Proof. vm_refl. Qed.
Lemma D_86fdc : decode_any W_86fdc = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fe0 : bv 32 := 0x08013603.
Lemma F_86fe0 : fetch_word Ubsan.M.loaded_segments (0x86fe0 : word) = Some W_86fe0.
Proof. vm_refl. Qed.
Lemma D_86fe0 : decode_any W_86fe0 = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fe4 : bv 32 := 0xeec594e3.
Lemma F_86fe4 : fetch_word Ubsan.M.loaded_segments (0x86fe4 : word) = Some W_86fe4.
Proof. vm_refl. Qed.
Lemma D_86fe4 : decode_any W_86fe4 = Some (Branch BC_NE 11 12 7912, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fe8 : bv 32 := 0x01813583.
Lemma F_86fe8 : fetch_word Ubsan.M.loaded_segments (0x86fe8 : word) = Some W_86fe8.
Proof. vm_refl. Qed.
Lemma D_86fe8 : decode_any W_86fe8 = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fec : bv 32 := 0x5c059663.
Lemma F_86fec : fetch_word Ubsan.M.loaded_segments (0x86fec : word) = Some W_86fec.
Proof. vm_refl. Qed.
Lemma D_86fec : decode_any W_86fec = Some (Branch BC_NE 11 0 1484, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ff0 : bv 32 := 0x06813583.
Lemma F_86ff0 : fetch_word Ubsan.M.loaded_segments (0x86ff0 : word) = Some W_86ff0.
Proof. vm_refl. Qed.
Lemma D_86ff0 : decode_any W_86ff0 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ff4 : bv 32 := 0x0035f593.
Lemma F_86ff4 : fetch_word Ubsan.M.loaded_segments (0x86ff4 : word) = Some W_86ff4.
Proof. vm_refl. Qed.
Lemma D_86ff4 : decode_any W_86ff4 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ff8 : bv 32 := 0x00058463.
Lemma F_86ff8 : fetch_word Ubsan.M.loaded_segments (0x86ff8 : word) = Some W_86ff8.
Proof. vm_refl. Qed.
Lemma D_86ff8 : decode_any W_86ff8 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ffc : bv 32 := 0xcf8fb06f.
Lemma F_86ffc : fetch_word Ubsan.M.loaded_segments (0x86ffc : word) = Some W_86ffc.
Proof. vm_refl. Qed.
Lemma D_86ffc : decode_any W_86ffc = Some (Jal 0 2077944, 4%Z).
Proof. vm_refl. Qed.
