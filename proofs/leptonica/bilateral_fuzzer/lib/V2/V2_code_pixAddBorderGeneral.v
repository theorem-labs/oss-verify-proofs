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

Definition W_1c144 : bv 32 := 0xf9010113.
Lemma F_1c144 : fetch_word Ubsan.M.loaded_segments (0x1c144 : word) = Some W_1c144.
Proof. vm_refl. Qed.
Lemma D_1c144 : decode_any W_1c144 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c148 : bv 32 := 0x06113423.
Lemma F_1c148 : fetch_word Ubsan.M.loaded_segments (0x1c148 : word) = Some W_1c148.
Proof. vm_refl. Qed.
Lemma D_1c148 : decode_any W_1c148 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c14c : bv 32 := 0x06813023.
Lemma F_1c14c : fetch_word Ubsan.M.loaded_segments (0x1c14c : word) = Some W_1c14c.
Proof. vm_refl. Qed.
Lemma D_1c14c : decode_any W_1c14c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c150 : bv 32 := 0x04913c23.
Lemma F_1c150 : fetch_word Ubsan.M.loaded_segments (0x1c150 : word) = Some W_1c150.
Proof. vm_refl. Qed.
Lemma D_1c150 : decode_any W_1c150 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c154 : bv 32 := 0x05213823.
Lemma F_1c154 : fetch_word Ubsan.M.loaded_segments (0x1c154 : word) = Some W_1c154.
Proof. vm_refl. Qed.
Lemma D_1c154 : decode_any W_1c154 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c158 : bv 32 := 0x05313423.
Lemma F_1c158 : fetch_word Ubsan.M.loaded_segments (0x1c158 : word) = Some W_1c158.
Proof. vm_refl. Qed.
Lemma D_1c158 : decode_any W_1c158 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c15c : bv 32 := 0x05413023.
Lemma F_1c15c : fetch_word Ubsan.M.loaded_segments (0x1c15c : word) = Some W_1c15c.
Proof. vm_refl. Qed.
Lemma D_1c15c : decode_any W_1c15c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c160 : bv 32 := 0x03513c23.
Lemma F_1c160 : fetch_word Ubsan.M.loaded_segments (0x1c160 : word) = Some W_1c160.
Proof. vm_refl. Qed.
Lemma D_1c160 : decode_any W_1c160 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c164 : bv 32 := 0x03613823.
Lemma F_1c164 : fetch_word Ubsan.M.loaded_segments (0x1c164 : word) = Some W_1c164.
Proof. vm_refl. Qed.
Lemma D_1c164 : decode_any W_1c164 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c168 : bv 32 := 0x03713423.
Lemma F_1c168 : fetch_word Ubsan.M.loaded_segments (0x1c168 : word) = Some W_1c168.
Proof. vm_refl. Qed.
Lemma D_1c168 : decode_any W_1c168 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c16c : bv 32 := 0x03813023.
Lemma F_1c16c : fetch_word Ubsan.M.loaded_segments (0x1c16c : word) = Some W_1c16c.
Proof. vm_refl. Qed.
Lemma D_1c16c : decode_any W_1c16c = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c170 : bv 32 := 0x0c050a63.
Lemma F_1c170 : fetch_word Ubsan.M.loaded_segments (0x1c170 : word) = Some W_1c170.
Proof. vm_refl. Qed.
Lemma D_1c170 : decode_any W_1c170 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c174 : bv 32 := 0x00070993.
Lemma F_1c174 : fetch_word Ubsan.M.loaded_segments (0x1c174 : word) = Some W_1c174.
Proof. vm_refl. Qed.
Lemma D_1c174 : decode_any W_1c174 = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c178 : bv 32 := 0x00068493.
Lemma F_1c178 : fetch_word Ubsan.M.loaded_segments (0x1c178 : word) = Some W_1c178.
Proof. vm_refl. Qed.
Lemma D_1c178 : decode_any W_1c178 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c17c : bv 32 := 0x00060b13.
Lemma F_1c17c : fetch_word Ubsan.M.loaded_segments (0x1c17c : word) = Some W_1c17c.
Proof. vm_refl. Qed.
Lemma D_1c17c : decode_any W_1c17c = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c180 : bv 32 := 0x00058913.
Lemma F_1c180 : fetch_word Ubsan.M.loaded_segments (0x1c180 : word) = Some W_1c180.
Proof. vm_refl. Qed.
Lemma D_1c180 : decode_any W_1c180 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c184 : bv 32 := 0x00050413.
Lemma F_1c184 : fetch_word Ubsan.M.loaded_segments (0x1c184 : word) = Some W_1c184.
Proof. vm_refl. Qed.
Lemma D_1c184 : decode_any W_1c184 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c188 : bv 32 := 0x00b66533.
Lemma F_1c188 : fetch_word Ubsan.M.loaded_segments (0x1c188 : word) = Some W_1c188.
Proof. vm_refl. Qed.
Lemma D_1c188 : decode_any W_1c188 = Some (Op ALU_OR 10 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c18c : bv 32 := 0x00e6e5b3.
Lemma F_1c18c : fetch_word Ubsan.M.loaded_segments (0x1c18c : word) = Some W_1c18c.
Proof. vm_refl. Qed.
Lemma D_1c18c : decode_any W_1c18c = Some (Op ALU_OR 11 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c190 : bv 32 := 0x00b56533.
Lemma F_1c190 : fetch_word Ubsan.M.loaded_segments (0x1c190 : word) = Some W_1c190.
Proof. vm_refl. Qed.
Lemma D_1c190 : decode_any W_1c190 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c194 : bv 32 := 0x0c054c63.
Lemma F_1c194 : fetch_word Ubsan.M.loaded_segments (0x1c194 : word) = Some W_1c194.
Proof. vm_refl. Qed.
Lemma D_1c194 : decode_any W_1c194 = Some (Branch BC_LT 10 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c198 : bv 32 := 0x00078c13.
Lemma F_1c198 : fetch_word Ubsan.M.loaded_segments (0x1c198 : word) = Some W_1c198.
Proof. vm_refl. Qed.
Lemma D_1c198 : decode_any W_1c198 = Some (OpImm ALU_ADD 24 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c19c : bv 32 := 0x01c10593.
Lemma F_1c19c : fetch_word Ubsan.M.loaded_segments (0x1c19c : word) = Some W_1c19c.
Proof. vm_refl. Qed.
Lemma D_1c19c : decode_any W_1c19c = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1a0 : bv 32 := 0x01810613.
Lemma F_1c1a0 : fetch_word Ubsan.M.loaded_segments (0x1c1a0 : word) = Some W_1c1a0.
Proof. vm_refl. Qed.
Lemma D_1c1a0 : decode_any W_1c1a0 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1a4 : bv 32 := 0x01410693.
Lemma F_1c1a4 : fetch_word Ubsan.M.loaded_segments (0x1c1a4 : word) = Some W_1c1a4.
Proof. vm_refl. Qed.
Lemma D_1c1a4 : decode_any W_1c1a4 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1a8 : bv 32 := 0x00040513.
Lemma F_1c1a8 : fetch_word Ubsan.M.loaded_segments (0x1c1a8 : word) = Some W_1c1a8.
Proof. vm_refl. Qed.
Lemma D_1c1a8 : decode_any W_1c1a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1ac : bv 32 := 0x98dfd0ef.
Lemma F_1c1ac : fetch_word Ubsan.M.loaded_segments (0x1c1ac : word) = Some W_1c1ac.
Proof. vm_refl. Qed.
Lemma D_1c1ac : decode_any W_1c1ac = Some (Jal 1 2087308, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1b0 : bv 32 := 0x01c12583.
Lemma F_1c1b0 : fetch_word Ubsan.M.loaded_segments (0x1c1b0 : word) = Some W_1c1b0.
Proof. vm_refl. Qed.
Lemma D_1c1b0 : decode_any W_1c1b0 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1b4 : bv 32 := 0x01258533.
Lemma F_1c1b4 : fetch_word Ubsan.M.loaded_segments (0x1c1b4 : word) = Some W_1c1b4.
Proof. vm_refl. Qed.
Lemma D_1c1b4 : decode_any W_1c1b4 = Some (Op ALU_ADD 10 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1b8 : bv 32 := 0x012585bb.
Lemma F_1c1b8 : fetch_word Ubsan.M.loaded_segments (0x1c1b8 : word) = Some W_1c1b8.
Proof. vm_refl. Qed.
Lemma D_1c1b8 : decode_any W_1c1b8 = Some (Op32 ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1bc : bv 32 := 0x28a59063.
Lemma F_1c1bc : fetch_word Ubsan.M.loaded_segments (0x1c1bc : word) = Some W_1c1bc.
Proof. vm_refl. Qed.
Lemma D_1c1bc : decode_any W_1c1bc = Some (Branch BC_NE 11 10 640, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1c0 : bv 32 := 0x0005051b.
Lemma F_1c1c0 : fetch_word Ubsan.M.loaded_segments (0x1c1c0 : word) = Some W_1c1c0.
Proof. vm_refl. Qed.
Lemma D_1c1c0 : decode_any W_1c1c0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1c4 : bv 32 := 0x01650abb.
Lemma F_1c1c4 : fetch_word Ubsan.M.loaded_segments (0x1c1c4 : word) = Some W_1c1c4.
Proof. vm_refl. Qed.
Lemma D_1c1c4 : decode_any W_1c1c4 = Some (Op32 ALU_ADD 21 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1c8 : bv 32 := 0x01650533.
Lemma F_1c1c8 : fetch_word Ubsan.M.loaded_segments (0x1c1c8 : word) = Some W_1c1c8.
Proof. vm_refl. Qed.
Lemma D_1c1c8 : decode_any W_1c1c8 = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1cc : bv 32 := 0x26aa9863.
Lemma F_1c1cc : fetch_word Ubsan.M.loaded_segments (0x1c1cc : word) = Some W_1c1cc.
Proof. vm_refl. Qed.
Lemma D_1c1cc : decode_any W_1c1cc = Some (Branch BC_NE 21 10 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1d0 : bv 32 := 0x01812583.
Lemma F_1c1d0 : fetch_word Ubsan.M.loaded_segments (0x1c1d0 : word) = Some W_1c1d0.
Proof. vm_refl. Qed.
Lemma D_1c1d0 : decode_any W_1c1d0 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1d4 : bv 32 := 0x00958533.
Lemma F_1c1d4 : fetch_word Ubsan.M.loaded_segments (0x1c1d4 : word) = Some W_1c1d4.
Proof. vm_refl. Qed.
Lemma D_1c1d4 : decode_any W_1c1d4 = Some (Op ALU_ADD 10 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1d8 : bv 32 := 0x009585bb.
Lemma F_1c1d8 : fetch_word Ubsan.M.loaded_segments (0x1c1d8 : word) = Some W_1c1d8.
Proof. vm_refl. Qed.
Lemma D_1c1d8 : decode_any W_1c1d8 = Some (Op32 ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1dc : bv 32 := 0x26a59063.
Lemma F_1c1dc : fetch_word Ubsan.M.loaded_segments (0x1c1dc : word) = Some W_1c1dc.
Proof. vm_refl. Qed.
Lemma D_1c1dc : decode_any W_1c1dc = Some (Branch BC_NE 11 10 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1e0 : bv 32 := 0x0005051b.
Lemma F_1c1e0 : fetch_word Ubsan.M.loaded_segments (0x1c1e0 : word) = Some W_1c1e0.
Proof. vm_refl. Qed.
Lemma D_1c1e0 : decode_any W_1c1e0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1e4 : bv 32 := 0x01350bbb.
Lemma F_1c1e4 : fetch_word Ubsan.M.loaded_segments (0x1c1e4 : word) = Some W_1c1e4.
Proof. vm_refl. Qed.
Lemma D_1c1e4 : decode_any W_1c1e4 = Some (Op32 ALU_ADD 23 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1e8 : bv 32 := 0x01350533.
Lemma F_1c1e8 : fetch_word Ubsan.M.loaded_segments (0x1c1e8 : word) = Some W_1c1e8.
Proof. vm_refl. Qed.
Lemma D_1c1e8 : decode_any W_1c1e8 = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1ec : bv 32 := 0x24ab9863.
Lemma F_1c1ec : fetch_word Ubsan.M.loaded_segments (0x1c1ec : word) = Some W_1c1ec.
Proof. vm_refl. Qed.
Lemma D_1c1ec : decode_any W_1c1ec = Some (Branch BC_NE 23 10 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1f0 : bv 32 := 0x01412603.
Lemma F_1c1f0 : fetch_word Ubsan.M.loaded_segments (0x1c1f0 : word) = Some W_1c1f0.
Proof. vm_refl. Qed.
Lemma D_1c1f0 : decode_any W_1c1f0 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1f4 : bv 32 := 0x000a8513.
Lemma F_1c1f4 : fetch_word Ubsan.M.loaded_segments (0x1c1f4 : word) = Some W_1c1f4.
Proof. vm_refl. Qed.
Lemma D_1c1f4 : decode_any W_1c1f4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1f8 : bv 32 := 0x000b8593.
Lemma F_1c1f8 : fetch_word Ubsan.M.loaded_segments (0x1c1f8 : word) = Some W_1c1f8.
Proof. vm_refl. Qed.
Lemma D_1c1f8 : decode_any W_1c1f8 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c1fc : bv 32 := 0x8d4fd0ef.
Lemma F_1c1fc : fetch_word Ubsan.M.loaded_segments (0x1c1fc : word) = Some W_1c1fc.
Proof. vm_refl. Qed.
Lemma D_1c1fc : decode_any W_1c1fc = Some (Jal 1 2085076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c200 : bv 32 := 0x0c050263.
Lemma F_1c200 : fetch_word Ubsan.M.loaded_segments (0x1c200 : word) = Some W_1c200.
Proof. vm_refl. Qed.
Lemma D_1c200 : decode_any W_1c200 = Some (Branch BC_EQ 10 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c204 : bv 32 := 0x00050a13.
Lemma F_1c204 : fetch_word Ubsan.M.loaded_segments (0x1c204 : word) = Some W_1c204.
Proof. vm_refl. Qed.
Lemma D_1c204 : decode_any W_1c204 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c208 : bv 32 := 0x00040593.
Lemma F_1c208 : fetch_word Ubsan.M.loaded_segments (0x1c208 : word) = Some W_1c208.
Proof. vm_refl. Qed.
Lemma D_1c208 : decode_any W_1c208 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c20c : bv 32 := 0x9e9fd0ef.
Lemma F_1c20c : fetch_word Ubsan.M.loaded_segments (0x1c20c : word) = Some W_1c20c.
Proof. vm_refl. Qed.
Lemma D_1c20c : decode_any W_1c20c = Some (Jal 1 2087400, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c210 : bv 32 := 0x000a0513.
Lemma F_1c210 : fetch_word Ubsan.M.loaded_segments (0x1c210 : word) = Some W_1c210.
Proof. vm_refl. Qed.
Lemma D_1c210 : decode_any W_1c210 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c214 : bv 32 := 0x00040593.
Lemma F_1c214 : fetch_word Ubsan.M.loaded_segments (0x1c214 : word) = Some W_1c214.
Proof. vm_refl. Qed.
Lemma D_1c214 : decode_any W_1c214 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c218 : bv 32 := 0xa6dfd0ef.
Lemma F_1c218 : fetch_word Ubsan.M.loaded_segments (0x1c218 : word) = Some W_1c218.
Proof. vm_refl. Qed.
Lemma D_1c218 : decode_any W_1c218 = Some (Jal 1 2087532, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c21c : bv 32 := 0x01412503.
Lemma F_1c21c : fetch_word Ubsan.M.loaded_segments (0x1c21c : word) = Some W_1c21c.
Proof. vm_refl. Qed.
Lemma D_1c21c : decode_any W_1c21c = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c220 : bv 32 := 0x02000593.
Lemma F_1c220 : fetch_word Ubsan.M.loaded_segments (0x1c220 : word) = Some W_1c220.
Proof. vm_refl. Qed.
Lemma D_1c220 : decode_any W_1c220 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c224 : bv 32 := 0x0cb51e63.
Lemma F_1c224 : fetch_word Ubsan.M.loaded_segments (0x1c224 : word) = Some W_1c224.
Proof. vm_refl. Qed.
Lemma D_1c224 : decode_any W_1c224 = Some (Branch BC_NE 10 11 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c228 : bv 32 := 0xf0000513.
Lemma F_1c228 : fetch_word Ubsan.M.loaded_segments (0x1c228 : word) = Some W_1c228.
Proof. vm_refl. Qed.
Lemma D_1c228 : decode_any W_1c228 = Some (OpImm ALU_ADD 10 0 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c22c : bv 32 := 0x000c0593.
Lemma F_1c22c : fetch_word Ubsan.M.loaded_segments (0x1c22c : word) = Some W_1c22c.
Proof. vm_refl. Qed.
Lemma D_1c22c : decode_any W_1c22c = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c230 : bv 32 := 0x0e0c0663.
Lemma F_1c230 : fetch_word Ubsan.M.loaded_segments (0x1c230 : word) = Some W_1c230.
Proof. vm_refl. Qed.
Lemma D_1c230 : decode_any W_1c230 = Some (Branch BC_EQ 24 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c234 : bv 32 := 0x0ea5f863.
Lemma F_1c234 : fetch_word Ubsan.M.loaded_segments (0x1c234 : word) = Some W_1c234.
Proof. vm_refl. Qed.
Lemma D_1c234 : decode_any W_1c234 = Some (Branch BC_GEU 11 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c238 : bv 32 := 0x000a0513.
Lemma F_1c238 : fetch_word Ubsan.M.loaded_segments (0x1c238 : word) = Some W_1c238.
Proof. vm_refl. Qed.
Lemma D_1c238 : decode_any W_1c238 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c23c : bv 32 := 0x974ff0ef.
Lemma F_1c23c : fetch_word Ubsan.M.loaded_segments (0x1c23c : word) = Some W_1c23c.
Proof. vm_refl. Qed.
Lemma D_1c23c : decode_any W_1c23c = Some (Jal 1 2093428, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c240 : bv 32 := 0x1a00006f.
Lemma F_1c240 : fetch_word Ubsan.M.loaded_segments (0x1c240 : word) = Some W_1c240.
Proof. vm_refl. Qed.
Lemma D_1c240 : decode_any W_1c240 = Some (Jal 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c244 : bv 32 := 0x00029517.
Lemma F_1c244 : fetch_word Ubsan.M.loaded_segments (0x1c244 : word) = Some W_1c244.
Proof. vm_refl. Qed.
Lemma D_1c244 : decode_any W_1c244 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c248 : bv 32 := 0xc5453503.
Lemma F_1c248 : fetch_word Ubsan.M.loaded_segments (0x1c248 : word) = Some W_1c248.
Proof. vm_refl. Qed.
Lemma D_1c248 : decode_any W_1c248 = Some (Load SZ8 true 10 10 3156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c24c : bv 32 := 0x00052503.
Lemma F_1c24c : fetch_word Ubsan.M.loaded_segments (0x1c24c : word) = Some W_1c24c.
Proof. vm_refl. Qed.
Lemma D_1c24c : decode_any W_1c24c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c250 : bv 32 := 0x00500593.
Lemma F_1c250 : fetch_word Ubsan.M.loaded_segments (0x1c250 : word) = Some W_1c250.
Proof. vm_refl. Qed.
Lemma D_1c250 : decode_any W_1c250 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c254 : bv 32 := 0x0aa5c263.
Lemma F_1c254 : fetch_word Ubsan.M.loaded_segments (0x1c254 : word) = Some W_1c254.
Proof. vm_refl. Qed.
Lemma D_1c254 : decode_any W_1c254 = Some (Branch BC_LT 11 10 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c258 : bv 32 := 0xffff4517.
Lemma F_1c258 : fetch_word Ubsan.M.loaded_segments (0x1c258 : word) = Some W_1c258.
Proof. vm_refl. Qed.
Lemma D_1c258 : decode_any W_1c258 = Some (Auipc 10 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c25c : bv 32 := 0xffff5597.
Lemma F_1c25c : fetch_word Ubsan.M.loaded_segments (0x1c25c : word) = Some W_1c25c.
Proof. vm_refl. Qed.
Lemma D_1c25c : decode_any W_1c25c = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c260 : bv 32 := 0x05c50513.
Lemma F_1c260 : fetch_word Ubsan.M.loaded_segments (0x1c260 : word) = Some W_1c260.
Proof. vm_refl. Qed.
Lemma D_1c260 : decode_any W_1c260 = Some (OpImm ALU_ADD 10 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c264 : bv 32 := 0x11c58593.
Lemma F_1c264 : fetch_word Ubsan.M.loaded_segments (0x1c264 : word) = Some W_1c264.
Proof. vm_refl. Qed.
Lemma D_1c264 : decode_any W_1c264 = Some (OpImm ALU_ADD 11 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c268 : bv 32 := 0x0280006f.
Lemma F_1c268 : fetch_word Ubsan.M.loaded_segments (0x1c268 : word) = Some W_1c268.
Proof. vm_refl. Qed.
Lemma D_1c268 : decode_any W_1c268 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c26c : bv 32 := 0x00029517.
Lemma F_1c26c : fetch_word Ubsan.M.loaded_segments (0x1c26c : word) = Some W_1c26c.
Proof. vm_refl. Qed.
Lemma D_1c26c : decode_any W_1c26c = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c270 : bv 32 := 0xc2c53503.
Lemma F_1c270 : fetch_word Ubsan.M.loaded_segments (0x1c270 : word) = Some W_1c270.
Proof. vm_refl. Qed.
Lemma D_1c270 : decode_any W_1c270 = Some (Load SZ8 true 10 10 3116, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c274 : bv 32 := 0x00052503.
Lemma F_1c274 : fetch_word Ubsan.M.loaded_segments (0x1c274 : word) = Some W_1c274.
Proof. vm_refl. Qed.
Lemma D_1c274 : decode_any W_1c274 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c278 : bv 32 := 0x00500593.
Lemma F_1c278 : fetch_word Ubsan.M.loaded_segments (0x1c278 : word) = Some W_1c278.
Proof. vm_refl. Qed.
Lemma D_1c278 : decode_any W_1c278 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c27c : bv 32 := 0x06a5ce63.
Lemma F_1c27c : fetch_word Ubsan.M.loaded_segments (0x1c27c : word) = Some W_1c27c.
Proof. vm_refl. Qed.
Lemma D_1c27c : decode_any W_1c27c = Some (Branch BC_LT 11 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c280 : bv 32 := 0xffff4517.
Lemma F_1c280 : fetch_word Ubsan.M.loaded_segments (0x1c280 : word) = Some W_1c280.
Proof. vm_refl. Qed.
Lemma D_1c280 : decode_any W_1c280 = Some (Auipc 10 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c284 : bv 32 := 0xffff5597.
Lemma F_1c284 : fetch_word Ubsan.M.loaded_segments (0x1c284 : word) = Some W_1c284.
Proof. vm_refl. Qed.
Lemma D_1c284 : decode_any W_1c284 = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c288 : bv 32 := 0x68b50513.
Lemma F_1c288 : fetch_word Ubsan.M.loaded_segments (0x1c288 : word) = Some W_1c288.
Proof. vm_refl. Qed.
Lemma D_1c288 : decode_any W_1c288 = Some (OpImm ALU_ADD 10 10 1675, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c28c : bv 32 := 0x0f458593.
Lemma F_1c28c : fetch_word Ubsan.M.loaded_segments (0x1c28c : word) = Some W_1c28c.
Proof. vm_refl. Qed.
Lemma D_1c28c : decode_any W_1c28c = Some (OpImm ALU_ADD 11 11 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c290 : bv 32 := 0x00000613.
Lemma F_1c290 : fetch_word Ubsan.M.loaded_segments (0x1c290 : word) = Some W_1c290.
Proof. vm_refl. Qed.
Lemma D_1c290 : decode_any W_1c290 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c294 : bv 32 := 0x06813083.
Lemma F_1c294 : fetch_word Ubsan.M.loaded_segments (0x1c294 : word) = Some W_1c294.
Proof. vm_refl. Qed.
Lemma D_1c294 : decode_any W_1c294 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c298 : bv 32 := 0x06013403.
Lemma F_1c298 : fetch_word Ubsan.M.loaded_segments (0x1c298 : word) = Some W_1c298.
Proof. vm_refl. Qed.
Lemma D_1c298 : decode_any W_1c298 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c29c : bv 32 := 0x05813483.
Lemma F_1c29c : fetch_word Ubsan.M.loaded_segments (0x1c29c : word) = Some W_1c29c.
Proof. vm_refl. Qed.
Lemma D_1c29c : decode_any W_1c29c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2a0 : bv 32 := 0x05013903.
Lemma F_1c2a0 : fetch_word Ubsan.M.loaded_segments (0x1c2a0 : word) = Some W_1c2a0.
Proof. vm_refl. Qed.
Lemma D_1c2a0 : decode_any W_1c2a0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2a4 : bv 32 := 0x04813983.
Lemma F_1c2a4 : fetch_word Ubsan.M.loaded_segments (0x1c2a4 : word) = Some W_1c2a4.
Proof. vm_refl. Qed.
Lemma D_1c2a4 : decode_any W_1c2a4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2a8 : bv 32 := 0x04013a03.
Lemma F_1c2a8 : fetch_word Ubsan.M.loaded_segments (0x1c2a8 : word) = Some W_1c2a8.
Proof. vm_refl. Qed.
Lemma D_1c2a8 : decode_any W_1c2a8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2ac : bv 32 := 0x03813a83.
Lemma F_1c2ac : fetch_word Ubsan.M.loaded_segments (0x1c2ac : word) = Some W_1c2ac.
Proof. vm_refl. Qed.
Lemma D_1c2ac : decode_any W_1c2ac = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2b0 : bv 32 := 0x03013b03.
Lemma F_1c2b0 : fetch_word Ubsan.M.loaded_segments (0x1c2b0 : word) = Some W_1c2b0.
Proof. vm_refl. Qed.
Lemma D_1c2b0 : decode_any W_1c2b0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2b4 : bv 32 := 0x02813b83.
Lemma F_1c2b4 : fetch_word Ubsan.M.loaded_segments (0x1c2b4 : word) = Some W_1c2b4.
Proof. vm_refl. Qed.
Lemma D_1c2b4 : decode_any W_1c2b4 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2b8 : bv 32 := 0x02013c03.
Lemma F_1c2b8 : fetch_word Ubsan.M.loaded_segments (0x1c2b8 : word) = Some W_1c2b8.
Proof. vm_refl. Qed.
Lemma D_1c2b8 : decode_any W_1c2b8 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2bc : bv 32 := 0x07010113.
Lemma F_1c2bc : fetch_word Ubsan.M.loaded_segments (0x1c2bc : word) = Some W_1c2bc.
Proof. vm_refl. Qed.
Lemma D_1c2bc : decode_any W_1c2bc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2c0 : bv 32 := 0xc05fb06f.
Lemma F_1c2c0 : fetch_word Ubsan.M.loaded_segments (0x1c2c0 : word) = Some W_1c2c0.
Proof. vm_refl. Qed.
Lemma D_1c2c0 : decode_any W_1c2c0 = Some (Jal 0 2079748, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2c4 : bv 32 := 0x00029517.
Lemma F_1c2c4 : fetch_word Ubsan.M.loaded_segments (0x1c2c4 : word) = Some W_1c2c4.
Proof. vm_refl. Qed.
Lemma D_1c2c4 : decode_any W_1c2c4 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2c8 : bv 32 := 0xbd453503.
Lemma F_1c2c8 : fetch_word Ubsan.M.loaded_segments (0x1c2c8 : word) = Some W_1c2c8.
Proof. vm_refl. Qed.
Lemma D_1c2c8 : decode_any W_1c2c8 = Some (Load SZ8 true 10 10 3028, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2cc : bv 32 := 0x00052503.
Lemma F_1c2cc : fetch_word Ubsan.M.loaded_segments (0x1c2cc : word) = Some W_1c2cc.
Proof. vm_refl. Qed.
Lemma D_1c2cc : decode_any W_1c2cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2d0 : bv 32 := 0x00500593.
Lemma F_1c2d0 : fetch_word Ubsan.M.loaded_segments (0x1c2d0 : word) = Some W_1c2d0.
Proof. vm_refl. Qed.
Lemma D_1c2d0 : decode_any W_1c2d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2d4 : bv 32 := 0x02a5c263.
Lemma F_1c2d4 : fetch_word Ubsan.M.loaded_segments (0x1c2d4 : word) = Some W_1c2d4.
Proof. vm_refl. Qed.
Lemma D_1c2d4 : decode_any W_1c2d4 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2d8 : bv 32 := 0xffff4517.
Lemma F_1c2d8 : fetch_word Ubsan.M.loaded_segments (0x1c2d8 : word) = Some W_1c2d8.
Proof. vm_refl. Qed.
Lemma D_1c2d8 : decode_any W_1c2d8 = Some (Auipc 10 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2dc : bv 32 := 0xffff5597.
Lemma F_1c2dc : fetch_word Ubsan.M.loaded_segments (0x1c2dc : word) = Some W_1c2dc.
Proof. vm_refl. Qed.
Lemma D_1c2dc : decode_any W_1c2dc = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2e0 : bv 32 := 0x48d50513.
Lemma F_1c2e0 : fetch_word Ubsan.M.loaded_segments (0x1c2e0 : word) = Some W_1c2e0.
Proof. vm_refl. Qed.
Lemma D_1c2e0 : decode_any W_1c2e0 = Some (OpImm ALU_ADD 10 10 1165, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2e4 : bv 32 := 0x09c58593.
Lemma F_1c2e4 : fetch_word Ubsan.M.loaded_segments (0x1c2e4 : word) = Some W_1c2e4.
Proof. vm_refl. Qed.
Lemma D_1c2e4 : decode_any W_1c2e4 = Some (OpImm ALU_ADD 11 11 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2e8 : bv 32 := 0x00000613.
Lemma F_1c2e8 : fetch_word Ubsan.M.loaded_segments (0x1c2e8 : word) = Some W_1c2e8.
Proof. vm_refl. Qed.
Lemma D_1c2e8 : decode_any W_1c2e8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2ec : bv 32 := 0xbd9fb0ef.
Lemma F_1c2ec : fetch_word Ubsan.M.loaded_segments (0x1c2ec : word) = Some W_1c2ec.
Proof. vm_refl. Qed.
Lemma D_1c2ec : decode_any W_1c2ec = Some (Jal 1 2079704, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2f0 : bv 32 := 0x00050a13.
Lemma F_1c2f0 : fetch_word Ubsan.M.loaded_segments (0x1c2f0 : word) = Some W_1c2f0.
Proof. vm_refl. Qed.
Lemma D_1c2f0 : decode_any W_1c2f0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2f4 : bv 32 := 0x1140006f.
Lemma F_1c2f4 : fetch_word Ubsan.M.loaded_segments (0x1c2f4 : word) = Some W_1c2f4.
Proof. vm_refl. Qed.
Lemma D_1c2f4 : decode_any W_1c2f4 = Some (Jal 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2f8 : bv 32 := 0x00000a13.
Lemma F_1c2f8 : fetch_word Ubsan.M.loaded_segments (0x1c2f8 : word) = Some W_1c2f8.
Proof. vm_refl. Qed.
Lemma D_1c2f8 : decode_any W_1c2f8 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c2fc : bv 32 := 0x10c0006f.
Lemma F_1c2fc : fetch_word Ubsan.M.loaded_segments (0x1c2fc : word) = Some W_1c2fc.
Proof. vm_refl. Qed.
Lemma D_1c2fc : decode_any W_1c2fc = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c300 : bv 32 := 0x01f00613.
Lemma F_1c300 : fetch_word Ubsan.M.loaded_segments (0x1c300 : word) = Some W_1c300.
Proof. vm_refl. Qed.
Lemma D_1c300 : decode_any W_1c300 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c304 : bv 32 := 0x12c57c63.
Lemma F_1c304 : fetch_word Ubsan.M.loaded_segments (0x1c304 : word) = Some W_1c304.
Proof. vm_refl. Qed.
Lemma D_1c304 : decode_any W_1c304 = Some (Branch BC_GEU 10 12 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c308 : bv 32 := 0x000c0593.
Lemma F_1c308 : fetch_word Ubsan.M.loaded_segments (0x1c308 : word) = Some W_1c308.
Proof. vm_refl. Qed.
Lemma D_1c308 : decode_any W_1c308 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c30c : bv 32 := 0xfff00613.
Lemma F_1c30c : fetch_word Ubsan.M.loaded_segments (0x1c30c : word) = Some W_1c30c.
Proof. vm_refl. Qed.
Lemma D_1c30c : decode_any W_1c30c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c310 : bv 32 := 0x00a6153b.
Lemma F_1c310 : fetch_word Ubsan.M.loaded_segments (0x1c310 : word) = Some W_1c310.
Proof. vm_refl. Qed.
Lemma D_1c310 : decode_any W_1c310 = Some (Op32 ALU_SLL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c314 : bv 32 := 0xfff54513.
Lemma F_1c314 : fetch_word Ubsan.M.loaded_segments (0x1c314 : word) = Some W_1c314.
Proof. vm_refl. Qed.
Lemma D_1c314 : decode_any W_1c314 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c318 : bv 32 := 0xf00c1ee3.
Lemma F_1c318 : fetch_word Ubsan.M.loaded_segments (0x1c318 : word) = Some W_1c318.
Proof. vm_refl. Qed.
Lemma D_1c318 : decode_any W_1c318 = Some (Branch BC_NE 24 0 7964, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c31c : bv 32 := 0x00000c13.
Lemma F_1c31c : fetch_word Ubsan.M.loaded_segments (0x1c31c : word) = Some W_1c31c.
Proof. vm_refl. Qed.
Lemma D_1c31c : decode_any W_1c31c = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c320 : bv 32 := 0x0080006f.
Lemma F_1c320 : fetch_word Ubsan.M.loaded_segments (0x1c320 : word) = Some W_1c320.
Proof. vm_refl. Qed.
Lemma D_1c320 : decode_any W_1c320 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c324 : bv 32 := 0x00f00c13.
Lemma F_1c324 : fetch_word Ubsan.M.loaded_segments (0x1c324 : word) = Some W_1c324.
Proof. vm_refl. Qed.
Lemma D_1c324 : decode_any W_1c324 = Some (OpImm ALU_ADD 24 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c328 : bv 32 := 0x00013023.
Lemma F_1c328 : fetch_word Ubsan.M.loaded_segments (0x1c328 : word) = Some W_1c328.
Proof. vm_refl. Qed.
Lemma D_1c328 : decode_any W_1c328 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c32c : bv 32 := 0x000a0513.
Lemma F_1c32c : fetch_word Ubsan.M.loaded_segments (0x1c32c : word) = Some W_1c32c.
Proof. vm_refl. Qed.
Lemma D_1c32c : decode_any W_1c32c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c330 : bv 32 := 0x00000593.
Lemma F_1c330 : fetch_word Ubsan.M.loaded_segments (0x1c330 : word) = Some W_1c330.
Proof. vm_refl. Qed.
Lemma D_1c330 : decode_any W_1c330 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c334 : bv 32 := 0x00000613.
Lemma F_1c334 : fetch_word Ubsan.M.loaded_segments (0x1c334 : word) = Some W_1c334.
Proof. vm_refl. Qed.
Lemma D_1c334 : decode_any W_1c334 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c338 : bv 32 := 0x00090693.
Lemma F_1c338 : fetch_word Ubsan.M.loaded_segments (0x1c338 : word) = Some W_1c338.
Proof. vm_refl. Qed.
Lemma D_1c338 : decode_any W_1c338 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c33c : bv 32 := 0x000b8713.
Lemma F_1c33c : fetch_word Ubsan.M.loaded_segments (0x1c33c : word) = Some W_1c33c.
Proof. vm_refl. Qed.
Lemma D_1c33c : decode_any W_1c33c = Some (OpImm ALU_ADD 14 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c340 : bv 32 := 0x000c0793.
Lemma F_1c340 : fetch_word Ubsan.M.loaded_segments (0x1c340 : word) = Some W_1c340.
Proof. vm_refl. Qed.
Lemma D_1c340 : decode_any W_1c340 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c344 : bv 32 := 0x00000813.
Lemma F_1c344 : fetch_word Ubsan.M.loaded_segments (0x1c344 : word) = Some W_1c344.
Proof. vm_refl. Qed.
Lemma D_1c344 : decode_any W_1c344 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c348 : bv 32 := 0x00000893.
Lemma F_1c348 : fetch_word Ubsan.M.loaded_segments (0x1c348 : word) = Some W_1c348.
Proof. vm_refl. Qed.
Lemma D_1c348 : decode_any W_1c348 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c34c : bv 32 := 0x0a40b0ef.
Lemma F_1c34c : fetch_word Ubsan.M.loaded_segments (0x1c34c : word) = Some W_1c34c.
Proof. vm_refl. Qed.
Lemma D_1c34c : decode_any W_1c34c = Some (Jal 1 45220, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c350 : bv 32 := 0x416a85b3.
Lemma F_1c350 : fetch_word Ubsan.M.loaded_segments (0x1c350 : word) = Some W_1c350.
Proof. vm_refl. Qed.
Lemma D_1c350 : decode_any W_1c350 = Some (Op ALU_SUB 11 21 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c354 : bv 32 := 0x416a853b.
Lemma F_1c354 : fetch_word Ubsan.M.loaded_segments (0x1c354 : word) = Some W_1c354.
Proof. vm_refl. Qed.
Lemma D_1c354 : decode_any W_1c354 = Some (Op32 ALU_SUB 10 21 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c358 : bv 32 := 0x0eb51263.
Lemma F_1c358 : fetch_word Ubsan.M.loaded_segments (0x1c358 : word) = Some W_1c358.
Proof. vm_refl. Qed.
Lemma D_1c358 : decode_any W_1c358 = Some (Branch BC_NE 10 11 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c35c : bv 32 := 0x0005859b.
Lemma F_1c35c : fetch_word Ubsan.M.loaded_segments (0x1c35c : word) = Some W_1c35c.
Proof. vm_refl. Qed.
Lemma D_1c35c : decode_any W_1c35c = Some (OpImm32 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c360 : bv 32 := 0x00013023.
Lemma F_1c360 : fetch_word Ubsan.M.loaded_segments (0x1c360 : word) = Some W_1c360.
Proof. vm_refl. Qed.
Lemma D_1c360 : decode_any W_1c360 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c364 : bv 32 := 0x000a0513.
Lemma F_1c364 : fetch_word Ubsan.M.loaded_segments (0x1c364 : word) = Some W_1c364.
Proof. vm_refl. Qed.
Lemma D_1c364 : decode_any W_1c364 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c368 : bv 32 := 0x00000613.
Lemma F_1c368 : fetch_word Ubsan.M.loaded_segments (0x1c368 : word) = Some W_1c368.
Proof. vm_refl. Qed.
Lemma D_1c368 : decode_any W_1c368 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c36c : bv 32 := 0x000b0693.
Lemma F_1c36c : fetch_word Ubsan.M.loaded_segments (0x1c36c : word) = Some W_1c36c.
Proof. vm_refl. Qed.
Lemma D_1c36c : decode_any W_1c36c = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c370 : bv 32 := 0x000b8713.
Lemma F_1c370 : fetch_word Ubsan.M.loaded_segments (0x1c370 : word) = Some W_1c370.
Proof. vm_refl. Qed.
Lemma D_1c370 : decode_any W_1c370 = Some (OpImm ALU_ADD 14 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c374 : bv 32 := 0x000c0793.
Lemma F_1c374 : fetch_word Ubsan.M.loaded_segments (0x1c374 : word) = Some W_1c374.
Proof. vm_refl. Qed.
Lemma D_1c374 : decode_any W_1c374 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c378 : bv 32 := 0x00000813.
Lemma F_1c378 : fetch_word Ubsan.M.loaded_segments (0x1c378 : word) = Some W_1c378.
Proof. vm_refl. Qed.
Lemma D_1c378 : decode_any W_1c378 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c37c : bv 32 := 0x00000893.
Lemma F_1c37c : fetch_word Ubsan.M.loaded_segments (0x1c37c : word) = Some W_1c37c.
Proof. vm_refl. Qed.
Lemma D_1c37c : decode_any W_1c37c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c380 : bv 32 := 0x0700b0ef.
Lemma F_1c380 : fetch_word Ubsan.M.loaded_segments (0x1c380 : word) = Some W_1c380.
Proof. vm_refl. Qed.
Lemma D_1c380 : decode_any W_1c380 = Some (Jal 1 45168, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c384 : bv 32 := 0x00013023.
Lemma F_1c384 : fetch_word Ubsan.M.loaded_segments (0x1c384 : word) = Some W_1c384.
Proof. vm_refl. Qed.
Lemma D_1c384 : decode_any W_1c384 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c388 : bv 32 := 0x000a0513.
Lemma F_1c388 : fetch_word Ubsan.M.loaded_segments (0x1c388 : word) = Some W_1c388.
Proof. vm_refl. Qed.
Lemma D_1c388 : decode_any W_1c388 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c38c : bv 32 := 0x00000593.
Lemma F_1c38c : fetch_word Ubsan.M.loaded_segments (0x1c38c : word) = Some W_1c38c.
Proof. vm_refl. Qed.
Lemma D_1c38c : decode_any W_1c38c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c390 : bv 32 := 0x00000613.
Lemma F_1c390 : fetch_word Ubsan.M.loaded_segments (0x1c390 : word) = Some W_1c390.
Proof. vm_refl. Qed.
Lemma D_1c390 : decode_any W_1c390 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c394 : bv 32 := 0x000a8693.
Lemma F_1c394 : fetch_word Ubsan.M.loaded_segments (0x1c394 : word) = Some W_1c394.
Proof. vm_refl. Qed.
Lemma D_1c394 : decode_any W_1c394 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c398 : bv 32 := 0x00048713.
Lemma F_1c398 : fetch_word Ubsan.M.loaded_segments (0x1c398 : word) = Some W_1c398.
Proof. vm_refl. Qed.
Lemma D_1c398 : decode_any W_1c398 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c39c : bv 32 := 0x000c0793.
Lemma F_1c39c : fetch_word Ubsan.M.loaded_segments (0x1c39c : word) = Some W_1c39c.
Proof. vm_refl. Qed.
Lemma D_1c39c : decode_any W_1c39c = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3a0 : bv 32 := 0x00000813.
Lemma F_1c3a0 : fetch_word Ubsan.M.loaded_segments (0x1c3a0 : word) = Some W_1c3a0.
Proof. vm_refl. Qed.
Lemma D_1c3a0 : decode_any W_1c3a0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3a4 : bv 32 := 0x00000893.
Lemma F_1c3a4 : fetch_word Ubsan.M.loaded_segments (0x1c3a4 : word) = Some W_1c3a4.
Proof. vm_refl. Qed.
Lemma D_1c3a4 : decode_any W_1c3a4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3a8 : bv 32 := 0x0480b0ef.
Lemma F_1c3a8 : fetch_word Ubsan.M.loaded_segments (0x1c3a8 : word) = Some W_1c3a8.
Proof. vm_refl. Qed.
Lemma D_1c3a8 : decode_any W_1c3a8 = Some (Jal 1 45128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3ac : bv 32 := 0x413b8633.
Lemma F_1c3ac : fetch_word Ubsan.M.loaded_segments (0x1c3ac : word) = Some W_1c3ac.
Proof. vm_refl. Qed.
Lemma D_1c3ac : decode_any W_1c3ac = Some (Op ALU_SUB 12 23 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3b0 : bv 32 := 0x413b853b.
Lemma F_1c3b0 : fetch_word Ubsan.M.loaded_segments (0x1c3b0 : word) = Some W_1c3b0.
Proof. vm_refl. Qed.
Lemma D_1c3b0 : decode_any W_1c3b0 = Some (Op32 ALU_SUB 10 23 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3b4 : bv 32 := 0x08c51463.
Lemma F_1c3b4 : fetch_word Ubsan.M.loaded_segments (0x1c3b4 : word) = Some W_1c3b4.
Proof. vm_refl. Qed.
Lemma D_1c3b4 : decode_any W_1c3b4 = Some (Branch BC_NE 10 12 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3b8 : bv 32 := 0x0006061b.
Lemma F_1c3b8 : fetch_word Ubsan.M.loaded_segments (0x1c3b8 : word) = Some W_1c3b8.
Proof. vm_refl. Qed.
Lemma D_1c3b8 : decode_any W_1c3b8 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3bc : bv 32 := 0x00013023.
Lemma F_1c3bc : fetch_word Ubsan.M.loaded_segments (0x1c3bc : word) = Some W_1c3bc.
Proof. vm_refl. Qed.
Lemma D_1c3bc : decode_any W_1c3bc = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3c0 : bv 32 := 0x000a0513.
Lemma F_1c3c0 : fetch_word Ubsan.M.loaded_segments (0x1c3c0 : word) = Some W_1c3c0.
Proof. vm_refl. Qed.
Lemma D_1c3c0 : decode_any W_1c3c0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3c4 : bv 32 := 0x00000593.
Lemma F_1c3c4 : fetch_word Ubsan.M.loaded_segments (0x1c3c4 : word) = Some W_1c3c4.
Proof. vm_refl. Qed.
Lemma D_1c3c4 : decode_any W_1c3c4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3c8 : bv 32 := 0x000a8693.
Lemma F_1c3c8 : fetch_word Ubsan.M.loaded_segments (0x1c3c8 : word) = Some W_1c3c8.
Proof. vm_refl. Qed.
Lemma D_1c3c8 : decode_any W_1c3c8 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3cc : bv 32 := 0x00098713.
Lemma F_1c3cc : fetch_word Ubsan.M.loaded_segments (0x1c3cc : word) = Some W_1c3cc.
Proof. vm_refl. Qed.
Lemma D_1c3cc : decode_any W_1c3cc = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3d0 : bv 32 := 0x000c0793.
Lemma F_1c3d0 : fetch_word Ubsan.M.loaded_segments (0x1c3d0 : word) = Some W_1c3d0.
Proof. vm_refl. Qed.
Lemma D_1c3d0 : decode_any W_1c3d0 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3d4 : bv 32 := 0x00000813.
Lemma F_1c3d4 : fetch_word Ubsan.M.loaded_segments (0x1c3d4 : word) = Some W_1c3d4.
Proof. vm_refl. Qed.
Lemma D_1c3d4 : decode_any W_1c3d4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3d8 : bv 32 := 0x00000893.
Lemma F_1c3d8 : fetch_word Ubsan.M.loaded_segments (0x1c3d8 : word) = Some W_1c3d8.
Proof. vm_refl. Qed.
Lemma D_1c3d8 : decode_any W_1c3d8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3dc : bv 32 := 0x0140b0ef.
Lemma F_1c3dc : fetch_word Ubsan.M.loaded_segments (0x1c3dc : word) = Some W_1c3dc.
Proof. vm_refl. Qed.
Lemma D_1c3dc : decode_any W_1c3dc = Some (Jal 1 45076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3e0 : bv 32 := 0x01c12683.
Lemma F_1c3e0 : fetch_word Ubsan.M.loaded_segments (0x1c3e0 : word) = Some W_1c3e0.
Proof. vm_refl. Qed.
Lemma D_1c3e0 : decode_any W_1c3e0 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3e4 : bv 32 := 0x01812703.
Lemma F_1c3e4 : fetch_word Ubsan.M.loaded_segments (0x1c3e4 : word) = Some W_1c3e4.
Proof. vm_refl. Qed.
Lemma D_1c3e4 : decode_any W_1c3e4 = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3e8 : bv 32 := 0x00c00793.
Lemma F_1c3e8 : fetch_word Ubsan.M.loaded_segments (0x1c3e8 : word) = Some W_1c3e8.
Proof. vm_refl. Qed.
Lemma D_1c3e8 : decode_any W_1c3e8 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3ec : bv 32 := 0x00013023.
Lemma F_1c3ec : fetch_word Ubsan.M.loaded_segments (0x1c3ec : word) = Some W_1c3ec.
Proof. vm_refl. Qed.
Lemma D_1c3ec : decode_any W_1c3ec = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3f0 : bv 32 := 0x000a0513.
Lemma F_1c3f0 : fetch_word Ubsan.M.loaded_segments (0x1c3f0 : word) = Some W_1c3f0.
Proof. vm_refl. Qed.
Lemma D_1c3f0 : decode_any W_1c3f0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3f4 : bv 32 := 0x00090593.
Lemma F_1c3f4 : fetch_word Ubsan.M.loaded_segments (0x1c3f4 : word) = Some W_1c3f4.
Proof. vm_refl. Qed.
Lemma D_1c3f4 : decode_any W_1c3f4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3f8 : bv 32 := 0x00048613.
Lemma F_1c3f8 : fetch_word Ubsan.M.loaded_segments (0x1c3f8 : word) = Some W_1c3f8.
Proof. vm_refl. Qed.
Lemma D_1c3f8 : decode_any W_1c3f8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c3fc : bv 32 := 0x00040813.
Lemma F_1c3fc : fetch_word Ubsan.M.loaded_segments (0x1c3fc : word) = Some W_1c3fc.
Proof. vm_refl. Qed.
Lemma D_1c3fc : decode_any W_1c3fc = Some (OpImm ALU_ADD 16 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c400 : bv 32 := 0x00000893.
Lemma F_1c400 : fetch_word Ubsan.M.loaded_segments (0x1c400 : word) = Some W_1c400.
Proof. vm_refl. Qed.
Lemma D_1c400 : decode_any W_1c400 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c404 : bv 32 := 0x7ed0a0ef.
Lemma F_1c404 : fetch_word Ubsan.M.loaded_segments (0x1c404 : word) = Some W_1c404.
Proof. vm_refl. Qed.
Lemma D_1c404 : decode_any W_1c404 = Some (Jal 1 45036, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c408 : bv 32 := 0x000a0513.
Lemma F_1c408 : fetch_word Ubsan.M.loaded_segments (0x1c408 : word) = Some W_1c408.
Proof. vm_refl. Qed.
Lemma D_1c408 : decode_any W_1c408 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c40c : bv 32 := 0x06813083.
Lemma F_1c40c : fetch_word Ubsan.M.loaded_segments (0x1c40c : word) = Some W_1c40c.
Proof. vm_refl. Qed.
Lemma D_1c40c : decode_any W_1c40c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c410 : bv 32 := 0x06013403.
Lemma F_1c410 : fetch_word Ubsan.M.loaded_segments (0x1c410 : word) = Some W_1c410.
Proof. vm_refl. Qed.
Lemma D_1c410 : decode_any W_1c410 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c414 : bv 32 := 0x05813483.
Lemma F_1c414 : fetch_word Ubsan.M.loaded_segments (0x1c414 : word) = Some W_1c414.
Proof. vm_refl. Qed.
Lemma D_1c414 : decode_any W_1c414 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c418 : bv 32 := 0x05013903.
Lemma F_1c418 : fetch_word Ubsan.M.loaded_segments (0x1c418 : word) = Some W_1c418.
Proof. vm_refl. Qed.
Lemma D_1c418 : decode_any W_1c418 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c41c : bv 32 := 0x04813983.
Lemma F_1c41c : fetch_word Ubsan.M.loaded_segments (0x1c41c : word) = Some W_1c41c.
Proof. vm_refl. Qed.
Lemma D_1c41c : decode_any W_1c41c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c420 : bv 32 := 0x04013a03.
Lemma F_1c420 : fetch_word Ubsan.M.loaded_segments (0x1c420 : word) = Some W_1c420.
Proof. vm_refl. Qed.
Lemma D_1c420 : decode_any W_1c420 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c424 : bv 32 := 0x03813a83.
Lemma F_1c424 : fetch_word Ubsan.M.loaded_segments (0x1c424 : word) = Some W_1c424.
Proof. vm_refl. Qed.
Lemma D_1c424 : decode_any W_1c424 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c428 : bv 32 := 0x03013b03.
Lemma F_1c428 : fetch_word Ubsan.M.loaded_segments (0x1c428 : word) = Some W_1c428.
Proof. vm_refl. Qed.
Lemma D_1c428 : decode_any W_1c428 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c42c : bv 32 := 0x02813b83.
Lemma F_1c42c : fetch_word Ubsan.M.loaded_segments (0x1c42c : word) = Some W_1c42c.
Proof. vm_refl. Qed.
Lemma D_1c42c : decode_any W_1c42c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c430 : bv 32 := 0x02013c03.
Lemma F_1c430 : fetch_word Ubsan.M.loaded_segments (0x1c430 : word) = Some W_1c430.
Proof. vm_refl. Qed.
Lemma D_1c430 : decode_any W_1c430 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c434 : bv 32 := 0x07010113.
Lemma F_1c434 : fetch_word Ubsan.M.loaded_segments (0x1c434 : word) = Some W_1c434.
Proof. vm_refl. Qed.
Lemma D_1c434 : decode_any W_1c434 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c438 : bv 32 := 0x00008067.
Lemma F_1c438 : fetch_word Ubsan.M.loaded_segments (0x1c438 : word) = Some W_1c438.
Proof. vm_refl. Qed.
Lemma D_1c438 : decode_any W_1c438 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c43c : bv 32 := 0xc0001073.
Lemma F_1c43c : fetch_word Ubsan.M.loaded_segments (0x1c43c : word) = Some W_1c43c.
Proof. vm_refl. Qed.
Lemma D_1c43c : decode_any W_1c43c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
