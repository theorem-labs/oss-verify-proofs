(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ce11c : bv 32 := 0x0035f693.
Lemma F_ce11c : fetch_word Ubsan.M.loaded_segments (0xce2d4 : word) = Some W_ce11c.
Proof. vm_refl. Qed.
Lemma D_ce11c : decode_any W_ce11c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce120 : bv 32 := 0x10068863.
Lemma F_ce120 : fetch_word Ubsan.M.loaded_segments (0xce2d8 : word) = Some W_ce120.
Proof. vm_refl. Qed.
Lemma D_ce120 : decode_any W_ce120 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce124 : bv 32 := 0x02060e63.
Lemma F_ce124 : fetch_word Ubsan.M.loaded_segments (0xce2dc : word) = Some W_ce124.
Proof. vm_refl. Qed.
Lemma D_ce124 : decode_any W_ce124 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce128 : bv 32 := 0x00158713.
Lemma F_ce128 : fetch_word Ubsan.M.loaded_segments (0xce2e0 : word) = Some W_ce128.
Proof. vm_refl. Qed.
Lemma D_ce128 : decode_any W_ce128 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce12c : bv 32 := 0x00100793.
Lemma F_ce12c : fetch_word Ubsan.M.loaded_segments (0xce2e4 : word) = Some W_ce12c.
Proof. vm_refl. Qed.
Lemma D_ce12c : decode_any W_ce12c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce130 : bv 32 := 0x00050693.
Lemma F_ce130 : fetch_word Ubsan.M.loaded_segments (0xce2e8 : word) = Some W_ce130.
Proof. vm_refl. Qed.
Lemma D_ce130 : decode_any W_ce130 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce134 : bv 32 := 0x0005c883.
Lemma F_ce134 : fetch_word Ubsan.M.loaded_segments (0xce2ec : word) = Some W_ce134.
Proof. vm_refl. Qed.
Lemma D_ce134 : decode_any W_ce134 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce138 : bv 32 := 0x00060813.
Lemma F_ce138 : fetch_word Ubsan.M.loaded_segments (0xce2f0 : word) = Some W_ce138.
Proof. vm_refl. Qed.
Lemma D_ce138 : decode_any W_ce138 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce13c : bv 32 := 0x00158593.
Lemma F_ce13c : fetch_word Ubsan.M.loaded_segments (0xce2f4 : word) = Some W_ce13c.
Proof. vm_refl. Qed.
Lemma D_ce13c : decode_any W_ce13c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce140 : bv 32 := 0x00377293.
Lemma F_ce140 : fetch_word Ubsan.M.loaded_segments (0xce2f8 : word) = Some W_ce140.
Proof. vm_refl. Qed.
Lemma D_ce140 : decode_any W_ce140 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce144 : bv 32 := 0x01168023.
Lemma F_ce144 : fetch_word Ubsan.M.loaded_segments (0xce2fc : word) = Some W_ce144.
Proof. vm_refl. Qed.
Lemma D_ce144 : decode_any W_ce144 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce148 : bv 32 := 0x00168693.
Lemma F_ce148 : fetch_word Ubsan.M.loaded_segments (0xce300 : word) = Some W_ce148.
Proof. vm_refl. Qed.
Lemma D_ce148 : decode_any W_ce148 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce14c : bv 32 := 0xfff60613.
Lemma F_ce14c : fetch_word Ubsan.M.loaded_segments (0xce304 : word) = Some W_ce14c.
Proof. vm_refl. Qed.
Lemma D_ce14c : decode_any W_ce14c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce150 : bv 32 := 0x00028a63.
Lemma F_ce150 : fetch_word Ubsan.M.loaded_segments (0xce308 : word) = Some W_ce150.
Proof. vm_refl. Qed.
Lemma D_ce150 : decode_any W_ce150 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce154 : bv 32 := 0x00170713.
Lemma F_ce154 : fetch_word Ubsan.M.loaded_segments (0xce30c : word) = Some W_ce154.
Proof. vm_refl. Qed.
Lemma D_ce154 : decode_any W_ce154 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce158 : bv 32 := 0xfcf81ee3.
Lemma F_ce158 : fetch_word Ubsan.M.loaded_segments (0xce310 : word) = Some W_ce158.
Proof. vm_refl. Qed.
Lemma D_ce158 : decode_any W_ce158 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce15c : bv 32 := 0x0080006f.
Lemma F_ce15c : fetch_word Ubsan.M.loaded_segments (0xce314 : word) = Some W_ce15c.
Proof. vm_refl. Qed.
Lemma D_ce15c : decode_any W_ce15c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce160 : bv 32 := 0x00050693.
Lemma F_ce160 : fetch_word Ubsan.M.loaded_segments (0xce318 : word) = Some W_ce160.
Proof. vm_refl. Qed.
Lemma D_ce160 : decode_any W_ce160 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce164 : bv 32 := 0x0036f793.
Lemma F_ce164 : fetch_word Ubsan.M.loaded_segments (0xce31c : word) = Some W_ce164.
Proof. vm_refl. Qed.
Lemma D_ce164 : decode_any W_ce164 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce168 : bv 32 := 0x0c078a63.
Lemma F_ce168 : fetch_word Ubsan.M.loaded_segments (0xce320 : word) = Some W_ce168.
Proof. vm_refl. Qed.
Lemma D_ce168 : decode_any W_ce168 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce16c : bv 32 := 0x02000713.
Lemma F_ce16c : fetch_word Ubsan.M.loaded_segments (0xce324 : word) = Some W_ce16c.
Proof. vm_refl. Qed.
Lemma D_ce16c : decode_any W_ce16c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce170 : bv 32 := 0x02e67063.
Lemma F_ce170 : fetch_word Ubsan.M.loaded_segments (0xce328 : word) = Some W_ce170.
Proof. vm_refl. Qed.
Lemma D_ce170 : decode_any W_ce170 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce174 : bv 32 := 0x01000713.
Lemma F_ce174 : fetch_word Ubsan.M.loaded_segments (0xce32c : word) = Some W_ce174.
Proof. vm_refl. Qed.
Lemma D_ce174 : decode_any W_ce174 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce178 : bv 32 := 0x24e67863.
Lemma F_ce178 : fetch_word Ubsan.M.loaded_segments (0xce330 : word) = Some W_ce178.
Proof. vm_refl. Qed.
Lemma D_ce178 : decode_any W_ce178 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce17c : bv 32 := 0x00867713.
Lemma F_ce17c : fetch_word Ubsan.M.loaded_segments (0xce334 : word) = Some W_ce17c.
Proof. vm_refl. Qed.
Lemma D_ce17c : decode_any W_ce17c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce180 : bv 32 := 0x2c071e63.
Lemma F_ce180 : fetch_word Ubsan.M.loaded_segments (0xce338 : word) = Some W_ce180.
Proof. vm_refl. Qed.
Lemma D_ce180 : decode_any W_ce180 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce184 : bv 32 := 0x00467713.
Lemma F_ce184 : fetch_word Ubsan.M.loaded_segments (0xce33c : word) = Some W_ce184.
Proof. vm_refl. Qed.
Lemma D_ce184 : decode_any W_ce184 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce188 : bv 32 := 0x32071463.
Lemma F_ce188 : fetch_word Ubsan.M.loaded_segments (0xce340 : word) = Some W_ce188.
Proof. vm_refl. Qed.
Lemma D_ce188 : decode_any W_ce188 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce18c : bv 32 := 0x3500006f.
Lemma F_ce18c : fetch_word Ubsan.M.loaded_segments (0xce344 : word) = Some W_ce18c.
Proof. vm_refl. Qed.
Lemma D_ce18c : decode_any W_ce18c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce190 : bv 32 := 0x0005a703.
Lemma F_ce190 : fetch_word Ubsan.M.loaded_segments (0xce348 : word) = Some W_ce190.
Proof. vm_refl. Qed.
Lemma D_ce190 : decode_any W_ce190 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce194 : bv 32 := 0x00300813.
Lemma F_ce194 : fetch_word Ubsan.M.loaded_segments (0xce34c : word) = Some W_ce194.
Proof. vm_refl. Qed.
Lemma D_ce194 : decode_any W_ce194 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce198 : bv 32 := 0x11078e63.
Lemma F_ce198 : fetch_word Ubsan.M.loaded_segments (0xce350 : word) = Some W_ce198.
Proof. vm_refl. Qed.
Lemma D_ce198 : decode_any W_ce198 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce19c : bv 32 := 0x00200813.
Lemma F_ce19c : fetch_word Ubsan.M.loaded_segments (0xce354 : word) = Some W_ce19c.
Proof. vm_refl. Qed.
Lemma D_ce19c : decode_any W_ce19c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1a0 : bv 32 := 0x19079c63.
Lemma F_ce1a0 : fetch_word Ubsan.M.loaded_segments (0xce358 : word) = Some W_ce1a0.
Proof. vm_refl. Qed.
Lemma D_ce1a0 : decode_any W_ce1a0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1a4 : bv 32 := 0x00875793.
Lemma F_ce1a4 : fetch_word Ubsan.M.loaded_segments (0xce35c : word) = Some W_ce1a4.
Proof. vm_refl. Qed.
Lemma D_ce1a4 : decode_any W_ce1a4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1a8 : bv 32 := 0xffe60613.
Lemma F_ce1a8 : fetch_word Ubsan.M.loaded_segments (0xce360 : word) = Some W_ce1a8.
Proof. vm_refl. Qed.
Lemma D_ce1a8 : decode_any W_ce1a8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1ac : bv 32 := 0x00e68023.
Lemma F_ce1ac : fetch_word Ubsan.M.loaded_segments (0xce364 : word) = Some W_ce1ac.
Proof. vm_refl. Qed.
Lemma D_ce1ac : decode_any W_ce1ac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1b0 : bv 32 := 0x00f680a3.
Lemma F_ce1b0 : fetch_word Ubsan.M.loaded_segments (0xce368 : word) = Some W_ce1b0.
Proof. vm_refl. Qed.
Lemma D_ce1b0 : decode_any W_ce1b0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1b4 : bv 32 := 0x00268693.
Lemma F_ce1b4 : fetch_word Ubsan.M.loaded_segments (0xce36c : word) = Some W_ce1b4.
Proof. vm_refl. Qed.
Lemma D_ce1b4 : decode_any W_ce1b4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1b8 : bv 32 := 0x01058593.
Lemma F_ce1b8 : fetch_word Ubsan.M.loaded_segments (0xce370 : word) = Some W_ce1b8.
Proof. vm_refl. Qed.
Lemma D_ce1b8 : decode_any W_ce1b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1bc : bv 32 := 0x01100793.
Lemma F_ce1bc : fetch_word Ubsan.M.loaded_segments (0xce374 : word) = Some W_ce1bc.
Proof. vm_refl. Qed.
Lemma D_ce1bc : decode_any W_ce1bc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1c0 : bv 32 := 0x0107581b.
Lemma F_ce1c0 : fetch_word Ubsan.M.loaded_segments (0xce378 : word) = Some W_ce1c0.
Proof. vm_refl. Qed.
Lemma D_ce1c0 : decode_any W_ce1c0 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1c4 : bv 32 := 0xff45a883.
Lemma F_ce1c4 : fetch_word Ubsan.M.loaded_segments (0xce37c : word) = Some W_ce1c4.
Proof. vm_refl. Qed.
Lemma D_ce1c4 : decode_any W_ce1c4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1c8 : bv 32 := 0xff85a283.
Lemma F_ce1c8 : fetch_word Ubsan.M.loaded_segments (0xce380 : word) = Some W_ce1c8.
Proof. vm_refl. Qed.
Lemma D_ce1c8 : decode_any W_ce1c8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1cc : bv 32 := 0xffc5a303.
Lemma F_ce1cc : fetch_word Ubsan.M.loaded_segments (0xce384 : word) = Some W_ce1cc.
Proof. vm_refl. Qed.
Lemma D_ce1cc : decode_any W_ce1cc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1d0 : bv 32 := 0x0005a703.
Lemma F_ce1d0 : fetch_word Ubsan.M.loaded_segments (0xce388 : word) = Some W_ce1d0.
Proof. vm_refl. Qed.
Lemma D_ce1d0 : decode_any W_ce1d0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1d4 : bv 32 := 0x01089393.
Lemma F_ce1d4 : fetch_word Ubsan.M.loaded_segments (0xce38c : word) = Some W_ce1d4.
Proof. vm_refl. Qed.
Lemma D_ce1d4 : decode_any W_ce1d4 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1d8 : bv 32 := 0x0108d89b.
Lemma F_ce1d8 : fetch_word Ubsan.M.loaded_segments (0xce390 : word) = Some W_ce1d8.
Proof. vm_refl. Qed.
Lemma D_ce1d8 : decode_any W_ce1d8 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1dc : bv 32 := 0x0103e833.
Lemma F_ce1dc : fetch_word Ubsan.M.loaded_segments (0xce394 : word) = Some W_ce1dc.
Proof. vm_refl. Qed.
Lemma D_ce1dc : decode_any W_ce1dc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1e0 : bv 32 := 0x01029393.
Lemma F_ce1e0 : fetch_word Ubsan.M.loaded_segments (0xce398 : word) = Some W_ce1e0.
Proof. vm_refl. Qed.
Lemma D_ce1e0 : decode_any W_ce1e0 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1e4 : bv 32 := 0x0102d29b.
Lemma F_ce1e4 : fetch_word Ubsan.M.loaded_segments (0xce39c : word) = Some W_ce1e4.
Proof. vm_refl. Qed.
Lemma D_ce1e4 : decode_any W_ce1e4 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1e8 : bv 32 := 0x0113e8b3.
Lemma F_ce1e8 : fetch_word Ubsan.M.loaded_segments (0xce3a0 : word) = Some W_ce1e8.
Proof. vm_refl. Qed.
Lemma D_ce1e8 : decode_any W_ce1e8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1ec : bv 32 := 0x01031393.
Lemma F_ce1ec : fetch_word Ubsan.M.loaded_segments (0xce3a4 : word) = Some W_ce1ec.
Proof. vm_refl. Qed.
Lemma D_ce1ec : decode_any W_ce1ec = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1f0 : bv 32 := 0x0103531b.
Lemma F_ce1f0 : fetch_word Ubsan.M.loaded_segments (0xce3a8 : word) = Some W_ce1f0.
Proof. vm_refl. Qed.
Lemma D_ce1f0 : decode_any W_ce1f0 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1f4 : bv 32 := 0x0053e2b3.
Lemma F_ce1f4 : fetch_word Ubsan.M.loaded_segments (0xce3ac : word) = Some W_ce1f4.
Proof. vm_refl. Qed.
Lemma D_ce1f4 : decode_any W_ce1f4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1f8 : bv 32 := 0x01071393.
Lemma F_ce1f8 : fetch_word Ubsan.M.loaded_segments (0xce3b0 : word) = Some W_ce1f8.
Proof. vm_refl. Qed.
Lemma D_ce1f8 : decode_any W_ce1f8 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce1fc : bv 32 := 0x0063e333.
Lemma F_ce1fc : fetch_word Ubsan.M.loaded_segments (0xce3b4 : word) = Some W_ce1fc.
Proof. vm_refl. Qed.
Lemma D_ce1fc : decode_any W_ce1fc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce200 : bv 32 := 0xff060613.
Lemma F_ce200 : fetch_word Ubsan.M.loaded_segments (0xce3b8 : word) = Some W_ce200.
Proof. vm_refl. Qed.
Lemma D_ce200 : decode_any W_ce200 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce204 : bv 32 := 0x0106a023.
Lemma F_ce204 : fetch_word Ubsan.M.loaded_segments (0xce3bc : word) = Some W_ce204.
Proof. vm_refl. Qed.
Lemma D_ce204 : decode_any W_ce204 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce208 : bv 32 := 0x0116a223.
Lemma F_ce208 : fetch_word Ubsan.M.loaded_segments (0xce3c0 : word) = Some W_ce208.
Proof. vm_refl. Qed.
Lemma D_ce208 : decode_any W_ce208 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce20c : bv 32 := 0x0056a423.
Lemma F_ce20c : fetch_word Ubsan.M.loaded_segments (0xce3c4 : word) = Some W_ce20c.
Proof. vm_refl. Qed.
Lemma D_ce20c : decode_any W_ce20c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce210 : bv 32 := 0x0066a623.
Lemma F_ce210 : fetch_word Ubsan.M.loaded_segments (0xce3c8 : word) = Some W_ce210.
Proof. vm_refl. Qed.
Lemma D_ce210 : decode_any W_ce210 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce214 : bv 32 := 0x01068693.
Lemma F_ce214 : fetch_word Ubsan.M.loaded_segments (0xce3cc : word) = Some W_ce214.
Proof. vm_refl. Qed.
Lemma D_ce214 : decode_any W_ce214 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce218 : bv 32 := 0x01058593.
Lemma F_ce218 : fetch_word Ubsan.M.loaded_segments (0xce3d0 : word) = Some W_ce218.
Proof. vm_refl. Qed.
Lemma D_ce218 : decode_any W_ce218 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce21c : bv 32 := 0xfac7e2e3.
Lemma F_ce21c : fetch_word Ubsan.M.loaded_segments (0xce3d4 : word) = Some W_ce21c.
Proof. vm_refl. Qed.
Lemma D_ce21c : decode_any W_ce21c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce220 : bv 32 := 0xff258593.
Lemma F_ce220 : fetch_word Ubsan.M.loaded_segments (0xce3d8 : word) = Some W_ce220.
Proof. vm_refl. Qed.
Lemma D_ce220 : decode_any W_ce220 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce224 : bv 32 := 0x01000713.
Lemma F_ce224 : fetch_word Ubsan.M.loaded_segments (0xce3dc : word) = Some W_ce224.
Proof. vm_refl. Qed.
Lemma D_ce224 : decode_any W_ce224 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce228 : bv 32 := 0xf4e66ae3.
Lemma F_ce228 : fetch_word Ubsan.M.loaded_segments (0xce3e0 : word) = Some W_ce228.
Proof. vm_refl. Qed.
Lemma D_ce228 : decode_any W_ce228 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce22c : bv 32 := 0x19c0006f.
Lemma F_ce22c : fetch_word Ubsan.M.loaded_segments (0xce3e4 : word) = Some W_ce22c.
Proof. vm_refl. Qed.
Lemma D_ce22c : decode_any W_ce22c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce230 : bv 32 := 0x00050693.
Lemma F_ce230 : fetch_word Ubsan.M.loaded_segments (0xce3e8 : word) = Some W_ce230.
Proof. vm_refl. Qed.
Lemma D_ce230 : decode_any W_ce230 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce234 : bv 32 := 0x00357793.
Lemma F_ce234 : fetch_word Ubsan.M.loaded_segments (0xce3ec : word) = Some W_ce234.
Proof. vm_refl. Qed.
Lemma D_ce234 : decode_any W_ce234 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce238 : bv 32 := 0xf2079ae3.
Lemma F_ce238 : fetch_word Ubsan.M.loaded_segments (0xce3f0 : word) = Some W_ce238.
Proof. vm_refl. Qed.
Lemma D_ce238 : decode_any W_ce238 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce23c : bv 32 := 0x01000713.
Lemma F_ce23c : fetch_word Ubsan.M.loaded_segments (0xce3f4 : word) = Some W_ce23c.
Proof. vm_refl. Qed.
Lemma D_ce23c : decode_any W_ce23c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce240 : bv 32 := 0x02e66c63.
Lemma F_ce240 : fetch_word Ubsan.M.loaded_segments (0xce3f8 : word) = Some W_ce240.
Proof. vm_refl. Qed.
Lemma D_ce240 : decode_any W_ce240 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce244 : bv 32 := 0x00f00713.
Lemma F_ce244 : fetch_word Ubsan.M.loaded_segments (0xce3fc : word) = Some W_ce244.
Proof. vm_refl. Qed.
Lemma D_ce244 : decode_any W_ce244 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce248 : bv 32 := 0x0005a783.
Lemma F_ce248 : fetch_word Ubsan.M.loaded_segments (0xce400 : word) = Some W_ce248.
Proof. vm_refl. Qed.
Lemma D_ce248 : decode_any W_ce248 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce24c : bv 32 := 0x0045a803.
Lemma F_ce24c : fetch_word Ubsan.M.loaded_segments (0xce404 : word) = Some W_ce24c.
Proof. vm_refl. Qed.
Lemma D_ce24c : decode_any W_ce24c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce250 : bv 32 := 0x0085a883.
Lemma F_ce250 : fetch_word Ubsan.M.loaded_segments (0xce408 : word) = Some W_ce250.
Proof. vm_refl. Qed.
Lemma D_ce250 : decode_any W_ce250 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce254 : bv 32 := 0x00c5a283.
Lemma F_ce254 : fetch_word Ubsan.M.loaded_segments (0xce40c : word) = Some W_ce254.
Proof. vm_refl. Qed.
Lemma D_ce254 : decode_any W_ce254 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce258 : bv 32 := 0x01058593.
Lemma F_ce258 : fetch_word Ubsan.M.loaded_segments (0xce410 : word) = Some W_ce258.
Proof. vm_refl. Qed.
Lemma D_ce258 : decode_any W_ce258 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce25c : bv 32 := 0xff060613.
Lemma F_ce25c : fetch_word Ubsan.M.loaded_segments (0xce414 : word) = Some W_ce25c.
Proof. vm_refl. Qed.
Lemma D_ce25c : decode_any W_ce25c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce260 : bv 32 := 0x00f6a023.
Lemma F_ce260 : fetch_word Ubsan.M.loaded_segments (0xce418 : word) = Some W_ce260.
Proof. vm_refl. Qed.
Lemma D_ce260 : decode_any W_ce260 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce264 : bv 32 := 0x0106a223.
Lemma F_ce264 : fetch_word Ubsan.M.loaded_segments (0xce41c : word) = Some W_ce264.
Proof. vm_refl. Qed.
Lemma D_ce264 : decode_any W_ce264 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce268 : bv 32 := 0x0116a423.
Lemma F_ce268 : fetch_word Ubsan.M.loaded_segments (0xce420 : word) = Some W_ce268.
Proof. vm_refl. Qed.
Lemma D_ce268 : decode_any W_ce268 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce26c : bv 32 := 0x0056a623.
Lemma F_ce26c : fetch_word Ubsan.M.loaded_segments (0xce424 : word) = Some W_ce26c.
Proof. vm_refl. Qed.
Lemma D_ce26c : decode_any W_ce26c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce270 : bv 32 := 0x01068693.
Lemma F_ce270 : fetch_word Ubsan.M.loaded_segments (0xce428 : word) = Some W_ce270.
Proof. vm_refl. Qed.
Lemma D_ce270 : decode_any W_ce270 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce274 : bv 32 := 0xfcc76ae3.
Lemma F_ce274 : fetch_word Ubsan.M.loaded_segments (0xce42c : word) = Some W_ce274.
Proof. vm_refl. Qed.
Lemma D_ce274 : decode_any W_ce274 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce278 : bv 32 := 0x00800713.
Lemma F_ce278 : fetch_word Ubsan.M.loaded_segments (0xce430 : word) = Some W_ce278.
Proof. vm_refl. Qed.
Lemma D_ce278 : decode_any W_ce278 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce27c : bv 32 := 0x00e66e63.
Lemma F_ce27c : fetch_word Ubsan.M.loaded_segments (0xce434 : word) = Some W_ce27c.
Proof. vm_refl. Qed.
Lemma D_ce27c : decode_any W_ce27c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce280 : bv 32 := 0x0005a703.
Lemma F_ce280 : fetch_word Ubsan.M.loaded_segments (0xce438 : word) = Some W_ce280.
Proof. vm_refl. Qed.
Lemma D_ce280 : decode_any W_ce280 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce284 : bv 32 := 0x0045a783.
Lemma F_ce284 : fetch_word Ubsan.M.loaded_segments (0xce43c : word) = Some W_ce284.
Proof. vm_refl. Qed.
Lemma D_ce284 : decode_any W_ce284 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce288 : bv 32 := 0x00e6a023.
Lemma F_ce288 : fetch_word Ubsan.M.loaded_segments (0xce440 : word) = Some W_ce288.
Proof. vm_refl. Qed.
Lemma D_ce288 : decode_any W_ce288 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce28c : bv 32 := 0x00f6a223.
Lemma F_ce28c : fetch_word Ubsan.M.loaded_segments (0xce444 : word) = Some W_ce28c.
Proof. vm_refl. Qed.
Lemma D_ce28c : decode_any W_ce28c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce290 : bv 32 := 0x00868693.
Lemma F_ce290 : fetch_word Ubsan.M.loaded_segments (0xce448 : word) = Some W_ce290.
Proof. vm_refl. Qed.
Lemma D_ce290 : decode_any W_ce290 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce294 : bv 32 := 0x00858593.
Lemma F_ce294 : fetch_word Ubsan.M.loaded_segments (0xce44c : word) = Some W_ce294.
Proof. vm_refl. Qed.
Lemma D_ce294 : decode_any W_ce294 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce298 : bv 32 := 0x00467713.
Lemma F_ce298 : fetch_word Ubsan.M.loaded_segments (0xce450 : word) = Some W_ce298.
Proof. vm_refl. Qed.
Lemma D_ce298 : decode_any W_ce298 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce29c : bv 32 := 0x24070063.
Lemma F_ce29c : fetch_word Ubsan.M.loaded_segments (0xce454 : word) = Some W_ce29c.
Proof. vm_refl. Qed.
Lemma D_ce29c : decode_any W_ce29c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2a0 : bv 32 := 0x0005a703.
Lemma F_ce2a0 : fetch_word Ubsan.M.loaded_segments (0xce458 : word) = Some W_ce2a0.
Proof. vm_refl. Qed.
Lemma D_ce2a0 : decode_any W_ce2a0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2a4 : bv 32 := 0x00458593.
Lemma F_ce2a4 : fetch_word Ubsan.M.loaded_segments (0xce45c : word) = Some W_ce2a4.
Proof. vm_refl. Qed.
Lemma D_ce2a4 : decode_any W_ce2a4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2a8 : bv 32 := 0x00e6a023.
Lemma F_ce2a8 : fetch_word Ubsan.M.loaded_segments (0xce460 : word) = Some W_ce2a8.
Proof. vm_refl. Qed.
Lemma D_ce2a8 : decode_any W_ce2a8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2ac : bv 32 := 0x00468693.
Lemma F_ce2ac : fetch_word Ubsan.M.loaded_segments (0xce464 : word) = Some W_ce2ac.
Proof. vm_refl. Qed.
Lemma D_ce2ac : decode_any W_ce2ac = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2b0 : bv 32 := 0x22c0006f.
Lemma F_ce2b0 : fetch_word Ubsan.M.loaded_segments (0xce468 : word) = Some W_ce2b0.
Proof. vm_refl. Qed.
Lemma D_ce2b0 : decode_any W_ce2b0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2b4 : bv 32 := 0x00e68023.
Lemma F_ce2b4 : fetch_word Ubsan.M.loaded_segments (0xce46c : word) = Some W_ce2b4.
Proof. vm_refl. Qed.
Lemma D_ce2b4 : decode_any W_ce2b4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2b8 : bv 32 := 0x00168693.
Lemma F_ce2b8 : fetch_word Ubsan.M.loaded_segments (0xce470 : word) = Some W_ce2b8.
Proof. vm_refl. Qed.
Lemma D_ce2b8 : decode_any W_ce2b8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2bc : bv 32 := 0xfff60613.
Lemma F_ce2bc : fetch_word Ubsan.M.loaded_segments (0xce474 : word) = Some W_ce2bc.
Proof. vm_refl. Qed.
Lemma D_ce2bc : decode_any W_ce2bc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2c0 : bv 32 := 0x01058593.
Lemma F_ce2c0 : fetch_word Ubsan.M.loaded_segments (0xce478 : word) = Some W_ce2c0.
Proof. vm_refl. Qed.
Lemma D_ce2c0 : decode_any W_ce2c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2c4 : bv 32 := 0x01200793.
Lemma F_ce2c4 : fetch_word Ubsan.M.loaded_segments (0xce47c : word) = Some W_ce2c4.
Proof. vm_refl. Qed.
Lemma D_ce2c4 : decode_any W_ce2c4 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2c8 : bv 32 := 0x0087581b.
Lemma F_ce2c8 : fetch_word Ubsan.M.loaded_segments (0xce480 : word) = Some W_ce2c8.
Proof. vm_refl. Qed.
Lemma D_ce2c8 : decode_any W_ce2c8 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2cc : bv 32 := 0xff45a883.
Lemma F_ce2cc : fetch_word Ubsan.M.loaded_segments (0xce484 : word) = Some W_ce2cc.
Proof. vm_refl. Qed.
Lemma D_ce2cc : decode_any W_ce2cc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2d0 : bv 32 := 0xff85a283.
Lemma F_ce2d0 : fetch_word Ubsan.M.loaded_segments (0xce488 : word) = Some W_ce2d0.
Proof. vm_refl. Qed.
Lemma D_ce2d0 : decode_any W_ce2d0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2d4 : bv 32 := 0xffc5a303.
Lemma F_ce2d4 : fetch_word Ubsan.M.loaded_segments (0xce48c : word) = Some W_ce2d4.
Proof. vm_refl. Qed.
Lemma D_ce2d4 : decode_any W_ce2d4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2d8 : bv 32 := 0x0005a703.
Lemma F_ce2d8 : fetch_word Ubsan.M.loaded_segments (0xce490 : word) = Some W_ce2d8.
Proof. vm_refl. Qed.
Lemma D_ce2d8 : decode_any W_ce2d8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2dc : bv 32 := 0x01889393.
Lemma F_ce2dc : fetch_word Ubsan.M.loaded_segments (0xce494 : word) = Some W_ce2dc.
Proof. vm_refl. Qed.
Lemma D_ce2dc : decode_any W_ce2dc = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2e0 : bv 32 := 0x0088d89b.
Lemma F_ce2e0 : fetch_word Ubsan.M.loaded_segments (0xce498 : word) = Some W_ce2e0.
Proof. vm_refl. Qed.
Lemma D_ce2e0 : decode_any W_ce2e0 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2e4 : bv 32 := 0x0103e833.
Lemma F_ce2e4 : fetch_word Ubsan.M.loaded_segments (0xce49c : word) = Some W_ce2e4.
Proof. vm_refl. Qed.
Lemma D_ce2e4 : decode_any W_ce2e4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2e8 : bv 32 := 0x01829393.
Lemma F_ce2e8 : fetch_word Ubsan.M.loaded_segments (0xce4a0 : word) = Some W_ce2e8.
Proof. vm_refl. Qed.
Lemma D_ce2e8 : decode_any W_ce2e8 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2ec : bv 32 := 0x0082d29b.
Lemma F_ce2ec : fetch_word Ubsan.M.loaded_segments (0xce4a4 : word) = Some W_ce2ec.
Proof. vm_refl. Qed.
Lemma D_ce2ec : decode_any W_ce2ec = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2f0 : bv 32 := 0x0113e8b3.
Lemma F_ce2f0 : fetch_word Ubsan.M.loaded_segments (0xce4a8 : word) = Some W_ce2f0.
Proof. vm_refl. Qed.
Lemma D_ce2f0 : decode_any W_ce2f0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2f4 : bv 32 := 0x01831393.
Lemma F_ce2f4 : fetch_word Ubsan.M.loaded_segments (0xce4ac : word) = Some W_ce2f4.
Proof. vm_refl. Qed.
Lemma D_ce2f4 : decode_any W_ce2f4 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2f8 : bv 32 := 0x0083531b.
Lemma F_ce2f8 : fetch_word Ubsan.M.loaded_segments (0xce4b0 : word) = Some W_ce2f8.
Proof. vm_refl. Qed.
Lemma D_ce2f8 : decode_any W_ce2f8 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce2fc : bv 32 := 0x0053e2b3.
Lemma F_ce2fc : fetch_word Ubsan.M.loaded_segments (0xce4b4 : word) = Some W_ce2fc.
Proof. vm_refl. Qed.
Lemma D_ce2fc : decode_any W_ce2fc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce300 : bv 32 := 0x01871393.
Lemma F_ce300 : fetch_word Ubsan.M.loaded_segments (0xce4b8 : word) = Some W_ce300.
Proof. vm_refl. Qed.
Lemma D_ce300 : decode_any W_ce300 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce304 : bv 32 := 0x0063e333.
Lemma F_ce304 : fetch_word Ubsan.M.loaded_segments (0xce4bc : word) = Some W_ce304.
Proof. vm_refl. Qed.
Lemma D_ce304 : decode_any W_ce304 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce308 : bv 32 := 0xff060613.
Lemma F_ce308 : fetch_word Ubsan.M.loaded_segments (0xce4c0 : word) = Some W_ce308.
Proof. vm_refl. Qed.
Lemma D_ce308 : decode_any W_ce308 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce30c : bv 32 := 0x0106a023.
Lemma F_ce30c : fetch_word Ubsan.M.loaded_segments (0xce4c4 : word) = Some W_ce30c.
Proof. vm_refl. Qed.
Lemma D_ce30c : decode_any W_ce30c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce310 : bv 32 := 0x0116a223.
Lemma F_ce310 : fetch_word Ubsan.M.loaded_segments (0xce4c8 : word) = Some W_ce310.
Proof. vm_refl. Qed.
Lemma D_ce310 : decode_any W_ce310 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce314 : bv 32 := 0x0056a423.
Lemma F_ce314 : fetch_word Ubsan.M.loaded_segments (0xce4cc : word) = Some W_ce314.
Proof. vm_refl. Qed.
Lemma D_ce314 : decode_any W_ce314 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce318 : bv 32 := 0x0066a623.
Lemma F_ce318 : fetch_word Ubsan.M.loaded_segments (0xce4d0 : word) = Some W_ce318.
Proof. vm_refl. Qed.
Lemma D_ce318 : decode_any W_ce318 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce31c : bv 32 := 0x01068693.
Lemma F_ce31c : fetch_word Ubsan.M.loaded_segments (0xce4d4 : word) = Some W_ce31c.
Proof. vm_refl. Qed.
Lemma D_ce31c : decode_any W_ce31c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce320 : bv 32 := 0x01058593.
Lemma F_ce320 : fetch_word Ubsan.M.loaded_segments (0xce4d8 : word) = Some W_ce320.
Proof. vm_refl. Qed.
Lemma D_ce320 : decode_any W_ce320 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce324 : bv 32 := 0xfac7e2e3.
Lemma F_ce324 : fetch_word Ubsan.M.loaded_segments (0xce4dc : word) = Some W_ce324.
Proof. vm_refl. Qed.
Lemma D_ce324 : decode_any W_ce324 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce328 : bv 32 := 0xff158593.
Lemma F_ce328 : fetch_word Ubsan.M.loaded_segments (0xce4e0 : word) = Some W_ce328.
Proof. vm_refl. Qed.
Lemma D_ce328 : decode_any W_ce328 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce32c : bv 32 := 0x01000713.
Lemma F_ce32c : fetch_word Ubsan.M.loaded_segments (0xce4e4 : word) = Some W_ce32c.
Proof. vm_refl. Qed.
Lemma D_ce32c : decode_any W_ce32c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce330 : bv 32 := 0xe4e666e3.
Lemma F_ce330 : fetch_word Ubsan.M.loaded_segments (0xce4e8 : word) = Some W_ce330.
Proof. vm_refl. Qed.
Lemma D_ce330 : decode_any W_ce330 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce334 : bv 32 := 0x0940006f.
Lemma F_ce334 : fetch_word Ubsan.M.loaded_segments (0xce4ec : word) = Some W_ce334.
Proof. vm_refl. Qed.
Lemma D_ce334 : decode_any W_ce334 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce338 : bv 32 := 0x00875793.
Lemma F_ce338 : fetch_word Ubsan.M.loaded_segments (0xce4f0 : word) = Some W_ce338.
Proof. vm_refl. Qed.
Lemma D_ce338 : decode_any W_ce338 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce33c : bv 32 := 0x01075813.
Lemma F_ce33c : fetch_word Ubsan.M.loaded_segments (0xce4f4 : word) = Some W_ce33c.
Proof. vm_refl. Qed.
Lemma D_ce33c : decode_any W_ce33c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce340 : bv 32 := 0xffd60613.
Lemma F_ce340 : fetch_word Ubsan.M.loaded_segments (0xce4f8 : word) = Some W_ce340.
Proof. vm_refl. Qed.
Lemma D_ce340 : decode_any W_ce340 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce344 : bv 32 := 0x00e68023.
Lemma F_ce344 : fetch_word Ubsan.M.loaded_segments (0xce4fc : word) = Some W_ce344.
Proof. vm_refl. Qed.
Lemma D_ce344 : decode_any W_ce344 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce348 : bv 32 := 0x00f680a3.
Lemma F_ce348 : fetch_word Ubsan.M.loaded_segments (0xce500 : word) = Some W_ce348.
Proof. vm_refl. Qed.
Lemma D_ce348 : decode_any W_ce348 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce34c : bv 32 := 0x01068123.
Lemma F_ce34c : fetch_word Ubsan.M.loaded_segments (0xce504 : word) = Some W_ce34c.
Proof. vm_refl. Qed.
Lemma D_ce34c : decode_any W_ce34c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce350 : bv 32 := 0x00368693.
Lemma F_ce350 : fetch_word Ubsan.M.loaded_segments (0xce508 : word) = Some W_ce350.
Proof. vm_refl. Qed.
Lemma D_ce350 : decode_any W_ce350 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce354 : bv 32 := 0x01058593.
Lemma F_ce354 : fetch_word Ubsan.M.loaded_segments (0xce50c : word) = Some W_ce354.
Proof. vm_refl. Qed.
Lemma D_ce354 : decode_any W_ce354 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce358 : bv 32 := 0x01000793.
Lemma F_ce358 : fetch_word Ubsan.M.loaded_segments (0xce510 : word) = Some W_ce358.
Proof. vm_refl. Qed.
Lemma D_ce358 : decode_any W_ce358 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce35c : bv 32 := 0x0187581b.
Lemma F_ce35c : fetch_word Ubsan.M.loaded_segments (0xce514 : word) = Some W_ce35c.
Proof. vm_refl. Qed.
Lemma D_ce35c : decode_any W_ce35c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce360 : bv 32 := 0xff45a883.
Lemma F_ce360 : fetch_word Ubsan.M.loaded_segments (0xce518 : word) = Some W_ce360.
Proof. vm_refl. Qed.
Lemma D_ce360 : decode_any W_ce360 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce364 : bv 32 := 0xff85a283.
Lemma F_ce364 : fetch_word Ubsan.M.loaded_segments (0xce51c : word) = Some W_ce364.
Proof. vm_refl. Qed.
Lemma D_ce364 : decode_any W_ce364 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce368 : bv 32 := 0xffc5a303.
Lemma F_ce368 : fetch_word Ubsan.M.loaded_segments (0xce520 : word) = Some W_ce368.
Proof. vm_refl. Qed.
Lemma D_ce368 : decode_any W_ce368 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce36c : bv 32 := 0x0005a703.
Lemma F_ce36c : fetch_word Ubsan.M.loaded_segments (0xce524 : word) = Some W_ce36c.
Proof. vm_refl. Qed.
Lemma D_ce36c : decode_any W_ce36c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce370 : bv 32 := 0x00889393.
Lemma F_ce370 : fetch_word Ubsan.M.loaded_segments (0xce528 : word) = Some W_ce370.
Proof. vm_refl. Qed.
Lemma D_ce370 : decode_any W_ce370 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce374 : bv 32 := 0x0188d89b.
Lemma F_ce374 : fetch_word Ubsan.M.loaded_segments (0xce52c : word) = Some W_ce374.
Proof. vm_refl. Qed.
Lemma D_ce374 : decode_any W_ce374 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce378 : bv 32 := 0x0103e833.
Lemma F_ce378 : fetch_word Ubsan.M.loaded_segments (0xce530 : word) = Some W_ce378.
Proof. vm_refl. Qed.
Lemma D_ce378 : decode_any W_ce378 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce37c : bv 32 := 0x00829393.
Lemma F_ce37c : fetch_word Ubsan.M.loaded_segments (0xce534 : word) = Some W_ce37c.
Proof. vm_refl. Qed.
Lemma D_ce37c : decode_any W_ce37c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce380 : bv 32 := 0x0182d29b.
Lemma F_ce380 : fetch_word Ubsan.M.loaded_segments (0xce538 : word) = Some W_ce380.
Proof. vm_refl. Qed.
Lemma D_ce380 : decode_any W_ce380 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce384 : bv 32 := 0x0113e8b3.
Lemma F_ce384 : fetch_word Ubsan.M.loaded_segments (0xce53c : word) = Some W_ce384.
Proof. vm_refl. Qed.
Lemma D_ce384 : decode_any W_ce384 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce388 : bv 32 := 0x00831393.
Lemma F_ce388 : fetch_word Ubsan.M.loaded_segments (0xce540 : word) = Some W_ce388.
Proof. vm_refl. Qed.
Lemma D_ce388 : decode_any W_ce388 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce38c : bv 32 := 0x0183531b.
Lemma F_ce38c : fetch_word Ubsan.M.loaded_segments (0xce544 : word) = Some W_ce38c.
Proof. vm_refl. Qed.
Lemma D_ce38c : decode_any W_ce38c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce390 : bv 32 := 0x0053e2b3.
Lemma F_ce390 : fetch_word Ubsan.M.loaded_segments (0xce548 : word) = Some W_ce390.
Proof. vm_refl. Qed.
Lemma D_ce390 : decode_any W_ce390 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce394 : bv 32 := 0x00871393.
Lemma F_ce394 : fetch_word Ubsan.M.loaded_segments (0xce54c : word) = Some W_ce394.
Proof. vm_refl. Qed.
Lemma D_ce394 : decode_any W_ce394 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce398 : bv 32 := 0x0063e333.
Lemma F_ce398 : fetch_word Ubsan.M.loaded_segments (0xce550 : word) = Some W_ce398.
Proof. vm_refl. Qed.
Lemma D_ce398 : decode_any W_ce398 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce39c : bv 32 := 0xff060613.
Lemma F_ce39c : fetch_word Ubsan.M.loaded_segments (0xce554 : word) = Some W_ce39c.
Proof. vm_refl. Qed.
Lemma D_ce39c : decode_any W_ce39c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3a0 : bv 32 := 0x0106a023.
Lemma F_ce3a0 : fetch_word Ubsan.M.loaded_segments (0xce558 : word) = Some W_ce3a0.
Proof. vm_refl. Qed.
Lemma D_ce3a0 : decode_any W_ce3a0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3a4 : bv 32 := 0x0116a223.
Lemma F_ce3a4 : fetch_word Ubsan.M.loaded_segments (0xce55c : word) = Some W_ce3a4.
Proof. vm_refl. Qed.
Lemma D_ce3a4 : decode_any W_ce3a4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3a8 : bv 32 := 0x0056a423.
Lemma F_ce3a8 : fetch_word Ubsan.M.loaded_segments (0xce560 : word) = Some W_ce3a8.
Proof. vm_refl. Qed.
Lemma D_ce3a8 : decode_any W_ce3a8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3ac : bv 32 := 0x0066a623.
Lemma F_ce3ac : fetch_word Ubsan.M.loaded_segments (0xce564 : word) = Some W_ce3ac.
Proof. vm_refl. Qed.
Lemma D_ce3ac : decode_any W_ce3ac = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3b0 : bv 32 := 0x01068693.
Lemma F_ce3b0 : fetch_word Ubsan.M.loaded_segments (0xce568 : word) = Some W_ce3b0.
Proof. vm_refl. Qed.
Lemma D_ce3b0 : decode_any W_ce3b0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3b4 : bv 32 := 0x01058593.
Lemma F_ce3b4 : fetch_word Ubsan.M.loaded_segments (0xce56c : word) = Some W_ce3b4.
Proof. vm_refl. Qed.
Lemma D_ce3b4 : decode_any W_ce3b4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3b8 : bv 32 := 0xfac7e2e3.
Lemma F_ce3b8 : fetch_word Ubsan.M.loaded_segments (0xce570 : word) = Some W_ce3b8.
Proof. vm_refl. Qed.
Lemma D_ce3b8 : decode_any W_ce3b8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3bc : bv 32 := 0xff358593.
Lemma F_ce3bc : fetch_word Ubsan.M.loaded_segments (0xce574 : word) = Some W_ce3bc.
Proof. vm_refl. Qed.
Lemma D_ce3bc : decode_any W_ce3bc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3c0 : bv 32 := 0x01000713.
Lemma F_ce3c0 : fetch_word Ubsan.M.loaded_segments (0xce578 : word) = Some W_ce3c0.
Proof. vm_refl. Qed.
Lemma D_ce3c0 : decode_any W_ce3c0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3c4 : bv 32 := 0xdae66ce3.
Lemma F_ce3c4 : fetch_word Ubsan.M.loaded_segments (0xce57c : word) = Some W_ce3c4.
Proof. vm_refl. Qed.
Lemma D_ce3c4 : decode_any W_ce3c4 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3c8 : bv 32 := 0x0005c703.
Lemma F_ce3c8 : fetch_word Ubsan.M.loaded_segments (0xce580 : word) = Some W_ce3c8.
Proof. vm_refl. Qed.
Lemma D_ce3c8 : decode_any W_ce3c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3cc : bv 32 := 0x0015c783.
Lemma F_ce3cc : fetch_word Ubsan.M.loaded_segments (0xce584 : word) = Some W_ce3cc.
Proof. vm_refl. Qed.
Lemma D_ce3cc : decode_any W_ce3cc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3d0 : bv 32 := 0x0025c803.
Lemma F_ce3d0 : fetch_word Ubsan.M.loaded_segments (0xce588 : word) = Some W_ce3d0.
Proof. vm_refl. Qed.
Lemma D_ce3d0 : decode_any W_ce3d0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3d4 : bv 32 := 0x0035c883.
Lemma F_ce3d4 : fetch_word Ubsan.M.loaded_segments (0xce58c : word) = Some W_ce3d4.
Proof. vm_refl. Qed.
Lemma D_ce3d4 : decode_any W_ce3d4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3d8 : bv 32 := 0x0045c283.
Lemma F_ce3d8 : fetch_word Ubsan.M.loaded_segments (0xce590 : word) = Some W_ce3d8.
Proof. vm_refl. Qed.
Lemma D_ce3d8 : decode_any W_ce3d8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3dc : bv 32 := 0x0055c303.
Lemma F_ce3dc : fetch_word Ubsan.M.loaded_segments (0xce594 : word) = Some W_ce3dc.
Proof. vm_refl. Qed.
Lemma D_ce3dc : decode_any W_ce3dc = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3e0 : bv 32 := 0x0065c383.
Lemma F_ce3e0 : fetch_word Ubsan.M.loaded_segments (0xce598 : word) = Some W_ce3e0.
Proof. vm_refl. Qed.
Lemma D_ce3e0 : decode_any W_ce3e0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3e4 : bv 32 := 0x0075ce03.
Lemma F_ce3e4 : fetch_word Ubsan.M.loaded_segments (0xce59c : word) = Some W_ce3e4.
Proof. vm_refl. Qed.
Lemma D_ce3e4 : decode_any W_ce3e4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3e8 : bv 32 := 0x00e68023.
Lemma F_ce3e8 : fetch_word Ubsan.M.loaded_segments (0xce5a0 : word) = Some W_ce3e8.
Proof. vm_refl. Qed.
Lemma D_ce3e8 : decode_any W_ce3e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3ec : bv 32 := 0x00f680a3.
Lemma F_ce3ec : fetch_word Ubsan.M.loaded_segments (0xce5a4 : word) = Some W_ce3ec.
Proof. vm_refl. Qed.
Lemma D_ce3ec : decode_any W_ce3ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3f0 : bv 32 := 0x01068123.
Lemma F_ce3f0 : fetch_word Ubsan.M.loaded_segments (0xce5a8 : word) = Some W_ce3f0.
Proof. vm_refl. Qed.
Lemma D_ce3f0 : decode_any W_ce3f0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3f4 : bv 32 := 0x011681a3.
Lemma F_ce3f4 : fetch_word Ubsan.M.loaded_segments (0xce5ac : word) = Some W_ce3f4.
Proof. vm_refl. Qed.
Lemma D_ce3f4 : decode_any W_ce3f4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3f8 : bv 32 := 0x0085c703.
Lemma F_ce3f8 : fetch_word Ubsan.M.loaded_segments (0xce5b0 : word) = Some W_ce3f8.
Proof. vm_refl. Qed.
Lemma D_ce3f8 : decode_any W_ce3f8 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce3fc : bv 32 := 0x0095c783.
Lemma F_ce3fc : fetch_word Ubsan.M.loaded_segments (0xce5b4 : word) = Some W_ce3fc.
Proof. vm_refl. Qed.
Lemma D_ce3fc : decode_any W_ce3fc = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce400 : bv 32 := 0x00a5c803.
Lemma F_ce400 : fetch_word Ubsan.M.loaded_segments (0xce5b8 : word) = Some W_ce400.
Proof. vm_refl. Qed.
Lemma D_ce400 : decode_any W_ce400 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce404 : bv 32 := 0x00b5c883.
Lemma F_ce404 : fetch_word Ubsan.M.loaded_segments (0xce5bc : word) = Some W_ce404.
Proof. vm_refl. Qed.
Lemma D_ce404 : decode_any W_ce404 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce408 : bv 32 := 0x00568223.
Lemma F_ce408 : fetch_word Ubsan.M.loaded_segments (0xce5c0 : word) = Some W_ce408.
Proof. vm_refl. Qed.
Lemma D_ce408 : decode_any W_ce408 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce40c : bv 32 := 0x006682a3.
Lemma F_ce40c : fetch_word Ubsan.M.loaded_segments (0xce5c4 : word) = Some W_ce40c.
Proof. vm_refl. Qed.
Lemma D_ce40c : decode_any W_ce40c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce410 : bv 32 := 0x00768323.
Lemma F_ce410 : fetch_word Ubsan.M.loaded_segments (0xce5c8 : word) = Some W_ce410.
Proof. vm_refl. Qed.
Lemma D_ce410 : decode_any W_ce410 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce414 : bv 32 := 0x01c683a3.
Lemma F_ce414 : fetch_word Ubsan.M.loaded_segments (0xce5cc : word) = Some W_ce414.
Proof. vm_refl. Qed.
Lemma D_ce414 : decode_any W_ce414 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce418 : bv 32 := 0x00c5c283.
Lemma F_ce418 : fetch_word Ubsan.M.loaded_segments (0xce5d0 : word) = Some W_ce418.
Proof. vm_refl. Qed.
Lemma D_ce418 : decode_any W_ce418 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce41c : bv 32 := 0x00d5c303.
Lemma F_ce41c : fetch_word Ubsan.M.loaded_segments (0xce5d4 : word) = Some W_ce41c.
Proof. vm_refl. Qed.
Lemma D_ce41c : decode_any W_ce41c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce420 : bv 32 := 0x00e5c383.
Lemma F_ce420 : fetch_word Ubsan.M.loaded_segments (0xce5d8 : word) = Some W_ce420.
Proof. vm_refl. Qed.
Lemma D_ce420 : decode_any W_ce420 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce424 : bv 32 := 0x00f5ce03.
Lemma F_ce424 : fetch_word Ubsan.M.loaded_segments (0xce5dc : word) = Some W_ce424.
Proof. vm_refl. Qed.
Lemma D_ce424 : decode_any W_ce424 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce428 : bv 32 := 0x01058593.
Lemma F_ce428 : fetch_word Ubsan.M.loaded_segments (0xce5e0 : word) = Some W_ce428.
Proof. vm_refl. Qed.
Lemma D_ce428 : decode_any W_ce428 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce42c : bv 32 := 0x00e68423.
Lemma F_ce42c : fetch_word Ubsan.M.loaded_segments (0xce5e4 : word) = Some W_ce42c.
Proof. vm_refl. Qed.
Lemma D_ce42c : decode_any W_ce42c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce430 : bv 32 := 0x00f684a3.
Lemma F_ce430 : fetch_word Ubsan.M.loaded_segments (0xce5e8 : word) = Some W_ce430.
Proof. vm_refl. Qed.
Lemma D_ce430 : decode_any W_ce430 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce434 : bv 32 := 0x01068523.
Lemma F_ce434 : fetch_word Ubsan.M.loaded_segments (0xce5ec : word) = Some W_ce434.
Proof. vm_refl. Qed.
Lemma D_ce434 : decode_any W_ce434 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce438 : bv 32 := 0x011685a3.
Lemma F_ce438 : fetch_word Ubsan.M.loaded_segments (0xce5f0 : word) = Some W_ce438.
Proof. vm_refl. Qed.
Lemma D_ce438 : decode_any W_ce438 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce43c : bv 32 := 0x01068713.
Lemma F_ce43c : fetch_word Ubsan.M.loaded_segments (0xce5f4 : word) = Some W_ce43c.
Proof. vm_refl. Qed.
Lemma D_ce43c : decode_any W_ce43c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce440 : bv 32 := 0x00568623.
Lemma F_ce440 : fetch_word Ubsan.M.loaded_segments (0xce5f8 : word) = Some W_ce440.
Proof. vm_refl. Qed.
Lemma D_ce440 : decode_any W_ce440 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce444 : bv 32 := 0x006686a3.
Lemma F_ce444 : fetch_word Ubsan.M.loaded_segments (0xce5fc : word) = Some W_ce444.
Proof. vm_refl. Qed.
Lemma D_ce444 : decode_any W_ce444 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce448 : bv 32 := 0x00768723.
Lemma F_ce448 : fetch_word Ubsan.M.loaded_segments (0xce600 : word) = Some W_ce448.
Proof. vm_refl. Qed.
Lemma D_ce448 : decode_any W_ce448 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce44c : bv 32 := 0x01c687a3.
Lemma F_ce44c : fetch_word Ubsan.M.loaded_segments (0xce604 : word) = Some W_ce44c.
Proof. vm_refl. Qed.
Lemma D_ce44c : decode_any W_ce44c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce450 : bv 32 := 0x00070693.
Lemma F_ce450 : fetch_word Ubsan.M.loaded_segments (0xce608 : word) = Some W_ce450.
Proof. vm_refl. Qed.
Lemma D_ce450 : decode_any W_ce450 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce454 : bv 32 := 0x00867713.
Lemma F_ce454 : fetch_word Ubsan.M.loaded_segments (0xce60c : word) = Some W_ce454.
Proof. vm_refl. Qed.
Lemma D_ce454 : decode_any W_ce454 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce458 : bv 32 := 0xd20706e3.
Lemma F_ce458 : fetch_word Ubsan.M.loaded_segments (0xce610 : word) = Some W_ce458.
Proof. vm_refl. Qed.
Lemma D_ce458 : decode_any W_ce458 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce45c : bv 32 := 0x0005c703.
Lemma F_ce45c : fetch_word Ubsan.M.loaded_segments (0xce614 : word) = Some W_ce45c.
Proof. vm_refl. Qed.
Lemma D_ce45c : decode_any W_ce45c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce460 : bv 32 := 0x0015c783.
Lemma F_ce460 : fetch_word Ubsan.M.loaded_segments (0xce618 : word) = Some W_ce460.
Proof. vm_refl. Qed.
Lemma D_ce460 : decode_any W_ce460 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce464 : bv 32 := 0x0025c803.
Lemma F_ce464 : fetch_word Ubsan.M.loaded_segments (0xce61c : word) = Some W_ce464.
Proof. vm_refl. Qed.
Lemma D_ce464 : decode_any W_ce464 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce468 : bv 32 := 0x0035c883.
Lemma F_ce468 : fetch_word Ubsan.M.loaded_segments (0xce620 : word) = Some W_ce468.
Proof. vm_refl. Qed.
Lemma D_ce468 : decode_any W_ce468 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce46c : bv 32 := 0x0045c283.
Lemma F_ce46c : fetch_word Ubsan.M.loaded_segments (0xce624 : word) = Some W_ce46c.
Proof. vm_refl. Qed.
Lemma D_ce46c : decode_any W_ce46c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce470 : bv 32 := 0x0055c303.
Lemma F_ce470 : fetch_word Ubsan.M.loaded_segments (0xce628 : word) = Some W_ce470.
Proof. vm_refl. Qed.
Lemma D_ce470 : decode_any W_ce470 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce474 : bv 32 := 0x0065c383.
Lemma F_ce474 : fetch_word Ubsan.M.loaded_segments (0xce62c : word) = Some W_ce474.
Proof. vm_refl. Qed.
Lemma D_ce474 : decode_any W_ce474 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce478 : bv 32 := 0x0075ce03.
Lemma F_ce478 : fetch_word Ubsan.M.loaded_segments (0xce630 : word) = Some W_ce478.
Proof. vm_refl. Qed.
Lemma D_ce478 : decode_any W_ce478 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce47c : bv 32 := 0x00858593.
Lemma F_ce47c : fetch_word Ubsan.M.loaded_segments (0xce634 : word) = Some W_ce47c.
Proof. vm_refl. Qed.
Lemma D_ce47c : decode_any W_ce47c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce480 : bv 32 := 0x00e68023.
Lemma F_ce480 : fetch_word Ubsan.M.loaded_segments (0xce638 : word) = Some W_ce480.
Proof. vm_refl. Qed.
Lemma D_ce480 : decode_any W_ce480 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce484 : bv 32 := 0x00f680a3.
Lemma F_ce484 : fetch_word Ubsan.M.loaded_segments (0xce63c : word) = Some W_ce484.
Proof. vm_refl. Qed.
Lemma D_ce484 : decode_any W_ce484 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce488 : bv 32 := 0x01068123.
Lemma F_ce488 : fetch_word Ubsan.M.loaded_segments (0xce640 : word) = Some W_ce488.
Proof. vm_refl. Qed.
Lemma D_ce488 : decode_any W_ce488 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce48c : bv 32 := 0x011681a3.
Lemma F_ce48c : fetch_word Ubsan.M.loaded_segments (0xce644 : word) = Some W_ce48c.
Proof. vm_refl. Qed.
Lemma D_ce48c : decode_any W_ce48c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce490 : bv 32 := 0x00868713.
Lemma F_ce490 : fetch_word Ubsan.M.loaded_segments (0xce648 : word) = Some W_ce490.
Proof. vm_refl. Qed.
Lemma D_ce490 : decode_any W_ce490 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce494 : bv 32 := 0x00568223.
Lemma F_ce494 : fetch_word Ubsan.M.loaded_segments (0xce64c : word) = Some W_ce494.
Proof. vm_refl. Qed.
Lemma D_ce494 : decode_any W_ce494 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce498 : bv 32 := 0x006682a3.
Lemma F_ce498 : fetch_word Ubsan.M.loaded_segments (0xce650 : word) = Some W_ce498.
Proof. vm_refl. Qed.
Lemma D_ce498 : decode_any W_ce498 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce49c : bv 32 := 0x00768323.
Lemma F_ce49c : fetch_word Ubsan.M.loaded_segments (0xce654 : word) = Some W_ce49c.
Proof. vm_refl. Qed.
Lemma D_ce49c : decode_any W_ce49c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4a0 : bv 32 := 0x01c683a3.
Lemma F_ce4a0 : fetch_word Ubsan.M.loaded_segments (0xce658 : word) = Some W_ce4a0.
Proof. vm_refl. Qed.
Lemma D_ce4a0 : decode_any W_ce4a0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4a4 : bv 32 := 0x00070693.
Lemma F_ce4a4 : fetch_word Ubsan.M.loaded_segments (0xce65c : word) = Some W_ce4a4.
Proof. vm_refl. Qed.
Lemma D_ce4a4 : decode_any W_ce4a4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4a8 : bv 32 := 0x00467713.
Lemma F_ce4a8 : fetch_word Ubsan.M.loaded_segments (0xce660 : word) = Some W_ce4a8.
Proof. vm_refl. Qed.
Lemma D_ce4a8 : decode_any W_ce4a8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4ac : bv 32 := 0x02070863.
Lemma F_ce4ac : fetch_word Ubsan.M.loaded_segments (0xce664 : word) = Some W_ce4ac.
Proof. vm_refl. Qed.
Lemma D_ce4ac : decode_any W_ce4ac = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4b0 : bv 32 := 0x0005c703.
Lemma F_ce4b0 : fetch_word Ubsan.M.loaded_segments (0xce668 : word) = Some W_ce4b0.
Proof. vm_refl. Qed.
Lemma D_ce4b0 : decode_any W_ce4b0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4b4 : bv 32 := 0x0015c783.
Lemma F_ce4b4 : fetch_word Ubsan.M.loaded_segments (0xce66c : word) = Some W_ce4b4.
Proof. vm_refl. Qed.
Lemma D_ce4b4 : decode_any W_ce4b4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4b8 : bv 32 := 0x0025c803.
Lemma F_ce4b8 : fetch_word Ubsan.M.loaded_segments (0xce670 : word) = Some W_ce4b8.
Proof. vm_refl. Qed.
Lemma D_ce4b8 : decode_any W_ce4b8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4bc : bv 32 := 0x0035c883.
Lemma F_ce4bc : fetch_word Ubsan.M.loaded_segments (0xce674 : word) = Some W_ce4bc.
Proof. vm_refl. Qed.
Lemma D_ce4bc : decode_any W_ce4bc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4c0 : bv 32 := 0x00458593.
Lemma F_ce4c0 : fetch_word Ubsan.M.loaded_segments (0xce678 : word) = Some W_ce4c0.
Proof. vm_refl. Qed.
Lemma D_ce4c0 : decode_any W_ce4c0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4c4 : bv 32 := 0x00468293.
Lemma F_ce4c4 : fetch_word Ubsan.M.loaded_segments (0xce67c : word) = Some W_ce4c4.
Proof. vm_refl. Qed.
Lemma D_ce4c4 : decode_any W_ce4c4 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4c8 : bv 32 := 0x00e68023.
Lemma F_ce4c8 : fetch_word Ubsan.M.loaded_segments (0xce680 : word) = Some W_ce4c8.
Proof. vm_refl. Qed.
Lemma D_ce4c8 : decode_any W_ce4c8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4cc : bv 32 := 0x00f680a3.
Lemma F_ce4cc : fetch_word Ubsan.M.loaded_segments (0xce684 : word) = Some W_ce4cc.
Proof. vm_refl. Qed.
Lemma D_ce4cc : decode_any W_ce4cc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4d0 : bv 32 := 0x01068123.
Lemma F_ce4d0 : fetch_word Ubsan.M.loaded_segments (0xce688 : word) = Some W_ce4d0.
Proof. vm_refl. Qed.
Lemma D_ce4d0 : decode_any W_ce4d0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4d4 : bv 32 := 0x011681a3.
Lemma F_ce4d4 : fetch_word Ubsan.M.loaded_segments (0xce68c : word) = Some W_ce4d4.
Proof. vm_refl. Qed.
Lemma D_ce4d4 : decode_any W_ce4d4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4d8 : bv 32 := 0x00028693.
Lemma F_ce4d8 : fetch_word Ubsan.M.loaded_segments (0xce690 : word) = Some W_ce4d8.
Proof. vm_refl. Qed.
Lemma D_ce4d8 : decode_any W_ce4d8 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4dc : bv 32 := 0x00267713.
Lemma F_ce4dc : fetch_word Ubsan.M.loaded_segments (0xce694 : word) = Some W_ce4dc.
Proof. vm_refl. Qed.
Lemma D_ce4dc : decode_any W_ce4dc = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4e0 : bv 32 := 0x00071863.
Lemma F_ce4e0 : fetch_word Ubsan.M.loaded_segments (0xce698 : word) = Some W_ce4e0.
Proof. vm_refl. Qed.
Lemma D_ce4e0 : decode_any W_ce4e0 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4e4 : bv 32 := 0x00167613.
Lemma F_ce4e4 : fetch_word Ubsan.M.loaded_segments (0xce69c : word) = Some W_ce4e4.
Proof. vm_refl. Qed.
Lemma D_ce4e4 : decode_any W_ce4e4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4e8 : bv 32 := 0x02061663.
Lemma F_ce4e8 : fetch_word Ubsan.M.loaded_segments (0xce6a0 : word) = Some W_ce4e8.
Proof. vm_refl. Qed.
Lemma D_ce4e8 : decode_any W_ce4e8 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4ec : bv 32 := 0x00008067.
Lemma F_ce4ec : fetch_word Ubsan.M.loaded_segments (0xce6a4 : word) = Some W_ce4ec.
Proof. vm_refl. Qed.
Lemma D_ce4ec : decode_any W_ce4ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4f0 : bv 32 := 0x0005c703.
Lemma F_ce4f0 : fetch_word Ubsan.M.loaded_segments (0xce6a8 : word) = Some W_ce4f0.
Proof. vm_refl. Qed.
Lemma D_ce4f0 : decode_any W_ce4f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4f4 : bv 32 := 0x0015c783.
Lemma F_ce4f4 : fetch_word Ubsan.M.loaded_segments (0xce6ac : word) = Some W_ce4f4.
Proof. vm_refl. Qed.
Lemma D_ce4f4 : decode_any W_ce4f4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4f8 : bv 32 := 0x00258593.
Lemma F_ce4f8 : fetch_word Ubsan.M.loaded_segments (0xce6b0 : word) = Some W_ce4f8.
Proof. vm_refl. Qed.
Lemma D_ce4f8 : decode_any W_ce4f8 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce4fc : bv 32 := 0x00268813.
Lemma F_ce4fc : fetch_word Ubsan.M.loaded_segments (0xce6b4 : word) = Some W_ce4fc.
Proof. vm_refl. Qed.
Lemma D_ce4fc : decode_any W_ce4fc = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce500 : bv 32 := 0x00e68023.
Lemma F_ce500 : fetch_word Ubsan.M.loaded_segments (0xce6b8 : word) = Some W_ce500.
Proof. vm_refl. Qed.
Lemma D_ce500 : decode_any W_ce500 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce504 : bv 32 := 0x00f680a3.
Lemma F_ce504 : fetch_word Ubsan.M.loaded_segments (0xce6bc : word) = Some W_ce504.
Proof. vm_refl. Qed.
Lemma D_ce504 : decode_any W_ce504 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce508 : bv 32 := 0x00080693.
Lemma F_ce508 : fetch_word Ubsan.M.loaded_segments (0xce6c0 : word) = Some W_ce508.
Proof. vm_refl. Qed.
Lemma D_ce508 : decode_any W_ce508 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce50c : bv 32 := 0x00167613.
Lemma F_ce50c : fetch_word Ubsan.M.loaded_segments (0xce6c4 : word) = Some W_ce50c.
Proof. vm_refl. Qed.
Lemma D_ce50c : decode_any W_ce50c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce510 : bv 32 := 0xfc060ee3.
Lemma F_ce510 : fetch_word Ubsan.M.loaded_segments (0xce6c8 : word) = Some W_ce510.
Proof. vm_refl. Qed.
Lemma D_ce510 : decode_any W_ce510 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce514 : bv 32 := 0x0005c583.
Lemma F_ce514 : fetch_word Ubsan.M.loaded_segments (0xce6cc : word) = Some W_ce514.
Proof. vm_refl. Qed.
Lemma D_ce514 : decode_any W_ce514 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce518 : bv 32 := 0x00b68023.
Lemma F_ce518 : fetch_word Ubsan.M.loaded_segments (0xce6d0 : word) = Some W_ce518.
Proof. vm_refl. Qed.
Lemma D_ce518 : decode_any W_ce518 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce51c : bv 32 := 0x00008067.
Lemma F_ce51c : fetch_word Ubsan.M.loaded_segments (0xce6d4 : word) = Some W_ce51c.
Proof. vm_refl. Qed.
Lemma D_ce51c : decode_any W_ce51c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce520 : bv 32 := 0x08b50663.
Lemma F_ce520 : fetch_word Ubsan.M.loaded_segments (0xce6d8 : word) = Some W_ce520.
Proof. vm_refl. Qed.
Lemma D_ce520 : decode_any W_ce520 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.
