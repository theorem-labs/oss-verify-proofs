(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9b1f0 : bv 32 := 0x0035f693.
Lemma F_9b1f0 : fetch_word Asan.M.loaded_segments (0x9b1f0 : word) = Some W_9b1f0.
Proof. vm_refl. Qed.
Lemma D_9b1f0 : decode_any W_9b1f0 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1f4 : bv 32 := 0x10068863.
Lemma F_9b1f4 : fetch_word Asan.M.loaded_segments (0x9b1f4 : word) = Some W_9b1f4.
Proof. vm_refl. Qed.
Lemma D_9b1f4 : decode_any W_9b1f4 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1f8 : bv 32 := 0x02060e63.
Lemma F_9b1f8 : fetch_word Asan.M.loaded_segments (0x9b1f8 : word) = Some W_9b1f8.
Proof. vm_refl. Qed.
Lemma D_9b1f8 : decode_any W_9b1f8 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1fc : bv 32 := 0x00158713.
Lemma F_9b1fc : fetch_word Asan.M.loaded_segments (0x9b1fc : word) = Some W_9b1fc.
Proof. vm_refl. Qed.
Lemma D_9b1fc : decode_any W_9b1fc = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b200 : bv 32 := 0x00100793.
Lemma F_9b200 : fetch_word Asan.M.loaded_segments (0x9b200 : word) = Some W_9b200.
Proof. vm_refl. Qed.
Lemma D_9b200 : decode_any W_9b200 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b204 : bv 32 := 0x00050693.
Lemma F_9b204 : fetch_word Asan.M.loaded_segments (0x9b204 : word) = Some W_9b204.
Proof. vm_refl. Qed.
Lemma D_9b204 : decode_any W_9b204 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b208 : bv 32 := 0x0005c883.
Lemma F_9b208 : fetch_word Asan.M.loaded_segments (0x9b208 : word) = Some W_9b208.
Proof. vm_refl. Qed.
Lemma D_9b208 : decode_any W_9b208 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b20c : bv 32 := 0x00060813.
Lemma F_9b20c : fetch_word Asan.M.loaded_segments (0x9b20c : word) = Some W_9b20c.
Proof. vm_refl. Qed.
Lemma D_9b20c : decode_any W_9b20c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b210 : bv 32 := 0x00158593.
Lemma F_9b210 : fetch_word Asan.M.loaded_segments (0x9b210 : word) = Some W_9b210.
Proof. vm_refl. Qed.
Lemma D_9b210 : decode_any W_9b210 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b214 : bv 32 := 0x00377293.
Lemma F_9b214 : fetch_word Asan.M.loaded_segments (0x9b214 : word) = Some W_9b214.
Proof. vm_refl. Qed.
Lemma D_9b214 : decode_any W_9b214 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b218 : bv 32 := 0x01168023.
Lemma F_9b218 : fetch_word Asan.M.loaded_segments (0x9b218 : word) = Some W_9b218.
Proof. vm_refl. Qed.
Lemma D_9b218 : decode_any W_9b218 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b21c : bv 32 := 0x00168693.
Lemma F_9b21c : fetch_word Asan.M.loaded_segments (0x9b21c : word) = Some W_9b21c.
Proof. vm_refl. Qed.
Lemma D_9b21c : decode_any W_9b21c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b220 : bv 32 := 0xfff60613.
Lemma F_9b220 : fetch_word Asan.M.loaded_segments (0x9b220 : word) = Some W_9b220.
Proof. vm_refl. Qed.
Lemma D_9b220 : decode_any W_9b220 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b224 : bv 32 := 0x00028a63.
Lemma F_9b224 : fetch_word Asan.M.loaded_segments (0x9b224 : word) = Some W_9b224.
Proof. vm_refl. Qed.
Lemma D_9b224 : decode_any W_9b224 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b228 : bv 32 := 0x00170713.
Lemma F_9b228 : fetch_word Asan.M.loaded_segments (0x9b228 : word) = Some W_9b228.
Proof. vm_refl. Qed.
Lemma D_9b228 : decode_any W_9b228 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b22c : bv 32 := 0xfcf81ee3.
Lemma F_9b22c : fetch_word Asan.M.loaded_segments (0x9b22c : word) = Some W_9b22c.
Proof. vm_refl. Qed.
Lemma D_9b22c : decode_any W_9b22c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b230 : bv 32 := 0x0080006f.
Lemma F_9b230 : fetch_word Asan.M.loaded_segments (0x9b230 : word) = Some W_9b230.
Proof. vm_refl. Qed.
Lemma D_9b230 : decode_any W_9b230 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b234 : bv 32 := 0x00050693.
Lemma F_9b234 : fetch_word Asan.M.loaded_segments (0x9b234 : word) = Some W_9b234.
Proof. vm_refl. Qed.
Lemma D_9b234 : decode_any W_9b234 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b238 : bv 32 := 0x0036f793.
Lemma F_9b238 : fetch_word Asan.M.loaded_segments (0x9b238 : word) = Some W_9b238.
Proof. vm_refl. Qed.
Lemma D_9b238 : decode_any W_9b238 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b23c : bv 32 := 0x0c078a63.
Lemma F_9b23c : fetch_word Asan.M.loaded_segments (0x9b23c : word) = Some W_9b23c.
Proof. vm_refl. Qed.
Lemma D_9b23c : decode_any W_9b23c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b240 : bv 32 := 0x02000713.
Lemma F_9b240 : fetch_word Asan.M.loaded_segments (0x9b240 : word) = Some W_9b240.
Proof. vm_refl. Qed.
Lemma D_9b240 : decode_any W_9b240 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b244 : bv 32 := 0x02e67063.
Lemma F_9b244 : fetch_word Asan.M.loaded_segments (0x9b244 : word) = Some W_9b244.
Proof. vm_refl. Qed.
Lemma D_9b244 : decode_any W_9b244 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b248 : bv 32 := 0x01000713.
Lemma F_9b248 : fetch_word Asan.M.loaded_segments (0x9b248 : word) = Some W_9b248.
Proof. vm_refl. Qed.
Lemma D_9b248 : decode_any W_9b248 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b24c : bv 32 := 0x24e67863.
Lemma F_9b24c : fetch_word Asan.M.loaded_segments (0x9b24c : word) = Some W_9b24c.
Proof. vm_refl. Qed.
Lemma D_9b24c : decode_any W_9b24c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b250 : bv 32 := 0x00867713.
Lemma F_9b250 : fetch_word Asan.M.loaded_segments (0x9b250 : word) = Some W_9b250.
Proof. vm_refl. Qed.
Lemma D_9b250 : decode_any W_9b250 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b254 : bv 32 := 0x2c071e63.
Lemma F_9b254 : fetch_word Asan.M.loaded_segments (0x9b254 : word) = Some W_9b254.
Proof. vm_refl. Qed.
Lemma D_9b254 : decode_any W_9b254 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b258 : bv 32 := 0x00467713.
Lemma F_9b258 : fetch_word Asan.M.loaded_segments (0x9b258 : word) = Some W_9b258.
Proof. vm_refl. Qed.
Lemma D_9b258 : decode_any W_9b258 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b25c : bv 32 := 0x32071463.
Lemma F_9b25c : fetch_word Asan.M.loaded_segments (0x9b25c : word) = Some W_9b25c.
Proof. vm_refl. Qed.
Lemma D_9b25c : decode_any W_9b25c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b260 : bv 32 := 0x3500006f.
Lemma F_9b260 : fetch_word Asan.M.loaded_segments (0x9b260 : word) = Some W_9b260.
Proof. vm_refl. Qed.
Lemma D_9b260 : decode_any W_9b260 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b264 : bv 32 := 0x0005a703.
Lemma F_9b264 : fetch_word Asan.M.loaded_segments (0x9b264 : word) = Some W_9b264.
Proof. vm_refl. Qed.
Lemma D_9b264 : decode_any W_9b264 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b268 : bv 32 := 0x00300813.
Lemma F_9b268 : fetch_word Asan.M.loaded_segments (0x9b268 : word) = Some W_9b268.
Proof. vm_refl. Qed.
Lemma D_9b268 : decode_any W_9b268 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b26c : bv 32 := 0x11078e63.
Lemma F_9b26c : fetch_word Asan.M.loaded_segments (0x9b26c : word) = Some W_9b26c.
Proof. vm_refl. Qed.
Lemma D_9b26c : decode_any W_9b26c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b270 : bv 32 := 0x00200813.
Lemma F_9b270 : fetch_word Asan.M.loaded_segments (0x9b270 : word) = Some W_9b270.
Proof. vm_refl. Qed.
Lemma D_9b270 : decode_any W_9b270 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b274 : bv 32 := 0x19079c63.
Lemma F_9b274 : fetch_word Asan.M.loaded_segments (0x9b274 : word) = Some W_9b274.
Proof. vm_refl. Qed.
Lemma D_9b274 : decode_any W_9b274 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b278 : bv 32 := 0x00875793.
Lemma F_9b278 : fetch_word Asan.M.loaded_segments (0x9b278 : word) = Some W_9b278.
Proof. vm_refl. Qed.
Lemma D_9b278 : decode_any W_9b278 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b27c : bv 32 := 0xffe60613.
Lemma F_9b27c : fetch_word Asan.M.loaded_segments (0x9b27c : word) = Some W_9b27c.
Proof. vm_refl. Qed.
Lemma D_9b27c : decode_any W_9b27c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b280 : bv 32 := 0x00e68023.
Lemma F_9b280 : fetch_word Asan.M.loaded_segments (0x9b280 : word) = Some W_9b280.
Proof. vm_refl. Qed.
Lemma D_9b280 : decode_any W_9b280 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b284 : bv 32 := 0x00f680a3.
Lemma F_9b284 : fetch_word Asan.M.loaded_segments (0x9b284 : word) = Some W_9b284.
Proof. vm_refl. Qed.
Lemma D_9b284 : decode_any W_9b284 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b288 : bv 32 := 0x00268693.
Lemma F_9b288 : fetch_word Asan.M.loaded_segments (0x9b288 : word) = Some W_9b288.
Proof. vm_refl. Qed.
Lemma D_9b288 : decode_any W_9b288 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b28c : bv 32 := 0x01058593.
Lemma F_9b28c : fetch_word Asan.M.loaded_segments (0x9b28c : word) = Some W_9b28c.
Proof. vm_refl. Qed.
Lemma D_9b28c : decode_any W_9b28c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b290 : bv 32 := 0x01100793.
Lemma F_9b290 : fetch_word Asan.M.loaded_segments (0x9b290 : word) = Some W_9b290.
Proof. vm_refl. Qed.
Lemma D_9b290 : decode_any W_9b290 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b294 : bv 32 := 0x0107581b.
Lemma F_9b294 : fetch_word Asan.M.loaded_segments (0x9b294 : word) = Some W_9b294.
Proof. vm_refl. Qed.
Lemma D_9b294 : decode_any W_9b294 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b298 : bv 32 := 0xff45a883.
Lemma F_9b298 : fetch_word Asan.M.loaded_segments (0x9b298 : word) = Some W_9b298.
Proof. vm_refl. Qed.
Lemma D_9b298 : decode_any W_9b298 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b29c : bv 32 := 0xff85a283.
Lemma F_9b29c : fetch_word Asan.M.loaded_segments (0x9b29c : word) = Some W_9b29c.
Proof. vm_refl. Qed.
Lemma D_9b29c : decode_any W_9b29c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2a0 : bv 32 := 0xffc5a303.
Lemma F_9b2a0 : fetch_word Asan.M.loaded_segments (0x9b2a0 : word) = Some W_9b2a0.
Proof. vm_refl. Qed.
Lemma D_9b2a0 : decode_any W_9b2a0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2a4 : bv 32 := 0x0005a703.
Lemma F_9b2a4 : fetch_word Asan.M.loaded_segments (0x9b2a4 : word) = Some W_9b2a4.
Proof. vm_refl. Qed.
Lemma D_9b2a4 : decode_any W_9b2a4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2a8 : bv 32 := 0x01089393.
Lemma F_9b2a8 : fetch_word Asan.M.loaded_segments (0x9b2a8 : word) = Some W_9b2a8.
Proof. vm_refl. Qed.
Lemma D_9b2a8 : decode_any W_9b2a8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2ac : bv 32 := 0x0108d89b.
Lemma F_9b2ac : fetch_word Asan.M.loaded_segments (0x9b2ac : word) = Some W_9b2ac.
Proof. vm_refl. Qed.
Lemma D_9b2ac : decode_any W_9b2ac = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2b0 : bv 32 := 0x0103e833.
Lemma F_9b2b0 : fetch_word Asan.M.loaded_segments (0x9b2b0 : word) = Some W_9b2b0.
Proof. vm_refl. Qed.
Lemma D_9b2b0 : decode_any W_9b2b0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2b4 : bv 32 := 0x01029393.
Lemma F_9b2b4 : fetch_word Asan.M.loaded_segments (0x9b2b4 : word) = Some W_9b2b4.
Proof. vm_refl. Qed.
Lemma D_9b2b4 : decode_any W_9b2b4 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2b8 : bv 32 := 0x0102d29b.
Lemma F_9b2b8 : fetch_word Asan.M.loaded_segments (0x9b2b8 : word) = Some W_9b2b8.
Proof. vm_refl. Qed.
Lemma D_9b2b8 : decode_any W_9b2b8 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2bc : bv 32 := 0x0113e8b3.
Lemma F_9b2bc : fetch_word Asan.M.loaded_segments (0x9b2bc : word) = Some W_9b2bc.
Proof. vm_refl. Qed.
Lemma D_9b2bc : decode_any W_9b2bc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2c0 : bv 32 := 0x01031393.
Lemma F_9b2c0 : fetch_word Asan.M.loaded_segments (0x9b2c0 : word) = Some W_9b2c0.
Proof. vm_refl. Qed.
Lemma D_9b2c0 : decode_any W_9b2c0 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2c4 : bv 32 := 0x0103531b.
Lemma F_9b2c4 : fetch_word Asan.M.loaded_segments (0x9b2c4 : word) = Some W_9b2c4.
Proof. vm_refl. Qed.
Lemma D_9b2c4 : decode_any W_9b2c4 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2c8 : bv 32 := 0x0053e2b3.
Lemma F_9b2c8 : fetch_word Asan.M.loaded_segments (0x9b2c8 : word) = Some W_9b2c8.
Proof. vm_refl. Qed.
Lemma D_9b2c8 : decode_any W_9b2c8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2cc : bv 32 := 0x01071393.
Lemma F_9b2cc : fetch_word Asan.M.loaded_segments (0x9b2cc : word) = Some W_9b2cc.
Proof. vm_refl. Qed.
Lemma D_9b2cc : decode_any W_9b2cc = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2d0 : bv 32 := 0x0063e333.
Lemma F_9b2d0 : fetch_word Asan.M.loaded_segments (0x9b2d0 : word) = Some W_9b2d0.
Proof. vm_refl. Qed.
Lemma D_9b2d0 : decode_any W_9b2d0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2d4 : bv 32 := 0xff060613.
Lemma F_9b2d4 : fetch_word Asan.M.loaded_segments (0x9b2d4 : word) = Some W_9b2d4.
Proof. vm_refl. Qed.
Lemma D_9b2d4 : decode_any W_9b2d4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2d8 : bv 32 := 0x0106a023.
Lemma F_9b2d8 : fetch_word Asan.M.loaded_segments (0x9b2d8 : word) = Some W_9b2d8.
Proof. vm_refl. Qed.
Lemma D_9b2d8 : decode_any W_9b2d8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2dc : bv 32 := 0x0116a223.
Lemma F_9b2dc : fetch_word Asan.M.loaded_segments (0x9b2dc : word) = Some W_9b2dc.
Proof. vm_refl. Qed.
Lemma D_9b2dc : decode_any W_9b2dc = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2e0 : bv 32 := 0x0056a423.
Lemma F_9b2e0 : fetch_word Asan.M.loaded_segments (0x9b2e0 : word) = Some W_9b2e0.
Proof. vm_refl. Qed.
Lemma D_9b2e0 : decode_any W_9b2e0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2e4 : bv 32 := 0x0066a623.
Lemma F_9b2e4 : fetch_word Asan.M.loaded_segments (0x9b2e4 : word) = Some W_9b2e4.
Proof. vm_refl. Qed.
Lemma D_9b2e4 : decode_any W_9b2e4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2e8 : bv 32 := 0x01068693.
Lemma F_9b2e8 : fetch_word Asan.M.loaded_segments (0x9b2e8 : word) = Some W_9b2e8.
Proof. vm_refl. Qed.
Lemma D_9b2e8 : decode_any W_9b2e8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2ec : bv 32 := 0x01058593.
Lemma F_9b2ec : fetch_word Asan.M.loaded_segments (0x9b2ec : word) = Some W_9b2ec.
Proof. vm_refl. Qed.
Lemma D_9b2ec : decode_any W_9b2ec = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2f0 : bv 32 := 0xfac7e2e3.
Lemma F_9b2f0 : fetch_word Asan.M.loaded_segments (0x9b2f0 : word) = Some W_9b2f0.
Proof. vm_refl. Qed.
Lemma D_9b2f0 : decode_any W_9b2f0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2f4 : bv 32 := 0xff258593.
Lemma F_9b2f4 : fetch_word Asan.M.loaded_segments (0x9b2f4 : word) = Some W_9b2f4.
Proof. vm_refl. Qed.
Lemma D_9b2f4 : decode_any W_9b2f4 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2f8 : bv 32 := 0x01000713.
Lemma F_9b2f8 : fetch_word Asan.M.loaded_segments (0x9b2f8 : word) = Some W_9b2f8.
Proof. vm_refl. Qed.
Lemma D_9b2f8 : decode_any W_9b2f8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2fc : bv 32 := 0xf4e66ae3.
Lemma F_9b2fc : fetch_word Asan.M.loaded_segments (0x9b2fc : word) = Some W_9b2fc.
Proof. vm_refl. Qed.
Lemma D_9b2fc : decode_any W_9b2fc = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b300 : bv 32 := 0x19c0006f.
Lemma F_9b300 : fetch_word Asan.M.loaded_segments (0x9b300 : word) = Some W_9b300.
Proof. vm_refl. Qed.
Lemma D_9b300 : decode_any W_9b300 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b304 : bv 32 := 0x00050693.
Lemma F_9b304 : fetch_word Asan.M.loaded_segments (0x9b304 : word) = Some W_9b304.
Proof. vm_refl. Qed.
Lemma D_9b304 : decode_any W_9b304 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b308 : bv 32 := 0x00357793.
Lemma F_9b308 : fetch_word Asan.M.loaded_segments (0x9b308 : word) = Some W_9b308.
Proof. vm_refl. Qed.
Lemma D_9b308 : decode_any W_9b308 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b30c : bv 32 := 0xf2079ae3.
Lemma F_9b30c : fetch_word Asan.M.loaded_segments (0x9b30c : word) = Some W_9b30c.
Proof. vm_refl. Qed.
Lemma D_9b30c : decode_any W_9b30c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b310 : bv 32 := 0x01000713.
Lemma F_9b310 : fetch_word Asan.M.loaded_segments (0x9b310 : word) = Some W_9b310.
Proof. vm_refl. Qed.
Lemma D_9b310 : decode_any W_9b310 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b314 : bv 32 := 0x02e66c63.
Lemma F_9b314 : fetch_word Asan.M.loaded_segments (0x9b314 : word) = Some W_9b314.
Proof. vm_refl. Qed.
Lemma D_9b314 : decode_any W_9b314 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b318 : bv 32 := 0x00f00713.
Lemma F_9b318 : fetch_word Asan.M.loaded_segments (0x9b318 : word) = Some W_9b318.
Proof. vm_refl. Qed.
Lemma D_9b318 : decode_any W_9b318 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b31c : bv 32 := 0x0005a783.
Lemma F_9b31c : fetch_word Asan.M.loaded_segments (0x9b31c : word) = Some W_9b31c.
Proof. vm_refl. Qed.
Lemma D_9b31c : decode_any W_9b31c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b320 : bv 32 := 0x0045a803.
Lemma F_9b320 : fetch_word Asan.M.loaded_segments (0x9b320 : word) = Some W_9b320.
Proof. vm_refl. Qed.
Lemma D_9b320 : decode_any W_9b320 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b324 : bv 32 := 0x0085a883.
Lemma F_9b324 : fetch_word Asan.M.loaded_segments (0x9b324 : word) = Some W_9b324.
Proof. vm_refl. Qed.
Lemma D_9b324 : decode_any W_9b324 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b328 : bv 32 := 0x00c5a283.
Lemma F_9b328 : fetch_word Asan.M.loaded_segments (0x9b328 : word) = Some W_9b328.
Proof. vm_refl. Qed.
Lemma D_9b328 : decode_any W_9b328 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b32c : bv 32 := 0x01058593.
Lemma F_9b32c : fetch_word Asan.M.loaded_segments (0x9b32c : word) = Some W_9b32c.
Proof. vm_refl. Qed.
Lemma D_9b32c : decode_any W_9b32c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b330 : bv 32 := 0xff060613.
Lemma F_9b330 : fetch_word Asan.M.loaded_segments (0x9b330 : word) = Some W_9b330.
Proof. vm_refl. Qed.
Lemma D_9b330 : decode_any W_9b330 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b334 : bv 32 := 0x00f6a023.
Lemma F_9b334 : fetch_word Asan.M.loaded_segments (0x9b334 : word) = Some W_9b334.
Proof. vm_refl. Qed.
Lemma D_9b334 : decode_any W_9b334 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b338 : bv 32 := 0x0106a223.
Lemma F_9b338 : fetch_word Asan.M.loaded_segments (0x9b338 : word) = Some W_9b338.
Proof. vm_refl. Qed.
Lemma D_9b338 : decode_any W_9b338 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b33c : bv 32 := 0x0116a423.
Lemma F_9b33c : fetch_word Asan.M.loaded_segments (0x9b33c : word) = Some W_9b33c.
Proof. vm_refl. Qed.
Lemma D_9b33c : decode_any W_9b33c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b340 : bv 32 := 0x0056a623.
Lemma F_9b340 : fetch_word Asan.M.loaded_segments (0x9b340 : word) = Some W_9b340.
Proof. vm_refl. Qed.
Lemma D_9b340 : decode_any W_9b340 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b344 : bv 32 := 0x01068693.
Lemma F_9b344 : fetch_word Asan.M.loaded_segments (0x9b344 : word) = Some W_9b344.
Proof. vm_refl. Qed.
Lemma D_9b344 : decode_any W_9b344 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b348 : bv 32 := 0xfcc76ae3.
Lemma F_9b348 : fetch_word Asan.M.loaded_segments (0x9b348 : word) = Some W_9b348.
Proof. vm_refl. Qed.
Lemma D_9b348 : decode_any W_9b348 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b34c : bv 32 := 0x00800713.
Lemma F_9b34c : fetch_word Asan.M.loaded_segments (0x9b34c : word) = Some W_9b34c.
Proof. vm_refl. Qed.
Lemma D_9b34c : decode_any W_9b34c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b350 : bv 32 := 0x00e66e63.
Lemma F_9b350 : fetch_word Asan.M.loaded_segments (0x9b350 : word) = Some W_9b350.
Proof. vm_refl. Qed.
Lemma D_9b350 : decode_any W_9b350 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b354 : bv 32 := 0x0005a703.
Lemma F_9b354 : fetch_word Asan.M.loaded_segments (0x9b354 : word) = Some W_9b354.
Proof. vm_refl. Qed.
Lemma D_9b354 : decode_any W_9b354 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b358 : bv 32 := 0x0045a783.
Lemma F_9b358 : fetch_word Asan.M.loaded_segments (0x9b358 : word) = Some W_9b358.
Proof. vm_refl. Qed.
Lemma D_9b358 : decode_any W_9b358 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b35c : bv 32 := 0x00e6a023.
Lemma F_9b35c : fetch_word Asan.M.loaded_segments (0x9b35c : word) = Some W_9b35c.
Proof. vm_refl. Qed.
Lemma D_9b35c : decode_any W_9b35c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b360 : bv 32 := 0x00f6a223.
Lemma F_9b360 : fetch_word Asan.M.loaded_segments (0x9b360 : word) = Some W_9b360.
Proof. vm_refl. Qed.
Lemma D_9b360 : decode_any W_9b360 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b364 : bv 32 := 0x00868693.
Lemma F_9b364 : fetch_word Asan.M.loaded_segments (0x9b364 : word) = Some W_9b364.
Proof. vm_refl. Qed.
Lemma D_9b364 : decode_any W_9b364 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b368 : bv 32 := 0x00858593.
Lemma F_9b368 : fetch_word Asan.M.loaded_segments (0x9b368 : word) = Some W_9b368.
Proof. vm_refl. Qed.
Lemma D_9b368 : decode_any W_9b368 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b36c : bv 32 := 0x00467713.
Lemma F_9b36c : fetch_word Asan.M.loaded_segments (0x9b36c : word) = Some W_9b36c.
Proof. vm_refl. Qed.
Lemma D_9b36c : decode_any W_9b36c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b370 : bv 32 := 0x24070063.
Lemma F_9b370 : fetch_word Asan.M.loaded_segments (0x9b370 : word) = Some W_9b370.
Proof. vm_refl. Qed.
Lemma D_9b370 : decode_any W_9b370 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b374 : bv 32 := 0x0005a703.
Lemma F_9b374 : fetch_word Asan.M.loaded_segments (0x9b374 : word) = Some W_9b374.
Proof. vm_refl. Qed.
Lemma D_9b374 : decode_any W_9b374 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b378 : bv 32 := 0x00458593.
Lemma F_9b378 : fetch_word Asan.M.loaded_segments (0x9b378 : word) = Some W_9b378.
Proof. vm_refl. Qed.
Lemma D_9b378 : decode_any W_9b378 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b37c : bv 32 := 0x00e6a023.
Lemma F_9b37c : fetch_word Asan.M.loaded_segments (0x9b37c : word) = Some W_9b37c.
Proof. vm_refl. Qed.
Lemma D_9b37c : decode_any W_9b37c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b380 : bv 32 := 0x00468693.
Lemma F_9b380 : fetch_word Asan.M.loaded_segments (0x9b380 : word) = Some W_9b380.
Proof. vm_refl. Qed.
Lemma D_9b380 : decode_any W_9b380 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b384 : bv 32 := 0x22c0006f.
Lemma F_9b384 : fetch_word Asan.M.loaded_segments (0x9b384 : word) = Some W_9b384.
Proof. vm_refl. Qed.
Lemma D_9b384 : decode_any W_9b384 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b388 : bv 32 := 0x00e68023.
Lemma F_9b388 : fetch_word Asan.M.loaded_segments (0x9b388 : word) = Some W_9b388.
Proof. vm_refl. Qed.
Lemma D_9b388 : decode_any W_9b388 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b38c : bv 32 := 0x00168693.
Lemma F_9b38c : fetch_word Asan.M.loaded_segments (0x9b38c : word) = Some W_9b38c.
Proof. vm_refl. Qed.
Lemma D_9b38c : decode_any W_9b38c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b390 : bv 32 := 0xfff60613.
Lemma F_9b390 : fetch_word Asan.M.loaded_segments (0x9b390 : word) = Some W_9b390.
Proof. vm_refl. Qed.
Lemma D_9b390 : decode_any W_9b390 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b394 : bv 32 := 0x01058593.
Lemma F_9b394 : fetch_word Asan.M.loaded_segments (0x9b394 : word) = Some W_9b394.
Proof. vm_refl. Qed.
Lemma D_9b394 : decode_any W_9b394 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b398 : bv 32 := 0x01200793.
Lemma F_9b398 : fetch_word Asan.M.loaded_segments (0x9b398 : word) = Some W_9b398.
Proof. vm_refl. Qed.
Lemma D_9b398 : decode_any W_9b398 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b39c : bv 32 := 0x0087581b.
Lemma F_9b39c : fetch_word Asan.M.loaded_segments (0x9b39c : word) = Some W_9b39c.
Proof. vm_refl. Qed.
Lemma D_9b39c : decode_any W_9b39c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3a0 : bv 32 := 0xff45a883.
Lemma F_9b3a0 : fetch_word Asan.M.loaded_segments (0x9b3a0 : word) = Some W_9b3a0.
Proof. vm_refl. Qed.
Lemma D_9b3a0 : decode_any W_9b3a0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3a4 : bv 32 := 0xff85a283.
Lemma F_9b3a4 : fetch_word Asan.M.loaded_segments (0x9b3a4 : word) = Some W_9b3a4.
Proof. vm_refl. Qed.
Lemma D_9b3a4 : decode_any W_9b3a4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3a8 : bv 32 := 0xffc5a303.
Lemma F_9b3a8 : fetch_word Asan.M.loaded_segments (0x9b3a8 : word) = Some W_9b3a8.
Proof. vm_refl. Qed.
Lemma D_9b3a8 : decode_any W_9b3a8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3ac : bv 32 := 0x0005a703.
Lemma F_9b3ac : fetch_word Asan.M.loaded_segments (0x9b3ac : word) = Some W_9b3ac.
Proof. vm_refl. Qed.
Lemma D_9b3ac : decode_any W_9b3ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3b0 : bv 32 := 0x01889393.
Lemma F_9b3b0 : fetch_word Asan.M.loaded_segments (0x9b3b0 : word) = Some W_9b3b0.
Proof. vm_refl. Qed.
Lemma D_9b3b0 : decode_any W_9b3b0 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3b4 : bv 32 := 0x0088d89b.
Lemma F_9b3b4 : fetch_word Asan.M.loaded_segments (0x9b3b4 : word) = Some W_9b3b4.
Proof. vm_refl. Qed.
Lemma D_9b3b4 : decode_any W_9b3b4 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3b8 : bv 32 := 0x0103e833.
Lemma F_9b3b8 : fetch_word Asan.M.loaded_segments (0x9b3b8 : word) = Some W_9b3b8.
Proof. vm_refl. Qed.
Lemma D_9b3b8 : decode_any W_9b3b8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3bc : bv 32 := 0x01829393.
Lemma F_9b3bc : fetch_word Asan.M.loaded_segments (0x9b3bc : word) = Some W_9b3bc.
Proof. vm_refl. Qed.
Lemma D_9b3bc : decode_any W_9b3bc = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3c0 : bv 32 := 0x0082d29b.
Lemma F_9b3c0 : fetch_word Asan.M.loaded_segments (0x9b3c0 : word) = Some W_9b3c0.
Proof. vm_refl. Qed.
Lemma D_9b3c0 : decode_any W_9b3c0 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3c4 : bv 32 := 0x0113e8b3.
Lemma F_9b3c4 : fetch_word Asan.M.loaded_segments (0x9b3c4 : word) = Some W_9b3c4.
Proof. vm_refl. Qed.
Lemma D_9b3c4 : decode_any W_9b3c4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3c8 : bv 32 := 0x01831393.
Lemma F_9b3c8 : fetch_word Asan.M.loaded_segments (0x9b3c8 : word) = Some W_9b3c8.
Proof. vm_refl. Qed.
Lemma D_9b3c8 : decode_any W_9b3c8 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3cc : bv 32 := 0x0083531b.
Lemma F_9b3cc : fetch_word Asan.M.loaded_segments (0x9b3cc : word) = Some W_9b3cc.
Proof. vm_refl. Qed.
Lemma D_9b3cc : decode_any W_9b3cc = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3d0 : bv 32 := 0x0053e2b3.
Lemma F_9b3d0 : fetch_word Asan.M.loaded_segments (0x9b3d0 : word) = Some W_9b3d0.
Proof. vm_refl. Qed.
Lemma D_9b3d0 : decode_any W_9b3d0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3d4 : bv 32 := 0x01871393.
Lemma F_9b3d4 : fetch_word Asan.M.loaded_segments (0x9b3d4 : word) = Some W_9b3d4.
Proof. vm_refl. Qed.
Lemma D_9b3d4 : decode_any W_9b3d4 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3d8 : bv 32 := 0x0063e333.
Lemma F_9b3d8 : fetch_word Asan.M.loaded_segments (0x9b3d8 : word) = Some W_9b3d8.
Proof. vm_refl. Qed.
Lemma D_9b3d8 : decode_any W_9b3d8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3dc : bv 32 := 0xff060613.
Lemma F_9b3dc : fetch_word Asan.M.loaded_segments (0x9b3dc : word) = Some W_9b3dc.
Proof. vm_refl. Qed.
Lemma D_9b3dc : decode_any W_9b3dc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3e0 : bv 32 := 0x0106a023.
Lemma F_9b3e0 : fetch_word Asan.M.loaded_segments (0x9b3e0 : word) = Some W_9b3e0.
Proof. vm_refl. Qed.
Lemma D_9b3e0 : decode_any W_9b3e0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3e4 : bv 32 := 0x0116a223.
Lemma F_9b3e4 : fetch_word Asan.M.loaded_segments (0x9b3e4 : word) = Some W_9b3e4.
Proof. vm_refl. Qed.
Lemma D_9b3e4 : decode_any W_9b3e4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3e8 : bv 32 := 0x0056a423.
Lemma F_9b3e8 : fetch_word Asan.M.loaded_segments (0x9b3e8 : word) = Some W_9b3e8.
Proof. vm_refl. Qed.
Lemma D_9b3e8 : decode_any W_9b3e8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3ec : bv 32 := 0x0066a623.
Lemma F_9b3ec : fetch_word Asan.M.loaded_segments (0x9b3ec : word) = Some W_9b3ec.
Proof. vm_refl. Qed.
Lemma D_9b3ec : decode_any W_9b3ec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3f0 : bv 32 := 0x01068693.
Lemma F_9b3f0 : fetch_word Asan.M.loaded_segments (0x9b3f0 : word) = Some W_9b3f0.
Proof. vm_refl. Qed.
Lemma D_9b3f0 : decode_any W_9b3f0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3f4 : bv 32 := 0x01058593.
Lemma F_9b3f4 : fetch_word Asan.M.loaded_segments (0x9b3f4 : word) = Some W_9b3f4.
Proof. vm_refl. Qed.
Lemma D_9b3f4 : decode_any W_9b3f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3f8 : bv 32 := 0xfac7e2e3.
Lemma F_9b3f8 : fetch_word Asan.M.loaded_segments (0x9b3f8 : word) = Some W_9b3f8.
Proof. vm_refl. Qed.
Lemma D_9b3f8 : decode_any W_9b3f8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3fc : bv 32 := 0xff158593.
Lemma F_9b3fc : fetch_word Asan.M.loaded_segments (0x9b3fc : word) = Some W_9b3fc.
Proof. vm_refl. Qed.
Lemma D_9b3fc : decode_any W_9b3fc = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b400 : bv 32 := 0x01000713.
Lemma F_9b400 : fetch_word Asan.M.loaded_segments (0x9b400 : word) = Some W_9b400.
Proof. vm_refl. Qed.
Lemma D_9b400 : decode_any W_9b400 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b404 : bv 32 := 0xe4e666e3.
Lemma F_9b404 : fetch_word Asan.M.loaded_segments (0x9b404 : word) = Some W_9b404.
Proof. vm_refl. Qed.
Lemma D_9b404 : decode_any W_9b404 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b408 : bv 32 := 0x0940006f.
Lemma F_9b408 : fetch_word Asan.M.loaded_segments (0x9b408 : word) = Some W_9b408.
Proof. vm_refl. Qed.
Lemma D_9b408 : decode_any W_9b408 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b40c : bv 32 := 0x00875793.
Lemma F_9b40c : fetch_word Asan.M.loaded_segments (0x9b40c : word) = Some W_9b40c.
Proof. vm_refl. Qed.
Lemma D_9b40c : decode_any W_9b40c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b410 : bv 32 := 0x01075813.
Lemma F_9b410 : fetch_word Asan.M.loaded_segments (0x9b410 : word) = Some W_9b410.
Proof. vm_refl. Qed.
Lemma D_9b410 : decode_any W_9b410 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b414 : bv 32 := 0xffd60613.
Lemma F_9b414 : fetch_word Asan.M.loaded_segments (0x9b414 : word) = Some W_9b414.
Proof. vm_refl. Qed.
Lemma D_9b414 : decode_any W_9b414 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b418 : bv 32 := 0x00e68023.
Lemma F_9b418 : fetch_word Asan.M.loaded_segments (0x9b418 : word) = Some W_9b418.
Proof. vm_refl. Qed.
Lemma D_9b418 : decode_any W_9b418 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b41c : bv 32 := 0x00f680a3.
Lemma F_9b41c : fetch_word Asan.M.loaded_segments (0x9b41c : word) = Some W_9b41c.
Proof. vm_refl. Qed.
Lemma D_9b41c : decode_any W_9b41c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b420 : bv 32 := 0x01068123.
Lemma F_9b420 : fetch_word Asan.M.loaded_segments (0x9b420 : word) = Some W_9b420.
Proof. vm_refl. Qed.
Lemma D_9b420 : decode_any W_9b420 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b424 : bv 32 := 0x00368693.
Lemma F_9b424 : fetch_word Asan.M.loaded_segments (0x9b424 : word) = Some W_9b424.
Proof. vm_refl. Qed.
Lemma D_9b424 : decode_any W_9b424 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b428 : bv 32 := 0x01058593.
Lemma F_9b428 : fetch_word Asan.M.loaded_segments (0x9b428 : word) = Some W_9b428.
Proof. vm_refl. Qed.
Lemma D_9b428 : decode_any W_9b428 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b42c : bv 32 := 0x01000793.
Lemma F_9b42c : fetch_word Asan.M.loaded_segments (0x9b42c : word) = Some W_9b42c.
Proof. vm_refl. Qed.
Lemma D_9b42c : decode_any W_9b42c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b430 : bv 32 := 0x0187581b.
Lemma F_9b430 : fetch_word Asan.M.loaded_segments (0x9b430 : word) = Some W_9b430.
Proof. vm_refl. Qed.
Lemma D_9b430 : decode_any W_9b430 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b434 : bv 32 := 0xff45a883.
Lemma F_9b434 : fetch_word Asan.M.loaded_segments (0x9b434 : word) = Some W_9b434.
Proof. vm_refl. Qed.
Lemma D_9b434 : decode_any W_9b434 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b438 : bv 32 := 0xff85a283.
Lemma F_9b438 : fetch_word Asan.M.loaded_segments (0x9b438 : word) = Some W_9b438.
Proof. vm_refl. Qed.
Lemma D_9b438 : decode_any W_9b438 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b43c : bv 32 := 0xffc5a303.
Lemma F_9b43c : fetch_word Asan.M.loaded_segments (0x9b43c : word) = Some W_9b43c.
Proof. vm_refl. Qed.
Lemma D_9b43c : decode_any W_9b43c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b440 : bv 32 := 0x0005a703.
Lemma F_9b440 : fetch_word Asan.M.loaded_segments (0x9b440 : word) = Some W_9b440.
Proof. vm_refl. Qed.
Lemma D_9b440 : decode_any W_9b440 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b444 : bv 32 := 0x00889393.
Lemma F_9b444 : fetch_word Asan.M.loaded_segments (0x9b444 : word) = Some W_9b444.
Proof. vm_refl. Qed.
Lemma D_9b444 : decode_any W_9b444 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b448 : bv 32 := 0x0188d89b.
Lemma F_9b448 : fetch_word Asan.M.loaded_segments (0x9b448 : word) = Some W_9b448.
Proof. vm_refl. Qed.
Lemma D_9b448 : decode_any W_9b448 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b44c : bv 32 := 0x0103e833.
Lemma F_9b44c : fetch_word Asan.M.loaded_segments (0x9b44c : word) = Some W_9b44c.
Proof. vm_refl. Qed.
Lemma D_9b44c : decode_any W_9b44c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b450 : bv 32 := 0x00829393.
Lemma F_9b450 : fetch_word Asan.M.loaded_segments (0x9b450 : word) = Some W_9b450.
Proof. vm_refl. Qed.
Lemma D_9b450 : decode_any W_9b450 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b454 : bv 32 := 0x0182d29b.
Lemma F_9b454 : fetch_word Asan.M.loaded_segments (0x9b454 : word) = Some W_9b454.
Proof. vm_refl. Qed.
Lemma D_9b454 : decode_any W_9b454 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b458 : bv 32 := 0x0113e8b3.
Lemma F_9b458 : fetch_word Asan.M.loaded_segments (0x9b458 : word) = Some W_9b458.
Proof. vm_refl. Qed.
Lemma D_9b458 : decode_any W_9b458 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b45c : bv 32 := 0x00831393.
Lemma F_9b45c : fetch_word Asan.M.loaded_segments (0x9b45c : word) = Some W_9b45c.
Proof. vm_refl. Qed.
Lemma D_9b45c : decode_any W_9b45c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b460 : bv 32 := 0x0183531b.
Lemma F_9b460 : fetch_word Asan.M.loaded_segments (0x9b460 : word) = Some W_9b460.
Proof. vm_refl. Qed.
Lemma D_9b460 : decode_any W_9b460 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b464 : bv 32 := 0x0053e2b3.
Lemma F_9b464 : fetch_word Asan.M.loaded_segments (0x9b464 : word) = Some W_9b464.
Proof. vm_refl. Qed.
Lemma D_9b464 : decode_any W_9b464 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b468 : bv 32 := 0x00871393.
Lemma F_9b468 : fetch_word Asan.M.loaded_segments (0x9b468 : word) = Some W_9b468.
Proof. vm_refl. Qed.
Lemma D_9b468 : decode_any W_9b468 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b46c : bv 32 := 0x0063e333.
Lemma F_9b46c : fetch_word Asan.M.loaded_segments (0x9b46c : word) = Some W_9b46c.
Proof. vm_refl. Qed.
Lemma D_9b46c : decode_any W_9b46c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b470 : bv 32 := 0xff060613.
Lemma F_9b470 : fetch_word Asan.M.loaded_segments (0x9b470 : word) = Some W_9b470.
Proof. vm_refl. Qed.
Lemma D_9b470 : decode_any W_9b470 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b474 : bv 32 := 0x0106a023.
Lemma F_9b474 : fetch_word Asan.M.loaded_segments (0x9b474 : word) = Some W_9b474.
Proof. vm_refl. Qed.
Lemma D_9b474 : decode_any W_9b474 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b478 : bv 32 := 0x0116a223.
Lemma F_9b478 : fetch_word Asan.M.loaded_segments (0x9b478 : word) = Some W_9b478.
Proof. vm_refl. Qed.
Lemma D_9b478 : decode_any W_9b478 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b47c : bv 32 := 0x0056a423.
Lemma F_9b47c : fetch_word Asan.M.loaded_segments (0x9b47c : word) = Some W_9b47c.
Proof. vm_refl. Qed.
Lemma D_9b47c : decode_any W_9b47c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b480 : bv 32 := 0x0066a623.
Lemma F_9b480 : fetch_word Asan.M.loaded_segments (0x9b480 : word) = Some W_9b480.
Proof. vm_refl. Qed.
Lemma D_9b480 : decode_any W_9b480 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b484 : bv 32 := 0x01068693.
Lemma F_9b484 : fetch_word Asan.M.loaded_segments (0x9b484 : word) = Some W_9b484.
Proof. vm_refl. Qed.
Lemma D_9b484 : decode_any W_9b484 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b488 : bv 32 := 0x01058593.
Lemma F_9b488 : fetch_word Asan.M.loaded_segments (0x9b488 : word) = Some W_9b488.
Proof. vm_refl. Qed.
Lemma D_9b488 : decode_any W_9b488 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b48c : bv 32 := 0xfac7e2e3.
Lemma F_9b48c : fetch_word Asan.M.loaded_segments (0x9b48c : word) = Some W_9b48c.
Proof. vm_refl. Qed.
Lemma D_9b48c : decode_any W_9b48c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b490 : bv 32 := 0xff358593.
Lemma F_9b490 : fetch_word Asan.M.loaded_segments (0x9b490 : word) = Some W_9b490.
Proof. vm_refl. Qed.
Lemma D_9b490 : decode_any W_9b490 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b494 : bv 32 := 0x01000713.
Lemma F_9b494 : fetch_word Asan.M.loaded_segments (0x9b494 : word) = Some W_9b494.
Proof. vm_refl. Qed.
Lemma D_9b494 : decode_any W_9b494 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b498 : bv 32 := 0xdae66ce3.
Lemma F_9b498 : fetch_word Asan.M.loaded_segments (0x9b498 : word) = Some W_9b498.
Proof. vm_refl. Qed.
Lemma D_9b498 : decode_any W_9b498 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b49c : bv 32 := 0x0005c703.
Lemma F_9b49c : fetch_word Asan.M.loaded_segments (0x9b49c : word) = Some W_9b49c.
Proof. vm_refl. Qed.
Lemma D_9b49c : decode_any W_9b49c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4a0 : bv 32 := 0x0015c783.
Lemma F_9b4a0 : fetch_word Asan.M.loaded_segments (0x9b4a0 : word) = Some W_9b4a0.
Proof. vm_refl. Qed.
Lemma D_9b4a0 : decode_any W_9b4a0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4a4 : bv 32 := 0x0025c803.
Lemma F_9b4a4 : fetch_word Asan.M.loaded_segments (0x9b4a4 : word) = Some W_9b4a4.
Proof. vm_refl. Qed.
Lemma D_9b4a4 : decode_any W_9b4a4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4a8 : bv 32 := 0x0035c883.
Lemma F_9b4a8 : fetch_word Asan.M.loaded_segments (0x9b4a8 : word) = Some W_9b4a8.
Proof. vm_refl. Qed.
Lemma D_9b4a8 : decode_any W_9b4a8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4ac : bv 32 := 0x0045c283.
Lemma F_9b4ac : fetch_word Asan.M.loaded_segments (0x9b4ac : word) = Some W_9b4ac.
Proof. vm_refl. Qed.
Lemma D_9b4ac : decode_any W_9b4ac = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4b0 : bv 32 := 0x0055c303.
Lemma F_9b4b0 : fetch_word Asan.M.loaded_segments (0x9b4b0 : word) = Some W_9b4b0.
Proof. vm_refl. Qed.
Lemma D_9b4b0 : decode_any W_9b4b0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4b4 : bv 32 := 0x0065c383.
Lemma F_9b4b4 : fetch_word Asan.M.loaded_segments (0x9b4b4 : word) = Some W_9b4b4.
Proof. vm_refl. Qed.
Lemma D_9b4b4 : decode_any W_9b4b4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4b8 : bv 32 := 0x0075ce03.
Lemma F_9b4b8 : fetch_word Asan.M.loaded_segments (0x9b4b8 : word) = Some W_9b4b8.
Proof. vm_refl. Qed.
Lemma D_9b4b8 : decode_any W_9b4b8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4bc : bv 32 := 0x00e68023.
Lemma F_9b4bc : fetch_word Asan.M.loaded_segments (0x9b4bc : word) = Some W_9b4bc.
Proof. vm_refl. Qed.
Lemma D_9b4bc : decode_any W_9b4bc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4c0 : bv 32 := 0x00f680a3.
Lemma F_9b4c0 : fetch_word Asan.M.loaded_segments (0x9b4c0 : word) = Some W_9b4c0.
Proof. vm_refl. Qed.
Lemma D_9b4c0 : decode_any W_9b4c0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4c4 : bv 32 := 0x01068123.
Lemma F_9b4c4 : fetch_word Asan.M.loaded_segments (0x9b4c4 : word) = Some W_9b4c4.
Proof. vm_refl. Qed.
Lemma D_9b4c4 : decode_any W_9b4c4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4c8 : bv 32 := 0x011681a3.
Lemma F_9b4c8 : fetch_word Asan.M.loaded_segments (0x9b4c8 : word) = Some W_9b4c8.
Proof. vm_refl. Qed.
Lemma D_9b4c8 : decode_any W_9b4c8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4cc : bv 32 := 0x0085c703.
Lemma F_9b4cc : fetch_word Asan.M.loaded_segments (0x9b4cc : word) = Some W_9b4cc.
Proof. vm_refl. Qed.
Lemma D_9b4cc : decode_any W_9b4cc = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4d0 : bv 32 := 0x0095c783.
Lemma F_9b4d0 : fetch_word Asan.M.loaded_segments (0x9b4d0 : word) = Some W_9b4d0.
Proof. vm_refl. Qed.
Lemma D_9b4d0 : decode_any W_9b4d0 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4d4 : bv 32 := 0x00a5c803.
Lemma F_9b4d4 : fetch_word Asan.M.loaded_segments (0x9b4d4 : word) = Some W_9b4d4.
Proof. vm_refl. Qed.
Lemma D_9b4d4 : decode_any W_9b4d4 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4d8 : bv 32 := 0x00b5c883.
Lemma F_9b4d8 : fetch_word Asan.M.loaded_segments (0x9b4d8 : word) = Some W_9b4d8.
Proof. vm_refl. Qed.
Lemma D_9b4d8 : decode_any W_9b4d8 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4dc : bv 32 := 0x00568223.
Lemma F_9b4dc : fetch_word Asan.M.loaded_segments (0x9b4dc : word) = Some W_9b4dc.
Proof. vm_refl. Qed.
Lemma D_9b4dc : decode_any W_9b4dc = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4e0 : bv 32 := 0x006682a3.
Lemma F_9b4e0 : fetch_word Asan.M.loaded_segments (0x9b4e0 : word) = Some W_9b4e0.
Proof. vm_refl. Qed.
Lemma D_9b4e0 : decode_any W_9b4e0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4e4 : bv 32 := 0x00768323.
Lemma F_9b4e4 : fetch_word Asan.M.loaded_segments (0x9b4e4 : word) = Some W_9b4e4.
Proof. vm_refl. Qed.
Lemma D_9b4e4 : decode_any W_9b4e4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4e8 : bv 32 := 0x01c683a3.
Lemma F_9b4e8 : fetch_word Asan.M.loaded_segments (0x9b4e8 : word) = Some W_9b4e8.
Proof. vm_refl. Qed.
Lemma D_9b4e8 : decode_any W_9b4e8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4ec : bv 32 := 0x00c5c283.
Lemma F_9b4ec : fetch_word Asan.M.loaded_segments (0x9b4ec : word) = Some W_9b4ec.
Proof. vm_refl. Qed.
Lemma D_9b4ec : decode_any W_9b4ec = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4f0 : bv 32 := 0x00d5c303.
Lemma F_9b4f0 : fetch_word Asan.M.loaded_segments (0x9b4f0 : word) = Some W_9b4f0.
Proof. vm_refl. Qed.
Lemma D_9b4f0 : decode_any W_9b4f0 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4f4 : bv 32 := 0x00e5c383.
Lemma F_9b4f4 : fetch_word Asan.M.loaded_segments (0x9b4f4 : word) = Some W_9b4f4.
Proof. vm_refl. Qed.
Lemma D_9b4f4 : decode_any W_9b4f4 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4f8 : bv 32 := 0x00f5ce03.
Lemma F_9b4f8 : fetch_word Asan.M.loaded_segments (0x9b4f8 : word) = Some W_9b4f8.
Proof. vm_refl. Qed.
Lemma D_9b4f8 : decode_any W_9b4f8 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4fc : bv 32 := 0x01058593.
Lemma F_9b4fc : fetch_word Asan.M.loaded_segments (0x9b4fc : word) = Some W_9b4fc.
Proof. vm_refl. Qed.
Lemma D_9b4fc : decode_any W_9b4fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b500 : bv 32 := 0x00e68423.
Lemma F_9b500 : fetch_word Asan.M.loaded_segments (0x9b500 : word) = Some W_9b500.
Proof. vm_refl. Qed.
Lemma D_9b500 : decode_any W_9b500 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b504 : bv 32 := 0x00f684a3.
Lemma F_9b504 : fetch_word Asan.M.loaded_segments (0x9b504 : word) = Some W_9b504.
Proof. vm_refl. Qed.
Lemma D_9b504 : decode_any W_9b504 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b508 : bv 32 := 0x01068523.
Lemma F_9b508 : fetch_word Asan.M.loaded_segments (0x9b508 : word) = Some W_9b508.
Proof. vm_refl. Qed.
Lemma D_9b508 : decode_any W_9b508 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b50c : bv 32 := 0x011685a3.
Lemma F_9b50c : fetch_word Asan.M.loaded_segments (0x9b50c : word) = Some W_9b50c.
Proof. vm_refl. Qed.
Lemma D_9b50c : decode_any W_9b50c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b510 : bv 32 := 0x01068713.
Lemma F_9b510 : fetch_word Asan.M.loaded_segments (0x9b510 : word) = Some W_9b510.
Proof. vm_refl. Qed.
Lemma D_9b510 : decode_any W_9b510 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b514 : bv 32 := 0x00568623.
Lemma F_9b514 : fetch_word Asan.M.loaded_segments (0x9b514 : word) = Some W_9b514.
Proof. vm_refl. Qed.
Lemma D_9b514 : decode_any W_9b514 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b518 : bv 32 := 0x006686a3.
Lemma F_9b518 : fetch_word Asan.M.loaded_segments (0x9b518 : word) = Some W_9b518.
Proof. vm_refl. Qed.
Lemma D_9b518 : decode_any W_9b518 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b51c : bv 32 := 0x00768723.
Lemma F_9b51c : fetch_word Asan.M.loaded_segments (0x9b51c : word) = Some W_9b51c.
Proof. vm_refl. Qed.
Lemma D_9b51c : decode_any W_9b51c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b520 : bv 32 := 0x01c687a3.
Lemma F_9b520 : fetch_word Asan.M.loaded_segments (0x9b520 : word) = Some W_9b520.
Proof. vm_refl. Qed.
Lemma D_9b520 : decode_any W_9b520 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b524 : bv 32 := 0x00070693.
Lemma F_9b524 : fetch_word Asan.M.loaded_segments (0x9b524 : word) = Some W_9b524.
Proof. vm_refl. Qed.
Lemma D_9b524 : decode_any W_9b524 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b528 : bv 32 := 0x00867713.
Lemma F_9b528 : fetch_word Asan.M.loaded_segments (0x9b528 : word) = Some W_9b528.
Proof. vm_refl. Qed.
Lemma D_9b528 : decode_any W_9b528 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b52c : bv 32 := 0xd20706e3.
Lemma F_9b52c : fetch_word Asan.M.loaded_segments (0x9b52c : word) = Some W_9b52c.
Proof. vm_refl. Qed.
Lemma D_9b52c : decode_any W_9b52c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b530 : bv 32 := 0x0005c703.
Lemma F_9b530 : fetch_word Asan.M.loaded_segments (0x9b530 : word) = Some W_9b530.
Proof. vm_refl. Qed.
Lemma D_9b530 : decode_any W_9b530 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b534 : bv 32 := 0x0015c783.
Lemma F_9b534 : fetch_word Asan.M.loaded_segments (0x9b534 : word) = Some W_9b534.
Proof. vm_refl. Qed.
Lemma D_9b534 : decode_any W_9b534 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b538 : bv 32 := 0x0025c803.
Lemma F_9b538 : fetch_word Asan.M.loaded_segments (0x9b538 : word) = Some W_9b538.
Proof. vm_refl. Qed.
Lemma D_9b538 : decode_any W_9b538 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b53c : bv 32 := 0x0035c883.
Lemma F_9b53c : fetch_word Asan.M.loaded_segments (0x9b53c : word) = Some W_9b53c.
Proof. vm_refl. Qed.
Lemma D_9b53c : decode_any W_9b53c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b540 : bv 32 := 0x0045c283.
Lemma F_9b540 : fetch_word Asan.M.loaded_segments (0x9b540 : word) = Some W_9b540.
Proof. vm_refl. Qed.
Lemma D_9b540 : decode_any W_9b540 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b544 : bv 32 := 0x0055c303.
Lemma F_9b544 : fetch_word Asan.M.loaded_segments (0x9b544 : word) = Some W_9b544.
Proof. vm_refl. Qed.
Lemma D_9b544 : decode_any W_9b544 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b548 : bv 32 := 0x0065c383.
Lemma F_9b548 : fetch_word Asan.M.loaded_segments (0x9b548 : word) = Some W_9b548.
Proof. vm_refl. Qed.
Lemma D_9b548 : decode_any W_9b548 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b54c : bv 32 := 0x0075ce03.
Lemma F_9b54c : fetch_word Asan.M.loaded_segments (0x9b54c : word) = Some W_9b54c.
Proof. vm_refl. Qed.
Lemma D_9b54c : decode_any W_9b54c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b550 : bv 32 := 0x00858593.
Lemma F_9b550 : fetch_word Asan.M.loaded_segments (0x9b550 : word) = Some W_9b550.
Proof. vm_refl. Qed.
Lemma D_9b550 : decode_any W_9b550 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b554 : bv 32 := 0x00e68023.
Lemma F_9b554 : fetch_word Asan.M.loaded_segments (0x9b554 : word) = Some W_9b554.
Proof. vm_refl. Qed.
Lemma D_9b554 : decode_any W_9b554 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b558 : bv 32 := 0x00f680a3.
Lemma F_9b558 : fetch_word Asan.M.loaded_segments (0x9b558 : word) = Some W_9b558.
Proof. vm_refl. Qed.
Lemma D_9b558 : decode_any W_9b558 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b55c : bv 32 := 0x01068123.
Lemma F_9b55c : fetch_word Asan.M.loaded_segments (0x9b55c : word) = Some W_9b55c.
Proof. vm_refl. Qed.
Lemma D_9b55c : decode_any W_9b55c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b560 : bv 32 := 0x011681a3.
Lemma F_9b560 : fetch_word Asan.M.loaded_segments (0x9b560 : word) = Some W_9b560.
Proof. vm_refl. Qed.
Lemma D_9b560 : decode_any W_9b560 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b564 : bv 32 := 0x00868713.
Lemma F_9b564 : fetch_word Asan.M.loaded_segments (0x9b564 : word) = Some W_9b564.
Proof. vm_refl. Qed.
Lemma D_9b564 : decode_any W_9b564 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b568 : bv 32 := 0x00568223.
Lemma F_9b568 : fetch_word Asan.M.loaded_segments (0x9b568 : word) = Some W_9b568.
Proof. vm_refl. Qed.
Lemma D_9b568 : decode_any W_9b568 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b56c : bv 32 := 0x006682a3.
Lemma F_9b56c : fetch_word Asan.M.loaded_segments (0x9b56c : word) = Some W_9b56c.
Proof. vm_refl. Qed.
Lemma D_9b56c : decode_any W_9b56c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b570 : bv 32 := 0x00768323.
Lemma F_9b570 : fetch_word Asan.M.loaded_segments (0x9b570 : word) = Some W_9b570.
Proof. vm_refl. Qed.
Lemma D_9b570 : decode_any W_9b570 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b574 : bv 32 := 0x01c683a3.
Lemma F_9b574 : fetch_word Asan.M.loaded_segments (0x9b574 : word) = Some W_9b574.
Proof. vm_refl. Qed.
Lemma D_9b574 : decode_any W_9b574 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b578 : bv 32 := 0x00070693.
Lemma F_9b578 : fetch_word Asan.M.loaded_segments (0x9b578 : word) = Some W_9b578.
Proof. vm_refl. Qed.
Lemma D_9b578 : decode_any W_9b578 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b57c : bv 32 := 0x00467713.
Lemma F_9b57c : fetch_word Asan.M.loaded_segments (0x9b57c : word) = Some W_9b57c.
Proof. vm_refl. Qed.
Lemma D_9b57c : decode_any W_9b57c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b580 : bv 32 := 0x02070863.
Lemma F_9b580 : fetch_word Asan.M.loaded_segments (0x9b580 : word) = Some W_9b580.
Proof. vm_refl. Qed.
Lemma D_9b580 : decode_any W_9b580 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b584 : bv 32 := 0x0005c703.
Lemma F_9b584 : fetch_word Asan.M.loaded_segments (0x9b584 : word) = Some W_9b584.
Proof. vm_refl. Qed.
Lemma D_9b584 : decode_any W_9b584 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b588 : bv 32 := 0x0015c783.
Lemma F_9b588 : fetch_word Asan.M.loaded_segments (0x9b588 : word) = Some W_9b588.
Proof. vm_refl. Qed.
Lemma D_9b588 : decode_any W_9b588 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b58c : bv 32 := 0x0025c803.
Lemma F_9b58c : fetch_word Asan.M.loaded_segments (0x9b58c : word) = Some W_9b58c.
Proof. vm_refl. Qed.
Lemma D_9b58c : decode_any W_9b58c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b590 : bv 32 := 0x0035c883.
Lemma F_9b590 : fetch_word Asan.M.loaded_segments (0x9b590 : word) = Some W_9b590.
Proof. vm_refl. Qed.
Lemma D_9b590 : decode_any W_9b590 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b594 : bv 32 := 0x00458593.
Lemma F_9b594 : fetch_word Asan.M.loaded_segments (0x9b594 : word) = Some W_9b594.
Proof. vm_refl. Qed.
Lemma D_9b594 : decode_any W_9b594 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b598 : bv 32 := 0x00468293.
Lemma F_9b598 : fetch_word Asan.M.loaded_segments (0x9b598 : word) = Some W_9b598.
Proof. vm_refl. Qed.
Lemma D_9b598 : decode_any W_9b598 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b59c : bv 32 := 0x00e68023.
Lemma F_9b59c : fetch_word Asan.M.loaded_segments (0x9b59c : word) = Some W_9b59c.
Proof. vm_refl. Qed.
Lemma D_9b59c : decode_any W_9b59c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5a0 : bv 32 := 0x00f680a3.
Lemma F_9b5a0 : fetch_word Asan.M.loaded_segments (0x9b5a0 : word) = Some W_9b5a0.
Proof. vm_refl. Qed.
Lemma D_9b5a0 : decode_any W_9b5a0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5a4 : bv 32 := 0x01068123.
Lemma F_9b5a4 : fetch_word Asan.M.loaded_segments (0x9b5a4 : word) = Some W_9b5a4.
Proof. vm_refl. Qed.
Lemma D_9b5a4 : decode_any W_9b5a4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5a8 : bv 32 := 0x011681a3.
Lemma F_9b5a8 : fetch_word Asan.M.loaded_segments (0x9b5a8 : word) = Some W_9b5a8.
Proof. vm_refl. Qed.
Lemma D_9b5a8 : decode_any W_9b5a8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5ac : bv 32 := 0x00028693.
Lemma F_9b5ac : fetch_word Asan.M.loaded_segments (0x9b5ac : word) = Some W_9b5ac.
Proof. vm_refl. Qed.
Lemma D_9b5ac : decode_any W_9b5ac = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5b0 : bv 32 := 0x00267713.
Lemma F_9b5b0 : fetch_word Asan.M.loaded_segments (0x9b5b0 : word) = Some W_9b5b0.
Proof. vm_refl. Qed.
Lemma D_9b5b0 : decode_any W_9b5b0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5b4 : bv 32 := 0x00071863.
Lemma F_9b5b4 : fetch_word Asan.M.loaded_segments (0x9b5b4 : word) = Some W_9b5b4.
Proof. vm_refl. Qed.
Lemma D_9b5b4 : decode_any W_9b5b4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5b8 : bv 32 := 0x00167613.
Lemma F_9b5b8 : fetch_word Asan.M.loaded_segments (0x9b5b8 : word) = Some W_9b5b8.
Proof. vm_refl. Qed.
Lemma D_9b5b8 : decode_any W_9b5b8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5bc : bv 32 := 0x02061663.
Lemma F_9b5bc : fetch_word Asan.M.loaded_segments (0x9b5bc : word) = Some W_9b5bc.
Proof. vm_refl. Qed.
Lemma D_9b5bc : decode_any W_9b5bc = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5c0 : bv 32 := 0x00008067.
Lemma F_9b5c0 : fetch_word Asan.M.loaded_segments (0x9b5c0 : word) = Some W_9b5c0.
Proof. vm_refl. Qed.
Lemma D_9b5c0 : decode_any W_9b5c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5c4 : bv 32 := 0x0005c703.
Lemma F_9b5c4 : fetch_word Asan.M.loaded_segments (0x9b5c4 : word) = Some W_9b5c4.
Proof. vm_refl. Qed.
Lemma D_9b5c4 : decode_any W_9b5c4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5c8 : bv 32 := 0x0015c783.
Lemma F_9b5c8 : fetch_word Asan.M.loaded_segments (0x9b5c8 : word) = Some W_9b5c8.
Proof. vm_refl. Qed.
Lemma D_9b5c8 : decode_any W_9b5c8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5cc : bv 32 := 0x00258593.
Lemma F_9b5cc : fetch_word Asan.M.loaded_segments (0x9b5cc : word) = Some W_9b5cc.
Proof. vm_refl. Qed.
Lemma D_9b5cc : decode_any W_9b5cc = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5d0 : bv 32 := 0x00268813.
Lemma F_9b5d0 : fetch_word Asan.M.loaded_segments (0x9b5d0 : word) = Some W_9b5d0.
Proof. vm_refl. Qed.
Lemma D_9b5d0 : decode_any W_9b5d0 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5d4 : bv 32 := 0x00e68023.
Lemma F_9b5d4 : fetch_word Asan.M.loaded_segments (0x9b5d4 : word) = Some W_9b5d4.
Proof. vm_refl. Qed.
Lemma D_9b5d4 : decode_any W_9b5d4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5d8 : bv 32 := 0x00f680a3.
Lemma F_9b5d8 : fetch_word Asan.M.loaded_segments (0x9b5d8 : word) = Some W_9b5d8.
Proof. vm_refl. Qed.
Lemma D_9b5d8 : decode_any W_9b5d8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5dc : bv 32 := 0x00080693.
Lemma F_9b5dc : fetch_word Asan.M.loaded_segments (0x9b5dc : word) = Some W_9b5dc.
Proof. vm_refl. Qed.
Lemma D_9b5dc : decode_any W_9b5dc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e0 : bv 32 := 0x00167613.
Lemma F_9b5e0 : fetch_word Asan.M.loaded_segments (0x9b5e0 : word) = Some W_9b5e0.
Proof. vm_refl. Qed.
Lemma D_9b5e0 : decode_any W_9b5e0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e4 : bv 32 := 0xfc060ee3.
Lemma F_9b5e4 : fetch_word Asan.M.loaded_segments (0x9b5e4 : word) = Some W_9b5e4.
Proof. vm_refl. Qed.
Lemma D_9b5e4 : decode_any W_9b5e4 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e8 : bv 32 := 0x0005c583.
Lemma F_9b5e8 : fetch_word Asan.M.loaded_segments (0x9b5e8 : word) = Some W_9b5e8.
Proof. vm_refl. Qed.
Lemma D_9b5e8 : decode_any W_9b5e8 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5ec : bv 32 := 0x00b68023.
Lemma F_9b5ec : fetch_word Asan.M.loaded_segments (0x9b5ec : word) = Some W_9b5ec.
Proof. vm_refl. Qed.
Lemma D_9b5ec : decode_any W_9b5ec = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5f0 : bv 32 := 0x00008067.
Lemma F_9b5f0 : fetch_word Asan.M.loaded_segments (0x9b5f0 : word) = Some W_9b5f0.
Proof. vm_refl. Qed.
Lemma D_9b5f0 : decode_any W_9b5f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
