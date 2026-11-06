(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5e2f0 : bv 32 := 0x0035f693.
Lemma F_5e2f0 : fetch_word Plain.M.loaded_segments (0x5e2f0 : word) = Some W_5e2f0.
Proof. vm_refl. Qed.
Lemma D_5e2f0 : decode_any W_5e2f0 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2f4 : bv 32 := 0x10068863.
Lemma F_5e2f4 : fetch_word Plain.M.loaded_segments (0x5e2f4 : word) = Some W_5e2f4.
Proof. vm_refl. Qed.
Lemma D_5e2f4 : decode_any W_5e2f4 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2f8 : bv 32 := 0x02060e63.
Lemma F_5e2f8 : fetch_word Plain.M.loaded_segments (0x5e2f8 : word) = Some W_5e2f8.
Proof. vm_refl. Qed.
Lemma D_5e2f8 : decode_any W_5e2f8 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2fc : bv 32 := 0x00158713.
Lemma F_5e2fc : fetch_word Plain.M.loaded_segments (0x5e2fc : word) = Some W_5e2fc.
Proof. vm_refl. Qed.
Lemma D_5e2fc : decode_any W_5e2fc = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e300 : bv 32 := 0x00100793.
Lemma F_5e300 : fetch_word Plain.M.loaded_segments (0x5e300 : word) = Some W_5e300.
Proof. vm_refl. Qed.
Lemma D_5e300 : decode_any W_5e300 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e304 : bv 32 := 0x00050693.
Lemma F_5e304 : fetch_word Plain.M.loaded_segments (0x5e304 : word) = Some W_5e304.
Proof. vm_refl. Qed.
Lemma D_5e304 : decode_any W_5e304 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e308 : bv 32 := 0x0005c883.
Lemma F_5e308 : fetch_word Plain.M.loaded_segments (0x5e308 : word) = Some W_5e308.
Proof. vm_refl. Qed.
Lemma D_5e308 : decode_any W_5e308 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e30c : bv 32 := 0x00060813.
Lemma F_5e30c : fetch_word Plain.M.loaded_segments (0x5e30c : word) = Some W_5e30c.
Proof. vm_refl. Qed.
Lemma D_5e30c : decode_any W_5e30c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e310 : bv 32 := 0x00158593.
Lemma F_5e310 : fetch_word Plain.M.loaded_segments (0x5e310 : word) = Some W_5e310.
Proof. vm_refl. Qed.
Lemma D_5e310 : decode_any W_5e310 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e314 : bv 32 := 0x00377293.
Lemma F_5e314 : fetch_word Plain.M.loaded_segments (0x5e314 : word) = Some W_5e314.
Proof. vm_refl. Qed.
Lemma D_5e314 : decode_any W_5e314 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e318 : bv 32 := 0x01168023.
Lemma F_5e318 : fetch_word Plain.M.loaded_segments (0x5e318 : word) = Some W_5e318.
Proof. vm_refl. Qed.
Lemma D_5e318 : decode_any W_5e318 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e31c : bv 32 := 0x00168693.
Lemma F_5e31c : fetch_word Plain.M.loaded_segments (0x5e31c : word) = Some W_5e31c.
Proof. vm_refl. Qed.
Lemma D_5e31c : decode_any W_5e31c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e320 : bv 32 := 0xfff60613.
Lemma F_5e320 : fetch_word Plain.M.loaded_segments (0x5e320 : word) = Some W_5e320.
Proof. vm_refl. Qed.
Lemma D_5e320 : decode_any W_5e320 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e324 : bv 32 := 0x00028a63.
Lemma F_5e324 : fetch_word Plain.M.loaded_segments (0x5e324 : word) = Some W_5e324.
Proof. vm_refl. Qed.
Lemma D_5e324 : decode_any W_5e324 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e328 : bv 32 := 0x00170713.
Lemma F_5e328 : fetch_word Plain.M.loaded_segments (0x5e328 : word) = Some W_5e328.
Proof. vm_refl. Qed.
Lemma D_5e328 : decode_any W_5e328 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e32c : bv 32 := 0xfcf81ee3.
Lemma F_5e32c : fetch_word Plain.M.loaded_segments (0x5e32c : word) = Some W_5e32c.
Proof. vm_refl. Qed.
Lemma D_5e32c : decode_any W_5e32c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e330 : bv 32 := 0x0080006f.
Lemma F_5e330 : fetch_word Plain.M.loaded_segments (0x5e330 : word) = Some W_5e330.
Proof. vm_refl. Qed.
Lemma D_5e330 : decode_any W_5e330 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e334 : bv 32 := 0x00050693.
Lemma F_5e334 : fetch_word Plain.M.loaded_segments (0x5e334 : word) = Some W_5e334.
Proof. vm_refl. Qed.
Lemma D_5e334 : decode_any W_5e334 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e338 : bv 32 := 0x0036f793.
Lemma F_5e338 : fetch_word Plain.M.loaded_segments (0x5e338 : word) = Some W_5e338.
Proof. vm_refl. Qed.
Lemma D_5e338 : decode_any W_5e338 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e33c : bv 32 := 0x0c078a63.
Lemma F_5e33c : fetch_word Plain.M.loaded_segments (0x5e33c : word) = Some W_5e33c.
Proof. vm_refl. Qed.
Lemma D_5e33c : decode_any W_5e33c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e340 : bv 32 := 0x02000713.
Lemma F_5e340 : fetch_word Plain.M.loaded_segments (0x5e340 : word) = Some W_5e340.
Proof. vm_refl. Qed.
Lemma D_5e340 : decode_any W_5e340 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e344 : bv 32 := 0x02e67063.
Lemma F_5e344 : fetch_word Plain.M.loaded_segments (0x5e344 : word) = Some W_5e344.
Proof. vm_refl. Qed.
Lemma D_5e344 : decode_any W_5e344 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e348 : bv 32 := 0x01000713.
Lemma F_5e348 : fetch_word Plain.M.loaded_segments (0x5e348 : word) = Some W_5e348.
Proof. vm_refl. Qed.
Lemma D_5e348 : decode_any W_5e348 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e34c : bv 32 := 0x24e67863.
Lemma F_5e34c : fetch_word Plain.M.loaded_segments (0x5e34c : word) = Some W_5e34c.
Proof. vm_refl. Qed.
Lemma D_5e34c : decode_any W_5e34c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e350 : bv 32 := 0x00867713.
Lemma F_5e350 : fetch_word Plain.M.loaded_segments (0x5e350 : word) = Some W_5e350.
Proof. vm_refl. Qed.
Lemma D_5e350 : decode_any W_5e350 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e354 : bv 32 := 0x2c071e63.
Lemma F_5e354 : fetch_word Plain.M.loaded_segments (0x5e354 : word) = Some W_5e354.
Proof. vm_refl. Qed.
Lemma D_5e354 : decode_any W_5e354 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e358 : bv 32 := 0x00467713.
Lemma F_5e358 : fetch_word Plain.M.loaded_segments (0x5e358 : word) = Some W_5e358.
Proof. vm_refl. Qed.
Lemma D_5e358 : decode_any W_5e358 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e35c : bv 32 := 0x32071463.
Lemma F_5e35c : fetch_word Plain.M.loaded_segments (0x5e35c : word) = Some W_5e35c.
Proof. vm_refl. Qed.
Lemma D_5e35c : decode_any W_5e35c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e360 : bv 32 := 0x3500006f.
Lemma F_5e360 : fetch_word Plain.M.loaded_segments (0x5e360 : word) = Some W_5e360.
Proof. vm_refl. Qed.
Lemma D_5e360 : decode_any W_5e360 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e364 : bv 32 := 0x0005a703.
Lemma F_5e364 : fetch_word Plain.M.loaded_segments (0x5e364 : word) = Some W_5e364.
Proof. vm_refl. Qed.
Lemma D_5e364 : decode_any W_5e364 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e368 : bv 32 := 0x00300813.
Lemma F_5e368 : fetch_word Plain.M.loaded_segments (0x5e368 : word) = Some W_5e368.
Proof. vm_refl. Qed.
Lemma D_5e368 : decode_any W_5e368 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e36c : bv 32 := 0x11078e63.
Lemma F_5e36c : fetch_word Plain.M.loaded_segments (0x5e36c : word) = Some W_5e36c.
Proof. vm_refl. Qed.
Lemma D_5e36c : decode_any W_5e36c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e370 : bv 32 := 0x00200813.
Lemma F_5e370 : fetch_word Plain.M.loaded_segments (0x5e370 : word) = Some W_5e370.
Proof. vm_refl. Qed.
Lemma D_5e370 : decode_any W_5e370 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e374 : bv 32 := 0x19079c63.
Lemma F_5e374 : fetch_word Plain.M.loaded_segments (0x5e374 : word) = Some W_5e374.
Proof. vm_refl. Qed.
Lemma D_5e374 : decode_any W_5e374 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e378 : bv 32 := 0x00875793.
Lemma F_5e378 : fetch_word Plain.M.loaded_segments (0x5e378 : word) = Some W_5e378.
Proof. vm_refl. Qed.
Lemma D_5e378 : decode_any W_5e378 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e37c : bv 32 := 0xffe60613.
Lemma F_5e37c : fetch_word Plain.M.loaded_segments (0x5e37c : word) = Some W_5e37c.
Proof. vm_refl. Qed.
Lemma D_5e37c : decode_any W_5e37c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e380 : bv 32 := 0x00e68023.
Lemma F_5e380 : fetch_word Plain.M.loaded_segments (0x5e380 : word) = Some W_5e380.
Proof. vm_refl. Qed.
Lemma D_5e380 : decode_any W_5e380 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e384 : bv 32 := 0x00f680a3.
Lemma F_5e384 : fetch_word Plain.M.loaded_segments (0x5e384 : word) = Some W_5e384.
Proof. vm_refl. Qed.
Lemma D_5e384 : decode_any W_5e384 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e388 : bv 32 := 0x00268693.
Lemma F_5e388 : fetch_word Plain.M.loaded_segments (0x5e388 : word) = Some W_5e388.
Proof. vm_refl. Qed.
Lemma D_5e388 : decode_any W_5e388 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e38c : bv 32 := 0x01058593.
Lemma F_5e38c : fetch_word Plain.M.loaded_segments (0x5e38c : word) = Some W_5e38c.
Proof. vm_refl. Qed.
Lemma D_5e38c : decode_any W_5e38c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e390 : bv 32 := 0x01100793.
Lemma F_5e390 : fetch_word Plain.M.loaded_segments (0x5e390 : word) = Some W_5e390.
Proof. vm_refl. Qed.
Lemma D_5e390 : decode_any W_5e390 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e394 : bv 32 := 0x0107581b.
Lemma F_5e394 : fetch_word Plain.M.loaded_segments (0x5e394 : word) = Some W_5e394.
Proof. vm_refl. Qed.
Lemma D_5e394 : decode_any W_5e394 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e398 : bv 32 := 0xff45a883.
Lemma F_5e398 : fetch_word Plain.M.loaded_segments (0x5e398 : word) = Some W_5e398.
Proof. vm_refl. Qed.
Lemma D_5e398 : decode_any W_5e398 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e39c : bv 32 := 0xff85a283.
Lemma F_5e39c : fetch_word Plain.M.loaded_segments (0x5e39c : word) = Some W_5e39c.
Proof. vm_refl. Qed.
Lemma D_5e39c : decode_any W_5e39c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3a0 : bv 32 := 0xffc5a303.
Lemma F_5e3a0 : fetch_word Plain.M.loaded_segments (0x5e3a0 : word) = Some W_5e3a0.
Proof. vm_refl. Qed.
Lemma D_5e3a0 : decode_any W_5e3a0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3a4 : bv 32 := 0x0005a703.
Lemma F_5e3a4 : fetch_word Plain.M.loaded_segments (0x5e3a4 : word) = Some W_5e3a4.
Proof. vm_refl. Qed.
Lemma D_5e3a4 : decode_any W_5e3a4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3a8 : bv 32 := 0x01089393.
Lemma F_5e3a8 : fetch_word Plain.M.loaded_segments (0x5e3a8 : word) = Some W_5e3a8.
Proof. vm_refl. Qed.
Lemma D_5e3a8 : decode_any W_5e3a8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3ac : bv 32 := 0x0108d89b.
Lemma F_5e3ac : fetch_word Plain.M.loaded_segments (0x5e3ac : word) = Some W_5e3ac.
Proof. vm_refl. Qed.
Lemma D_5e3ac : decode_any W_5e3ac = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3b0 : bv 32 := 0x0103e833.
Lemma F_5e3b0 : fetch_word Plain.M.loaded_segments (0x5e3b0 : word) = Some W_5e3b0.
Proof. vm_refl. Qed.
Lemma D_5e3b0 : decode_any W_5e3b0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3b4 : bv 32 := 0x01029393.
Lemma F_5e3b4 : fetch_word Plain.M.loaded_segments (0x5e3b4 : word) = Some W_5e3b4.
Proof. vm_refl. Qed.
Lemma D_5e3b4 : decode_any W_5e3b4 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3b8 : bv 32 := 0x0102d29b.
Lemma F_5e3b8 : fetch_word Plain.M.loaded_segments (0x5e3b8 : word) = Some W_5e3b8.
Proof. vm_refl. Qed.
Lemma D_5e3b8 : decode_any W_5e3b8 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3bc : bv 32 := 0x0113e8b3.
Lemma F_5e3bc : fetch_word Plain.M.loaded_segments (0x5e3bc : word) = Some W_5e3bc.
Proof. vm_refl. Qed.
Lemma D_5e3bc : decode_any W_5e3bc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3c0 : bv 32 := 0x01031393.
Lemma F_5e3c0 : fetch_word Plain.M.loaded_segments (0x5e3c0 : word) = Some W_5e3c0.
Proof. vm_refl. Qed.
Lemma D_5e3c0 : decode_any W_5e3c0 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3c4 : bv 32 := 0x0103531b.
Lemma F_5e3c4 : fetch_word Plain.M.loaded_segments (0x5e3c4 : word) = Some W_5e3c4.
Proof. vm_refl. Qed.
Lemma D_5e3c4 : decode_any W_5e3c4 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3c8 : bv 32 := 0x0053e2b3.
Lemma F_5e3c8 : fetch_word Plain.M.loaded_segments (0x5e3c8 : word) = Some W_5e3c8.
Proof. vm_refl. Qed.
Lemma D_5e3c8 : decode_any W_5e3c8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3cc : bv 32 := 0x01071393.
Lemma F_5e3cc : fetch_word Plain.M.loaded_segments (0x5e3cc : word) = Some W_5e3cc.
Proof. vm_refl. Qed.
Lemma D_5e3cc : decode_any W_5e3cc = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3d0 : bv 32 := 0x0063e333.
Lemma F_5e3d0 : fetch_word Plain.M.loaded_segments (0x5e3d0 : word) = Some W_5e3d0.
Proof. vm_refl. Qed.
Lemma D_5e3d0 : decode_any W_5e3d0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3d4 : bv 32 := 0xff060613.
Lemma F_5e3d4 : fetch_word Plain.M.loaded_segments (0x5e3d4 : word) = Some W_5e3d4.
Proof. vm_refl. Qed.
Lemma D_5e3d4 : decode_any W_5e3d4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3d8 : bv 32 := 0x0106a023.
Lemma F_5e3d8 : fetch_word Plain.M.loaded_segments (0x5e3d8 : word) = Some W_5e3d8.
Proof. vm_refl. Qed.
Lemma D_5e3d8 : decode_any W_5e3d8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3dc : bv 32 := 0x0116a223.
Lemma F_5e3dc : fetch_word Plain.M.loaded_segments (0x5e3dc : word) = Some W_5e3dc.
Proof. vm_refl. Qed.
Lemma D_5e3dc : decode_any W_5e3dc = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3e0 : bv 32 := 0x0056a423.
Lemma F_5e3e0 : fetch_word Plain.M.loaded_segments (0x5e3e0 : word) = Some W_5e3e0.
Proof. vm_refl. Qed.
Lemma D_5e3e0 : decode_any W_5e3e0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3e4 : bv 32 := 0x0066a623.
Lemma F_5e3e4 : fetch_word Plain.M.loaded_segments (0x5e3e4 : word) = Some W_5e3e4.
Proof. vm_refl. Qed.
Lemma D_5e3e4 : decode_any W_5e3e4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3e8 : bv 32 := 0x01068693.
Lemma F_5e3e8 : fetch_word Plain.M.loaded_segments (0x5e3e8 : word) = Some W_5e3e8.
Proof. vm_refl. Qed.
Lemma D_5e3e8 : decode_any W_5e3e8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3ec : bv 32 := 0x01058593.
Lemma F_5e3ec : fetch_word Plain.M.loaded_segments (0x5e3ec : word) = Some W_5e3ec.
Proof. vm_refl. Qed.
Lemma D_5e3ec : decode_any W_5e3ec = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3f0 : bv 32 := 0xfac7e2e3.
Lemma F_5e3f0 : fetch_word Plain.M.loaded_segments (0x5e3f0 : word) = Some W_5e3f0.
Proof. vm_refl. Qed.
Lemma D_5e3f0 : decode_any W_5e3f0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3f4 : bv 32 := 0xff258593.
Lemma F_5e3f4 : fetch_word Plain.M.loaded_segments (0x5e3f4 : word) = Some W_5e3f4.
Proof. vm_refl. Qed.
Lemma D_5e3f4 : decode_any W_5e3f4 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3f8 : bv 32 := 0x01000713.
Lemma F_5e3f8 : fetch_word Plain.M.loaded_segments (0x5e3f8 : word) = Some W_5e3f8.
Proof. vm_refl. Qed.
Lemma D_5e3f8 : decode_any W_5e3f8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3fc : bv 32 := 0xf4e66ae3.
Lemma F_5e3fc : fetch_word Plain.M.loaded_segments (0x5e3fc : word) = Some W_5e3fc.
Proof. vm_refl. Qed.
Lemma D_5e3fc : decode_any W_5e3fc = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e400 : bv 32 := 0x19c0006f.
Lemma F_5e400 : fetch_word Plain.M.loaded_segments (0x5e400 : word) = Some W_5e400.
Proof. vm_refl. Qed.
Lemma D_5e400 : decode_any W_5e400 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e404 : bv 32 := 0x00050693.
Lemma F_5e404 : fetch_word Plain.M.loaded_segments (0x5e404 : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e408 : bv 32 := 0x00357793.
Lemma F_5e408 : fetch_word Plain.M.loaded_segments (0x5e408 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e40c : bv 32 := 0xf2079ae3.
Lemma F_5e40c : fetch_word Plain.M.loaded_segments (0x5e40c : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e410 : bv 32 := 0x01000713.
Lemma F_5e410 : fetch_word Plain.M.loaded_segments (0x5e410 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e414 : bv 32 := 0x02e66c63.
Lemma F_5e414 : fetch_word Plain.M.loaded_segments (0x5e414 : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e418 : bv 32 := 0x00f00713.
Lemma F_5e418 : fetch_word Plain.M.loaded_segments (0x5e418 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e41c : bv 32 := 0x0005a783.
Lemma F_5e41c : fetch_word Plain.M.loaded_segments (0x5e41c : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e420 : bv 32 := 0x0045a803.
Lemma F_5e420 : fetch_word Plain.M.loaded_segments (0x5e420 : word) = Some W_5e420.
Proof. vm_refl. Qed.
Lemma D_5e420 : decode_any W_5e420 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e424 : bv 32 := 0x0085a883.
Lemma F_5e424 : fetch_word Plain.M.loaded_segments (0x5e424 : word) = Some W_5e424.
Proof. vm_refl. Qed.
Lemma D_5e424 : decode_any W_5e424 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e428 : bv 32 := 0x00c5a283.
Lemma F_5e428 : fetch_word Plain.M.loaded_segments (0x5e428 : word) = Some W_5e428.
Proof. vm_refl. Qed.
Lemma D_5e428 : decode_any W_5e428 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e42c : bv 32 := 0x01058593.
Lemma F_5e42c : fetch_word Plain.M.loaded_segments (0x5e42c : word) = Some W_5e42c.
Proof. vm_refl. Qed.
Lemma D_5e42c : decode_any W_5e42c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e430 : bv 32 := 0xff060613.
Lemma F_5e430 : fetch_word Plain.M.loaded_segments (0x5e430 : word) = Some W_5e430.
Proof. vm_refl. Qed.
Lemma D_5e430 : decode_any W_5e430 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e434 : bv 32 := 0x00f6a023.
Lemma F_5e434 : fetch_word Plain.M.loaded_segments (0x5e434 : word) = Some W_5e434.
Proof. vm_refl. Qed.
Lemma D_5e434 : decode_any W_5e434 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e438 : bv 32 := 0x0106a223.
Lemma F_5e438 : fetch_word Plain.M.loaded_segments (0x5e438 : word) = Some W_5e438.
Proof. vm_refl. Qed.
Lemma D_5e438 : decode_any W_5e438 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e43c : bv 32 := 0x0116a423.
Lemma F_5e43c : fetch_word Plain.M.loaded_segments (0x5e43c : word) = Some W_5e43c.
Proof. vm_refl. Qed.
Lemma D_5e43c : decode_any W_5e43c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e440 : bv 32 := 0x0056a623.
Lemma F_5e440 : fetch_word Plain.M.loaded_segments (0x5e440 : word) = Some W_5e440.
Proof. vm_refl. Qed.
Lemma D_5e440 : decode_any W_5e440 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e444 : bv 32 := 0x01068693.
Lemma F_5e444 : fetch_word Plain.M.loaded_segments (0x5e444 : word) = Some W_5e444.
Proof. vm_refl. Qed.
Lemma D_5e444 : decode_any W_5e444 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e448 : bv 32 := 0xfcc76ae3.
Lemma F_5e448 : fetch_word Plain.M.loaded_segments (0x5e448 : word) = Some W_5e448.
Proof. vm_refl. Qed.
Lemma D_5e448 : decode_any W_5e448 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e44c : bv 32 := 0x00800713.
Lemma F_5e44c : fetch_word Plain.M.loaded_segments (0x5e44c : word) = Some W_5e44c.
Proof. vm_refl. Qed.
Lemma D_5e44c : decode_any W_5e44c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e450 : bv 32 := 0x00e66e63.
Lemma F_5e450 : fetch_word Plain.M.loaded_segments (0x5e450 : word) = Some W_5e450.
Proof. vm_refl. Qed.
Lemma D_5e450 : decode_any W_5e450 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e454 : bv 32 := 0x0005a703.
Lemma F_5e454 : fetch_word Plain.M.loaded_segments (0x5e454 : word) = Some W_5e454.
Proof. vm_refl. Qed.
Lemma D_5e454 : decode_any W_5e454 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e458 : bv 32 := 0x0045a783.
Lemma F_5e458 : fetch_word Plain.M.loaded_segments (0x5e458 : word) = Some W_5e458.
Proof. vm_refl. Qed.
Lemma D_5e458 : decode_any W_5e458 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e45c : bv 32 := 0x00e6a023.
Lemma F_5e45c : fetch_word Plain.M.loaded_segments (0x5e45c : word) = Some W_5e45c.
Proof. vm_refl. Qed.
Lemma D_5e45c : decode_any W_5e45c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e460 : bv 32 := 0x00f6a223.
Lemma F_5e460 : fetch_word Plain.M.loaded_segments (0x5e460 : word) = Some W_5e460.
Proof. vm_refl. Qed.
Lemma D_5e460 : decode_any W_5e460 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e464 : bv 32 := 0x00868693.
Lemma F_5e464 : fetch_word Plain.M.loaded_segments (0x5e464 : word) = Some W_5e464.
Proof. vm_refl. Qed.
Lemma D_5e464 : decode_any W_5e464 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e468 : bv 32 := 0x00858593.
Lemma F_5e468 : fetch_word Plain.M.loaded_segments (0x5e468 : word) = Some W_5e468.
Proof. vm_refl. Qed.
Lemma D_5e468 : decode_any W_5e468 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e46c : bv 32 := 0x00467713.
Lemma F_5e46c : fetch_word Plain.M.loaded_segments (0x5e46c : word) = Some W_5e46c.
Proof. vm_refl. Qed.
Lemma D_5e46c : decode_any W_5e46c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e470 : bv 32 := 0x24070063.
Lemma F_5e470 : fetch_word Plain.M.loaded_segments (0x5e470 : word) = Some W_5e470.
Proof. vm_refl. Qed.
Lemma D_5e470 : decode_any W_5e470 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e474 : bv 32 := 0x0005a703.
Lemma F_5e474 : fetch_word Plain.M.loaded_segments (0x5e474 : word) = Some W_5e474.
Proof. vm_refl. Qed.
Lemma D_5e474 : decode_any W_5e474 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e478 : bv 32 := 0x00458593.
Lemma F_5e478 : fetch_word Plain.M.loaded_segments (0x5e478 : word) = Some W_5e478.
Proof. vm_refl. Qed.
Lemma D_5e478 : decode_any W_5e478 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e47c : bv 32 := 0x00e6a023.
Lemma F_5e47c : fetch_word Plain.M.loaded_segments (0x5e47c : word) = Some W_5e47c.
Proof. vm_refl. Qed.
Lemma D_5e47c : decode_any W_5e47c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e480 : bv 32 := 0x00468693.
Lemma F_5e480 : fetch_word Plain.M.loaded_segments (0x5e480 : word) = Some W_5e480.
Proof. vm_refl. Qed.
Lemma D_5e480 : decode_any W_5e480 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e484 : bv 32 := 0x22c0006f.
Lemma F_5e484 : fetch_word Plain.M.loaded_segments (0x5e484 : word) = Some W_5e484.
Proof. vm_refl. Qed.
Lemma D_5e484 : decode_any W_5e484 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e488 : bv 32 := 0x00e68023.
Lemma F_5e488 : fetch_word Plain.M.loaded_segments (0x5e488 : word) = Some W_5e488.
Proof. vm_refl. Qed.
Lemma D_5e488 : decode_any W_5e488 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e48c : bv 32 := 0x00168693.
Lemma F_5e48c : fetch_word Plain.M.loaded_segments (0x5e48c : word) = Some W_5e48c.
Proof. vm_refl. Qed.
Lemma D_5e48c : decode_any W_5e48c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e490 : bv 32 := 0xfff60613.
Lemma F_5e490 : fetch_word Plain.M.loaded_segments (0x5e490 : word) = Some W_5e490.
Proof. vm_refl. Qed.
Lemma D_5e490 : decode_any W_5e490 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e494 : bv 32 := 0x01058593.
Lemma F_5e494 : fetch_word Plain.M.loaded_segments (0x5e494 : word) = Some W_5e494.
Proof. vm_refl. Qed.
Lemma D_5e494 : decode_any W_5e494 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e498 : bv 32 := 0x01200793.
Lemma F_5e498 : fetch_word Plain.M.loaded_segments (0x5e498 : word) = Some W_5e498.
Proof. vm_refl. Qed.
Lemma D_5e498 : decode_any W_5e498 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e49c : bv 32 := 0x0087581b.
Lemma F_5e49c : fetch_word Plain.M.loaded_segments (0x5e49c : word) = Some W_5e49c.
Proof. vm_refl. Qed.
Lemma D_5e49c : decode_any W_5e49c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4a0 : bv 32 := 0xff45a883.
Lemma F_5e4a0 : fetch_word Plain.M.loaded_segments (0x5e4a0 : word) = Some W_5e4a0.
Proof. vm_refl. Qed.
Lemma D_5e4a0 : decode_any W_5e4a0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4a4 : bv 32 := 0xff85a283.
Lemma F_5e4a4 : fetch_word Plain.M.loaded_segments (0x5e4a4 : word) = Some W_5e4a4.
Proof. vm_refl. Qed.
Lemma D_5e4a4 : decode_any W_5e4a4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4a8 : bv 32 := 0xffc5a303.
Lemma F_5e4a8 : fetch_word Plain.M.loaded_segments (0x5e4a8 : word) = Some W_5e4a8.
Proof. vm_refl. Qed.
Lemma D_5e4a8 : decode_any W_5e4a8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4ac : bv 32 := 0x0005a703.
Lemma F_5e4ac : fetch_word Plain.M.loaded_segments (0x5e4ac : word) = Some W_5e4ac.
Proof. vm_refl. Qed.
Lemma D_5e4ac : decode_any W_5e4ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4b0 : bv 32 := 0x01889393.
Lemma F_5e4b0 : fetch_word Plain.M.loaded_segments (0x5e4b0 : word) = Some W_5e4b0.
Proof. vm_refl. Qed.
Lemma D_5e4b0 : decode_any W_5e4b0 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4b4 : bv 32 := 0x0088d89b.
Lemma F_5e4b4 : fetch_word Plain.M.loaded_segments (0x5e4b4 : word) = Some W_5e4b4.
Proof. vm_refl. Qed.
Lemma D_5e4b4 : decode_any W_5e4b4 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4b8 : bv 32 := 0x0103e833.
Lemma F_5e4b8 : fetch_word Plain.M.loaded_segments (0x5e4b8 : word) = Some W_5e4b8.
Proof. vm_refl. Qed.
Lemma D_5e4b8 : decode_any W_5e4b8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4bc : bv 32 := 0x01829393.
Lemma F_5e4bc : fetch_word Plain.M.loaded_segments (0x5e4bc : word) = Some W_5e4bc.
Proof. vm_refl. Qed.
Lemma D_5e4bc : decode_any W_5e4bc = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4c0 : bv 32 := 0x0082d29b.
Lemma F_5e4c0 : fetch_word Plain.M.loaded_segments (0x5e4c0 : word) = Some W_5e4c0.
Proof. vm_refl. Qed.
Lemma D_5e4c0 : decode_any W_5e4c0 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4c4 : bv 32 := 0x0113e8b3.
Lemma F_5e4c4 : fetch_word Plain.M.loaded_segments (0x5e4c4 : word) = Some W_5e4c4.
Proof. vm_refl. Qed.
Lemma D_5e4c4 : decode_any W_5e4c4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4c8 : bv 32 := 0x01831393.
Lemma F_5e4c8 : fetch_word Plain.M.loaded_segments (0x5e4c8 : word) = Some W_5e4c8.
Proof. vm_refl. Qed.
Lemma D_5e4c8 : decode_any W_5e4c8 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4cc : bv 32 := 0x0083531b.
Lemma F_5e4cc : fetch_word Plain.M.loaded_segments (0x5e4cc : word) = Some W_5e4cc.
Proof. vm_refl. Qed.
Lemma D_5e4cc : decode_any W_5e4cc = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4d0 : bv 32 := 0x0053e2b3.
Lemma F_5e4d0 : fetch_word Plain.M.loaded_segments (0x5e4d0 : word) = Some W_5e4d0.
Proof. vm_refl. Qed.
Lemma D_5e4d0 : decode_any W_5e4d0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4d4 : bv 32 := 0x01871393.
Lemma F_5e4d4 : fetch_word Plain.M.loaded_segments (0x5e4d4 : word) = Some W_5e4d4.
Proof. vm_refl. Qed.
Lemma D_5e4d4 : decode_any W_5e4d4 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4d8 : bv 32 := 0x0063e333.
Lemma F_5e4d8 : fetch_word Plain.M.loaded_segments (0x5e4d8 : word) = Some W_5e4d8.
Proof. vm_refl. Qed.
Lemma D_5e4d8 : decode_any W_5e4d8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4dc : bv 32 := 0xff060613.
Lemma F_5e4dc : fetch_word Plain.M.loaded_segments (0x5e4dc : word) = Some W_5e4dc.
Proof. vm_refl. Qed.
Lemma D_5e4dc : decode_any W_5e4dc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4e0 : bv 32 := 0x0106a023.
Lemma F_5e4e0 : fetch_word Plain.M.loaded_segments (0x5e4e0 : word) = Some W_5e4e0.
Proof. vm_refl. Qed.
Lemma D_5e4e0 : decode_any W_5e4e0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4e4 : bv 32 := 0x0116a223.
Lemma F_5e4e4 : fetch_word Plain.M.loaded_segments (0x5e4e4 : word) = Some W_5e4e4.
Proof. vm_refl. Qed.
Lemma D_5e4e4 : decode_any W_5e4e4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4e8 : bv 32 := 0x0056a423.
Lemma F_5e4e8 : fetch_word Plain.M.loaded_segments (0x5e4e8 : word) = Some W_5e4e8.
Proof. vm_refl. Qed.
Lemma D_5e4e8 : decode_any W_5e4e8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4ec : bv 32 := 0x0066a623.
Lemma F_5e4ec : fetch_word Plain.M.loaded_segments (0x5e4ec : word) = Some W_5e4ec.
Proof. vm_refl. Qed.
Lemma D_5e4ec : decode_any W_5e4ec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4f0 : bv 32 := 0x01068693.
Lemma F_5e4f0 : fetch_word Plain.M.loaded_segments (0x5e4f0 : word) = Some W_5e4f0.
Proof. vm_refl. Qed.
Lemma D_5e4f0 : decode_any W_5e4f0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4f4 : bv 32 := 0x01058593.
Lemma F_5e4f4 : fetch_word Plain.M.loaded_segments (0x5e4f4 : word) = Some W_5e4f4.
Proof. vm_refl. Qed.
Lemma D_5e4f4 : decode_any W_5e4f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4f8 : bv 32 := 0xfac7e2e3.
Lemma F_5e4f8 : fetch_word Plain.M.loaded_segments (0x5e4f8 : word) = Some W_5e4f8.
Proof. vm_refl. Qed.
Lemma D_5e4f8 : decode_any W_5e4f8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e4fc : bv 32 := 0xff158593.
Lemma F_5e4fc : fetch_word Plain.M.loaded_segments (0x5e4fc : word) = Some W_5e4fc.
Proof. vm_refl. Qed.
Lemma D_5e4fc : decode_any W_5e4fc = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e500 : bv 32 := 0x01000713.
Lemma F_5e500 : fetch_word Plain.M.loaded_segments (0x5e500 : word) = Some W_5e500.
Proof. vm_refl. Qed.
Lemma D_5e500 : decode_any W_5e500 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e504 : bv 32 := 0xe4e666e3.
Lemma F_5e504 : fetch_word Plain.M.loaded_segments (0x5e504 : word) = Some W_5e504.
Proof. vm_refl. Qed.
Lemma D_5e504 : decode_any W_5e504 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e508 : bv 32 := 0x0940006f.
Lemma F_5e508 : fetch_word Plain.M.loaded_segments (0x5e508 : word) = Some W_5e508.
Proof. vm_refl. Qed.
Lemma D_5e508 : decode_any W_5e508 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e50c : bv 32 := 0x00875793.
Lemma F_5e50c : fetch_word Plain.M.loaded_segments (0x5e50c : word) = Some W_5e50c.
Proof. vm_refl. Qed.
Lemma D_5e50c : decode_any W_5e50c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e510 : bv 32 := 0x01075813.
Lemma F_5e510 : fetch_word Plain.M.loaded_segments (0x5e510 : word) = Some W_5e510.
Proof. vm_refl. Qed.
Lemma D_5e510 : decode_any W_5e510 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e514 : bv 32 := 0xffd60613.
Lemma F_5e514 : fetch_word Plain.M.loaded_segments (0x5e514 : word) = Some W_5e514.
Proof. vm_refl. Qed.
Lemma D_5e514 : decode_any W_5e514 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e518 : bv 32 := 0x00e68023.
Lemma F_5e518 : fetch_word Plain.M.loaded_segments (0x5e518 : word) = Some W_5e518.
Proof. vm_refl. Qed.
Lemma D_5e518 : decode_any W_5e518 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e51c : bv 32 := 0x00f680a3.
Lemma F_5e51c : fetch_word Plain.M.loaded_segments (0x5e51c : word) = Some W_5e51c.
Proof. vm_refl. Qed.
Lemma D_5e51c : decode_any W_5e51c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e520 : bv 32 := 0x01068123.
Lemma F_5e520 : fetch_word Plain.M.loaded_segments (0x5e520 : word) = Some W_5e520.
Proof. vm_refl. Qed.
Lemma D_5e520 : decode_any W_5e520 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e524 : bv 32 := 0x00368693.
Lemma F_5e524 : fetch_word Plain.M.loaded_segments (0x5e524 : word) = Some W_5e524.
Proof. vm_refl. Qed.
Lemma D_5e524 : decode_any W_5e524 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e528 : bv 32 := 0x01058593.
Lemma F_5e528 : fetch_word Plain.M.loaded_segments (0x5e528 : word) = Some W_5e528.
Proof. vm_refl. Qed.
Lemma D_5e528 : decode_any W_5e528 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e52c : bv 32 := 0x01000793.
Lemma F_5e52c : fetch_word Plain.M.loaded_segments (0x5e52c : word) = Some W_5e52c.
Proof. vm_refl. Qed.
Lemma D_5e52c : decode_any W_5e52c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e530 : bv 32 := 0x0187581b.
Lemma F_5e530 : fetch_word Plain.M.loaded_segments (0x5e530 : word) = Some W_5e530.
Proof. vm_refl. Qed.
Lemma D_5e530 : decode_any W_5e530 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e534 : bv 32 := 0xff45a883.
Lemma F_5e534 : fetch_word Plain.M.loaded_segments (0x5e534 : word) = Some W_5e534.
Proof. vm_refl. Qed.
Lemma D_5e534 : decode_any W_5e534 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e538 : bv 32 := 0xff85a283.
Lemma F_5e538 : fetch_word Plain.M.loaded_segments (0x5e538 : word) = Some W_5e538.
Proof. vm_refl. Qed.
Lemma D_5e538 : decode_any W_5e538 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e53c : bv 32 := 0xffc5a303.
Lemma F_5e53c : fetch_word Plain.M.loaded_segments (0x5e53c : word) = Some W_5e53c.
Proof. vm_refl. Qed.
Lemma D_5e53c : decode_any W_5e53c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e540 : bv 32 := 0x0005a703.
Lemma F_5e540 : fetch_word Plain.M.loaded_segments (0x5e540 : word) = Some W_5e540.
Proof. vm_refl. Qed.
Lemma D_5e540 : decode_any W_5e540 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e544 : bv 32 := 0x00889393.
Lemma F_5e544 : fetch_word Plain.M.loaded_segments (0x5e544 : word) = Some W_5e544.
Proof. vm_refl. Qed.
Lemma D_5e544 : decode_any W_5e544 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e548 : bv 32 := 0x0188d89b.
Lemma F_5e548 : fetch_word Plain.M.loaded_segments (0x5e548 : word) = Some W_5e548.
Proof. vm_refl. Qed.
Lemma D_5e548 : decode_any W_5e548 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e54c : bv 32 := 0x0103e833.
Lemma F_5e54c : fetch_word Plain.M.loaded_segments (0x5e54c : word) = Some W_5e54c.
Proof. vm_refl. Qed.
Lemma D_5e54c : decode_any W_5e54c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e550 : bv 32 := 0x00829393.
Lemma F_5e550 : fetch_word Plain.M.loaded_segments (0x5e550 : word) = Some W_5e550.
Proof. vm_refl. Qed.
Lemma D_5e550 : decode_any W_5e550 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e554 : bv 32 := 0x0182d29b.
Lemma F_5e554 : fetch_word Plain.M.loaded_segments (0x5e554 : word) = Some W_5e554.
Proof. vm_refl. Qed.
Lemma D_5e554 : decode_any W_5e554 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e558 : bv 32 := 0x0113e8b3.
Lemma F_5e558 : fetch_word Plain.M.loaded_segments (0x5e558 : word) = Some W_5e558.
Proof. vm_refl. Qed.
Lemma D_5e558 : decode_any W_5e558 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e55c : bv 32 := 0x00831393.
Lemma F_5e55c : fetch_word Plain.M.loaded_segments (0x5e55c : word) = Some W_5e55c.
Proof. vm_refl. Qed.
Lemma D_5e55c : decode_any W_5e55c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e560 : bv 32 := 0x0183531b.
Lemma F_5e560 : fetch_word Plain.M.loaded_segments (0x5e560 : word) = Some W_5e560.
Proof. vm_refl. Qed.
Lemma D_5e560 : decode_any W_5e560 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e564 : bv 32 := 0x0053e2b3.
Lemma F_5e564 : fetch_word Plain.M.loaded_segments (0x5e564 : word) = Some W_5e564.
Proof. vm_refl. Qed.
Lemma D_5e564 : decode_any W_5e564 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e568 : bv 32 := 0x00871393.
Lemma F_5e568 : fetch_word Plain.M.loaded_segments (0x5e568 : word) = Some W_5e568.
Proof. vm_refl. Qed.
Lemma D_5e568 : decode_any W_5e568 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e56c : bv 32 := 0x0063e333.
Lemma F_5e56c : fetch_word Plain.M.loaded_segments (0x5e56c : word) = Some W_5e56c.
Proof. vm_refl. Qed.
Lemma D_5e56c : decode_any W_5e56c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e570 : bv 32 := 0xff060613.
Lemma F_5e570 : fetch_word Plain.M.loaded_segments (0x5e570 : word) = Some W_5e570.
Proof. vm_refl. Qed.
Lemma D_5e570 : decode_any W_5e570 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e574 : bv 32 := 0x0106a023.
Lemma F_5e574 : fetch_word Plain.M.loaded_segments (0x5e574 : word) = Some W_5e574.
Proof. vm_refl. Qed.
Lemma D_5e574 : decode_any W_5e574 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e578 : bv 32 := 0x0116a223.
Lemma F_5e578 : fetch_word Plain.M.loaded_segments (0x5e578 : word) = Some W_5e578.
Proof. vm_refl. Qed.
Lemma D_5e578 : decode_any W_5e578 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e57c : bv 32 := 0x0056a423.
Lemma F_5e57c : fetch_word Plain.M.loaded_segments (0x5e57c : word) = Some W_5e57c.
Proof. vm_refl. Qed.
Lemma D_5e57c : decode_any W_5e57c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e580 : bv 32 := 0x0066a623.
Lemma F_5e580 : fetch_word Plain.M.loaded_segments (0x5e580 : word) = Some W_5e580.
Proof. vm_refl. Qed.
Lemma D_5e580 : decode_any W_5e580 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e584 : bv 32 := 0x01068693.
Lemma F_5e584 : fetch_word Plain.M.loaded_segments (0x5e584 : word) = Some W_5e584.
Proof. vm_refl. Qed.
Lemma D_5e584 : decode_any W_5e584 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e588 : bv 32 := 0x01058593.
Lemma F_5e588 : fetch_word Plain.M.loaded_segments (0x5e588 : word) = Some W_5e588.
Proof. vm_refl. Qed.
Lemma D_5e588 : decode_any W_5e588 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e58c : bv 32 := 0xfac7e2e3.
Lemma F_5e58c : fetch_word Plain.M.loaded_segments (0x5e58c : word) = Some W_5e58c.
Proof. vm_refl. Qed.
Lemma D_5e58c : decode_any W_5e58c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e590 : bv 32 := 0xff358593.
Lemma F_5e590 : fetch_word Plain.M.loaded_segments (0x5e590 : word) = Some W_5e590.
Proof. vm_refl. Qed.
Lemma D_5e590 : decode_any W_5e590 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e594 : bv 32 := 0x01000713.
Lemma F_5e594 : fetch_word Plain.M.loaded_segments (0x5e594 : word) = Some W_5e594.
Proof. vm_refl. Qed.
Lemma D_5e594 : decode_any W_5e594 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e598 : bv 32 := 0xdae66ce3.
Lemma F_5e598 : fetch_word Plain.M.loaded_segments (0x5e598 : word) = Some W_5e598.
Proof. vm_refl. Qed.
Lemma D_5e598 : decode_any W_5e598 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e59c : bv 32 := 0x0005c703.
Lemma F_5e59c : fetch_word Plain.M.loaded_segments (0x5e59c : word) = Some W_5e59c.
Proof. vm_refl. Qed.
Lemma D_5e59c : decode_any W_5e59c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5a0 : bv 32 := 0x0015c783.
Lemma F_5e5a0 : fetch_word Plain.M.loaded_segments (0x5e5a0 : word) = Some W_5e5a0.
Proof. vm_refl. Qed.
Lemma D_5e5a0 : decode_any W_5e5a0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5a4 : bv 32 := 0x0025c803.
Lemma F_5e5a4 : fetch_word Plain.M.loaded_segments (0x5e5a4 : word) = Some W_5e5a4.
Proof. vm_refl. Qed.
Lemma D_5e5a4 : decode_any W_5e5a4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5a8 : bv 32 := 0x0035c883.
Lemma F_5e5a8 : fetch_word Plain.M.loaded_segments (0x5e5a8 : word) = Some W_5e5a8.
Proof. vm_refl. Qed.
Lemma D_5e5a8 : decode_any W_5e5a8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5ac : bv 32 := 0x0045c283.
Lemma F_5e5ac : fetch_word Plain.M.loaded_segments (0x5e5ac : word) = Some W_5e5ac.
Proof. vm_refl. Qed.
Lemma D_5e5ac : decode_any W_5e5ac = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5b0 : bv 32 := 0x0055c303.
Lemma F_5e5b0 : fetch_word Plain.M.loaded_segments (0x5e5b0 : word) = Some W_5e5b0.
Proof. vm_refl. Qed.
Lemma D_5e5b0 : decode_any W_5e5b0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5b4 : bv 32 := 0x0065c383.
Lemma F_5e5b4 : fetch_word Plain.M.loaded_segments (0x5e5b4 : word) = Some W_5e5b4.
Proof. vm_refl. Qed.
Lemma D_5e5b4 : decode_any W_5e5b4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5b8 : bv 32 := 0x0075ce03.
Lemma F_5e5b8 : fetch_word Plain.M.loaded_segments (0x5e5b8 : word) = Some W_5e5b8.
Proof. vm_refl. Qed.
Lemma D_5e5b8 : decode_any W_5e5b8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5bc : bv 32 := 0x00e68023.
Lemma F_5e5bc : fetch_word Plain.M.loaded_segments (0x5e5bc : word) = Some W_5e5bc.
Proof. vm_refl. Qed.
Lemma D_5e5bc : decode_any W_5e5bc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5c0 : bv 32 := 0x00f680a3.
Lemma F_5e5c0 : fetch_word Plain.M.loaded_segments (0x5e5c0 : word) = Some W_5e5c0.
Proof. vm_refl. Qed.
Lemma D_5e5c0 : decode_any W_5e5c0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5c4 : bv 32 := 0x01068123.
Lemma F_5e5c4 : fetch_word Plain.M.loaded_segments (0x5e5c4 : word) = Some W_5e5c4.
Proof. vm_refl. Qed.
Lemma D_5e5c4 : decode_any W_5e5c4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5c8 : bv 32 := 0x011681a3.
Lemma F_5e5c8 : fetch_word Plain.M.loaded_segments (0x5e5c8 : word) = Some W_5e5c8.
Proof. vm_refl. Qed.
Lemma D_5e5c8 : decode_any W_5e5c8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5cc : bv 32 := 0x0085c703.
Lemma F_5e5cc : fetch_word Plain.M.loaded_segments (0x5e5cc : word) = Some W_5e5cc.
Proof. vm_refl. Qed.
Lemma D_5e5cc : decode_any W_5e5cc = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5d0 : bv 32 := 0x0095c783.
Lemma F_5e5d0 : fetch_word Plain.M.loaded_segments (0x5e5d0 : word) = Some W_5e5d0.
Proof. vm_refl. Qed.
Lemma D_5e5d0 : decode_any W_5e5d0 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5d4 : bv 32 := 0x00a5c803.
Lemma F_5e5d4 : fetch_word Plain.M.loaded_segments (0x5e5d4 : word) = Some W_5e5d4.
Proof. vm_refl. Qed.
Lemma D_5e5d4 : decode_any W_5e5d4 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5d8 : bv 32 := 0x00b5c883.
Lemma F_5e5d8 : fetch_word Plain.M.loaded_segments (0x5e5d8 : word) = Some W_5e5d8.
Proof. vm_refl. Qed.
Lemma D_5e5d8 : decode_any W_5e5d8 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5dc : bv 32 := 0x00568223.
Lemma F_5e5dc : fetch_word Plain.M.loaded_segments (0x5e5dc : word) = Some W_5e5dc.
Proof. vm_refl. Qed.
Lemma D_5e5dc : decode_any W_5e5dc = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5e0 : bv 32 := 0x006682a3.
Lemma F_5e5e0 : fetch_word Plain.M.loaded_segments (0x5e5e0 : word) = Some W_5e5e0.
Proof. vm_refl. Qed.
Lemma D_5e5e0 : decode_any W_5e5e0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5e4 : bv 32 := 0x00768323.
Lemma F_5e5e4 : fetch_word Plain.M.loaded_segments (0x5e5e4 : word) = Some W_5e5e4.
Proof. vm_refl. Qed.
Lemma D_5e5e4 : decode_any W_5e5e4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5e8 : bv 32 := 0x01c683a3.
Lemma F_5e5e8 : fetch_word Plain.M.loaded_segments (0x5e5e8 : word) = Some W_5e5e8.
Proof. vm_refl. Qed.
Lemma D_5e5e8 : decode_any W_5e5e8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5ec : bv 32 := 0x00c5c283.
Lemma F_5e5ec : fetch_word Plain.M.loaded_segments (0x5e5ec : word) = Some W_5e5ec.
Proof. vm_refl. Qed.
Lemma D_5e5ec : decode_any W_5e5ec = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5f0 : bv 32 := 0x00d5c303.
Lemma F_5e5f0 : fetch_word Plain.M.loaded_segments (0x5e5f0 : word) = Some W_5e5f0.
Proof. vm_refl. Qed.
Lemma D_5e5f0 : decode_any W_5e5f0 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5f4 : bv 32 := 0x00e5c383.
Lemma F_5e5f4 : fetch_word Plain.M.loaded_segments (0x5e5f4 : word) = Some W_5e5f4.
Proof. vm_refl. Qed.
Lemma D_5e5f4 : decode_any W_5e5f4 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5f8 : bv 32 := 0x00f5ce03.
Lemma F_5e5f8 : fetch_word Plain.M.loaded_segments (0x5e5f8 : word) = Some W_5e5f8.
Proof. vm_refl. Qed.
Lemma D_5e5f8 : decode_any W_5e5f8 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e5fc : bv 32 := 0x01058593.
Lemma F_5e5fc : fetch_word Plain.M.loaded_segments (0x5e5fc : word) = Some W_5e5fc.
Proof. vm_refl. Qed.
Lemma D_5e5fc : decode_any W_5e5fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e600 : bv 32 := 0x00e68423.
Lemma F_5e600 : fetch_word Plain.M.loaded_segments (0x5e600 : word) = Some W_5e600.
Proof. vm_refl. Qed.
Lemma D_5e600 : decode_any W_5e600 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e604 : bv 32 := 0x00f684a3.
Lemma F_5e604 : fetch_word Plain.M.loaded_segments (0x5e604 : word) = Some W_5e604.
Proof. vm_refl. Qed.
Lemma D_5e604 : decode_any W_5e604 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e608 : bv 32 := 0x01068523.
Lemma F_5e608 : fetch_word Plain.M.loaded_segments (0x5e608 : word) = Some W_5e608.
Proof. vm_refl. Qed.
Lemma D_5e608 : decode_any W_5e608 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e60c : bv 32 := 0x011685a3.
Lemma F_5e60c : fetch_word Plain.M.loaded_segments (0x5e60c : word) = Some W_5e60c.
Proof. vm_refl. Qed.
Lemma D_5e60c : decode_any W_5e60c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e610 : bv 32 := 0x01068713.
Lemma F_5e610 : fetch_word Plain.M.loaded_segments (0x5e610 : word) = Some W_5e610.
Proof. vm_refl. Qed.
Lemma D_5e610 : decode_any W_5e610 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e614 : bv 32 := 0x00568623.
Lemma F_5e614 : fetch_word Plain.M.loaded_segments (0x5e614 : word) = Some W_5e614.
Proof. vm_refl. Qed.
Lemma D_5e614 : decode_any W_5e614 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e618 : bv 32 := 0x006686a3.
Lemma F_5e618 : fetch_word Plain.M.loaded_segments (0x5e618 : word) = Some W_5e618.
Proof. vm_refl. Qed.
Lemma D_5e618 : decode_any W_5e618 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e61c : bv 32 := 0x00768723.
Lemma F_5e61c : fetch_word Plain.M.loaded_segments (0x5e61c : word) = Some W_5e61c.
Proof. vm_refl. Qed.
Lemma D_5e61c : decode_any W_5e61c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e620 : bv 32 := 0x01c687a3.
Lemma F_5e620 : fetch_word Plain.M.loaded_segments (0x5e620 : word) = Some W_5e620.
Proof. vm_refl. Qed.
Lemma D_5e620 : decode_any W_5e620 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e624 : bv 32 := 0x00070693.
Lemma F_5e624 : fetch_word Plain.M.loaded_segments (0x5e624 : word) = Some W_5e624.
Proof. vm_refl. Qed.
Lemma D_5e624 : decode_any W_5e624 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e628 : bv 32 := 0x00867713.
Lemma F_5e628 : fetch_word Plain.M.loaded_segments (0x5e628 : word) = Some W_5e628.
Proof. vm_refl. Qed.
Lemma D_5e628 : decode_any W_5e628 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e62c : bv 32 := 0xd20706e3.
Lemma F_5e62c : fetch_word Plain.M.loaded_segments (0x5e62c : word) = Some W_5e62c.
Proof. vm_refl. Qed.
Lemma D_5e62c : decode_any W_5e62c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e630 : bv 32 := 0x0005c703.
Lemma F_5e630 : fetch_word Plain.M.loaded_segments (0x5e630 : word) = Some W_5e630.
Proof. vm_refl. Qed.
Lemma D_5e630 : decode_any W_5e630 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e634 : bv 32 := 0x0015c783.
Lemma F_5e634 : fetch_word Plain.M.loaded_segments (0x5e634 : word) = Some W_5e634.
Proof. vm_refl. Qed.
Lemma D_5e634 : decode_any W_5e634 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e638 : bv 32 := 0x0025c803.
Lemma F_5e638 : fetch_word Plain.M.loaded_segments (0x5e638 : word) = Some W_5e638.
Proof. vm_refl. Qed.
Lemma D_5e638 : decode_any W_5e638 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e63c : bv 32 := 0x0035c883.
Lemma F_5e63c : fetch_word Plain.M.loaded_segments (0x5e63c : word) = Some W_5e63c.
Proof. vm_refl. Qed.
Lemma D_5e63c : decode_any W_5e63c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e640 : bv 32 := 0x0045c283.
Lemma F_5e640 : fetch_word Plain.M.loaded_segments (0x5e640 : word) = Some W_5e640.
Proof. vm_refl. Qed.
Lemma D_5e640 : decode_any W_5e640 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e644 : bv 32 := 0x0055c303.
Lemma F_5e644 : fetch_word Plain.M.loaded_segments (0x5e644 : word) = Some W_5e644.
Proof. vm_refl. Qed.
Lemma D_5e644 : decode_any W_5e644 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e648 : bv 32 := 0x0065c383.
Lemma F_5e648 : fetch_word Plain.M.loaded_segments (0x5e648 : word) = Some W_5e648.
Proof. vm_refl. Qed.
Lemma D_5e648 : decode_any W_5e648 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e64c : bv 32 := 0x0075ce03.
Lemma F_5e64c : fetch_word Plain.M.loaded_segments (0x5e64c : word) = Some W_5e64c.
Proof. vm_refl. Qed.
Lemma D_5e64c : decode_any W_5e64c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e650 : bv 32 := 0x00858593.
Lemma F_5e650 : fetch_word Plain.M.loaded_segments (0x5e650 : word) = Some W_5e650.
Proof. vm_refl. Qed.
Lemma D_5e650 : decode_any W_5e650 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e654 : bv 32 := 0x00e68023.
Lemma F_5e654 : fetch_word Plain.M.loaded_segments (0x5e654 : word) = Some W_5e654.
Proof. vm_refl. Qed.
Lemma D_5e654 : decode_any W_5e654 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e658 : bv 32 := 0x00f680a3.
Lemma F_5e658 : fetch_word Plain.M.loaded_segments (0x5e658 : word) = Some W_5e658.
Proof. vm_refl. Qed.
Lemma D_5e658 : decode_any W_5e658 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e65c : bv 32 := 0x01068123.
Lemma F_5e65c : fetch_word Plain.M.loaded_segments (0x5e65c : word) = Some W_5e65c.
Proof. vm_refl. Qed.
Lemma D_5e65c : decode_any W_5e65c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e660 : bv 32 := 0x011681a3.
Lemma F_5e660 : fetch_word Plain.M.loaded_segments (0x5e660 : word) = Some W_5e660.
Proof. vm_refl. Qed.
Lemma D_5e660 : decode_any W_5e660 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e664 : bv 32 := 0x00868713.
Lemma F_5e664 : fetch_word Plain.M.loaded_segments (0x5e664 : word) = Some W_5e664.
Proof. vm_refl. Qed.
Lemma D_5e664 : decode_any W_5e664 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e668 : bv 32 := 0x00568223.
Lemma F_5e668 : fetch_word Plain.M.loaded_segments (0x5e668 : word) = Some W_5e668.
Proof. vm_refl. Qed.
Lemma D_5e668 : decode_any W_5e668 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e66c : bv 32 := 0x006682a3.
Lemma F_5e66c : fetch_word Plain.M.loaded_segments (0x5e66c : word) = Some W_5e66c.
Proof. vm_refl. Qed.
Lemma D_5e66c : decode_any W_5e66c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e670 : bv 32 := 0x00768323.
Lemma F_5e670 : fetch_word Plain.M.loaded_segments (0x5e670 : word) = Some W_5e670.
Proof. vm_refl. Qed.
Lemma D_5e670 : decode_any W_5e670 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e674 : bv 32 := 0x01c683a3.
Lemma F_5e674 : fetch_word Plain.M.loaded_segments (0x5e674 : word) = Some W_5e674.
Proof. vm_refl. Qed.
Lemma D_5e674 : decode_any W_5e674 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e678 : bv 32 := 0x00070693.
Lemma F_5e678 : fetch_word Plain.M.loaded_segments (0x5e678 : word) = Some W_5e678.
Proof. vm_refl. Qed.
Lemma D_5e678 : decode_any W_5e678 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e67c : bv 32 := 0x00467713.
Lemma F_5e67c : fetch_word Plain.M.loaded_segments (0x5e67c : word) = Some W_5e67c.
Proof. vm_refl. Qed.
Lemma D_5e67c : decode_any W_5e67c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e680 : bv 32 := 0x02070863.
Lemma F_5e680 : fetch_word Plain.M.loaded_segments (0x5e680 : word) = Some W_5e680.
Proof. vm_refl. Qed.
Lemma D_5e680 : decode_any W_5e680 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e684 : bv 32 := 0x0005c703.
Lemma F_5e684 : fetch_word Plain.M.loaded_segments (0x5e684 : word) = Some W_5e684.
Proof. vm_refl. Qed.
Lemma D_5e684 : decode_any W_5e684 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e688 : bv 32 := 0x0015c783.
Lemma F_5e688 : fetch_word Plain.M.loaded_segments (0x5e688 : word) = Some W_5e688.
Proof. vm_refl. Qed.
Lemma D_5e688 : decode_any W_5e688 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e68c : bv 32 := 0x0025c803.
Lemma F_5e68c : fetch_word Plain.M.loaded_segments (0x5e68c : word) = Some W_5e68c.
Proof. vm_refl. Qed.
Lemma D_5e68c : decode_any W_5e68c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e690 : bv 32 := 0x0035c883.
Lemma F_5e690 : fetch_word Plain.M.loaded_segments (0x5e690 : word) = Some W_5e690.
Proof. vm_refl. Qed.
Lemma D_5e690 : decode_any W_5e690 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e694 : bv 32 := 0x00458593.
Lemma F_5e694 : fetch_word Plain.M.loaded_segments (0x5e694 : word) = Some W_5e694.
Proof. vm_refl. Qed.
Lemma D_5e694 : decode_any W_5e694 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e698 : bv 32 := 0x00468293.
Lemma F_5e698 : fetch_word Plain.M.loaded_segments (0x5e698 : word) = Some W_5e698.
Proof. vm_refl. Qed.
Lemma D_5e698 : decode_any W_5e698 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e69c : bv 32 := 0x00e68023.
Lemma F_5e69c : fetch_word Plain.M.loaded_segments (0x5e69c : word) = Some W_5e69c.
Proof. vm_refl. Qed.
Lemma D_5e69c : decode_any W_5e69c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6a0 : bv 32 := 0x00f680a3.
Lemma F_5e6a0 : fetch_word Plain.M.loaded_segments (0x5e6a0 : word) = Some W_5e6a0.
Proof. vm_refl. Qed.
Lemma D_5e6a0 : decode_any W_5e6a0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6a4 : bv 32 := 0x01068123.
Lemma F_5e6a4 : fetch_word Plain.M.loaded_segments (0x5e6a4 : word) = Some W_5e6a4.
Proof. vm_refl. Qed.
Lemma D_5e6a4 : decode_any W_5e6a4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6a8 : bv 32 := 0x011681a3.
Lemma F_5e6a8 : fetch_word Plain.M.loaded_segments (0x5e6a8 : word) = Some W_5e6a8.
Proof. vm_refl. Qed.
Lemma D_5e6a8 : decode_any W_5e6a8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6ac : bv 32 := 0x00028693.
Lemma F_5e6ac : fetch_word Plain.M.loaded_segments (0x5e6ac : word) = Some W_5e6ac.
Proof. vm_refl. Qed.
Lemma D_5e6ac : decode_any W_5e6ac = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6b0 : bv 32 := 0x00267713.
Lemma F_5e6b0 : fetch_word Plain.M.loaded_segments (0x5e6b0 : word) = Some W_5e6b0.
Proof. vm_refl. Qed.
Lemma D_5e6b0 : decode_any W_5e6b0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6b4 : bv 32 := 0x00071863.
Lemma F_5e6b4 : fetch_word Plain.M.loaded_segments (0x5e6b4 : word) = Some W_5e6b4.
Proof. vm_refl. Qed.
Lemma D_5e6b4 : decode_any W_5e6b4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6b8 : bv 32 := 0x00167613.
Lemma F_5e6b8 : fetch_word Plain.M.loaded_segments (0x5e6b8 : word) = Some W_5e6b8.
Proof. vm_refl. Qed.
Lemma D_5e6b8 : decode_any W_5e6b8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6bc : bv 32 := 0x02061663.
Lemma F_5e6bc : fetch_word Plain.M.loaded_segments (0x5e6bc : word) = Some W_5e6bc.
Proof. vm_refl. Qed.
Lemma D_5e6bc : decode_any W_5e6bc = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6c0 : bv 32 := 0x00008067.
Lemma F_5e6c0 : fetch_word Plain.M.loaded_segments (0x5e6c0 : word) = Some W_5e6c0.
Proof. vm_refl. Qed.
Lemma D_5e6c0 : decode_any W_5e6c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6c4 : bv 32 := 0x0005c703.
Lemma F_5e6c4 : fetch_word Plain.M.loaded_segments (0x5e6c4 : word) = Some W_5e6c4.
Proof. vm_refl. Qed.
Lemma D_5e6c4 : decode_any W_5e6c4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6c8 : bv 32 := 0x0015c783.
Lemma F_5e6c8 : fetch_word Plain.M.loaded_segments (0x5e6c8 : word) = Some W_5e6c8.
Proof. vm_refl. Qed.
Lemma D_5e6c8 : decode_any W_5e6c8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6cc : bv 32 := 0x00258593.
Lemma F_5e6cc : fetch_word Plain.M.loaded_segments (0x5e6cc : word) = Some W_5e6cc.
Proof. vm_refl. Qed.
Lemma D_5e6cc : decode_any W_5e6cc = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6d0 : bv 32 := 0x00268813.
Lemma F_5e6d0 : fetch_word Plain.M.loaded_segments (0x5e6d0 : word) = Some W_5e6d0.
Proof. vm_refl. Qed.
Lemma D_5e6d0 : decode_any W_5e6d0 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6d4 : bv 32 := 0x00e68023.
Lemma F_5e6d4 : fetch_word Plain.M.loaded_segments (0x5e6d4 : word) = Some W_5e6d4.
Proof. vm_refl. Qed.
Lemma D_5e6d4 : decode_any W_5e6d4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6d8 : bv 32 := 0x00f680a3.
Lemma F_5e6d8 : fetch_word Plain.M.loaded_segments (0x5e6d8 : word) = Some W_5e6d8.
Proof. vm_refl. Qed.
Lemma D_5e6d8 : decode_any W_5e6d8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6dc : bv 32 := 0x00080693.
Lemma F_5e6dc : fetch_word Plain.M.loaded_segments (0x5e6dc : word) = Some W_5e6dc.
Proof. vm_refl. Qed.
Lemma D_5e6dc : decode_any W_5e6dc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6e0 : bv 32 := 0x00167613.
Lemma F_5e6e0 : fetch_word Plain.M.loaded_segments (0x5e6e0 : word) = Some W_5e6e0.
Proof. vm_refl. Qed.
Lemma D_5e6e0 : decode_any W_5e6e0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6e4 : bv 32 := 0xfc060ee3.
Lemma F_5e6e4 : fetch_word Plain.M.loaded_segments (0x5e6e4 : word) = Some W_5e6e4.
Proof. vm_refl. Qed.
Lemma D_5e6e4 : decode_any W_5e6e4 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6e8 : bv 32 := 0x0005c583.
Lemma F_5e6e8 : fetch_word Plain.M.loaded_segments (0x5e6e8 : word) = Some W_5e6e8.
Proof. vm_refl. Qed.
Lemma D_5e6e8 : decode_any W_5e6e8 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6ec : bv 32 := 0x00b68023.
Lemma F_5e6ec : fetch_word Plain.M.loaded_segments (0x5e6ec : word) = Some W_5e6ec.
Proof. vm_refl. Qed.
Lemma D_5e6ec : decode_any W_5e6ec = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e6f0 : bv 32 := 0x00008067.
Lemma F_5e6f0 : fetch_word Plain.M.loaded_segments (0x5e6f0 : word) = Some W_5e6f0.
Proof. vm_refl. Qed.
Lemma D_5e6f0 : decode_any W_5e6f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
