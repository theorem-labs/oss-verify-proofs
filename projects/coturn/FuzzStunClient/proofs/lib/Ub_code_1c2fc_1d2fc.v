(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_1c2fc : bv 32 := 0x00c78613.
Lemma F_1c2fc : fetch_word Ubsan.M.loaded_segments (0x1c2fc : word) = Some W_1c2fc.
Proof. vm_refl. Qed.
Lemma D_1c2fc : decode_any W_1c2fc = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c300 : bv 32 := 0x0056d713.
Lemma F_1c300 : fetch_word Ubsan.M.loaded_segments (0x1c300 : word) = Some W_1c300.
Proof. vm_refl. Qed.
Lemma D_1c300 : decode_any W_1c300 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c304 : bv 32 := 0x0306e663.
Lemma F_1c304 : fetch_word Ubsan.M.loaded_segments (0x1c304 : word) = Some W_1c304.
Proof. vm_refl. Qed.
Lemma D_1c304 : decode_any W_1c304 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c308 : bv 32 := 0x00500693.
Lemma F_1c308 : fetch_word Ubsan.M.loaded_segments (0x1c308 : word) = Some W_1c308.
Proof. vm_refl. Qed.
Lemma D_1c308 : decode_any W_1c308 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c30c : bv 32 := 0x00d70463.
Lemma F_1c30c : fetch_word Ubsan.M.loaded_segments (0x1c30c : word) = Some W_1c30c.
Proof. vm_refl. Qed.
Lemma D_1c30c : decode_any W_1c30c = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c314 : bv 32 := 0x0087e703.
Lemma F_1c314 : fetch_word Ubsan.M.loaded_segments (0x1c314 : word) = Some W_1c314.
Proof. vm_refl. Qed.
Lemma D_1c314 : decode_any W_1c314 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c318 : bv 32 := 0x00400693.
Lemma F_1c318 : fetch_word Ubsan.M.loaded_segments (0x1c318 : word) = Some W_1c318.
Proof. vm_refl. Qed.
Lemma D_1c318 : decode_any W_1c318 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c31c : bv 32 := 0x00e6e463.
Lemma F_1c31c : fetch_word Ubsan.M.loaded_segments (0x1c31c : word) = Some W_1c31c.
Proof. vm_refl. Qed.
Lemma D_1c31c : decode_any W_1c31c = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c324 : bv 32 := 0x0077c683.
Lemma F_1c324 : fetch_word Ubsan.M.loaded_segments (0x1c324 : word) = Some W_1c324.
Proof. vm_refl. Qed.
Lemma D_1c324 : decode_any W_1c324 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c328 : bv 32 := 0x00068463.
Lemma F_1c328 : fetch_word Ubsan.M.loaded_segments (0x1c328 : word) = Some W_1c328.
Proof. vm_refl. Qed.
Lemma D_1c328 : decode_any W_1c328 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c330 : bv 32 := 0x409606b3.
Lemma F_1c330 : fetch_word Ubsan.M.loaded_segments (0x1c330 : word) = Some W_1c330.
Proof. vm_refl. Qed.
Lemma D_1c330 : decode_any W_1c330 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c334 : bv 32 := 0x00e6f463.
Lemma F_1c334 : fetch_word Ubsan.M.loaded_segments (0x1c334 : word) = Some W_1c334.
Proof. vm_refl. Qed.
Lemma D_1c334 : decode_any W_1c334 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c33c : bv 32 := 0x40e606b3.
Lemma F_1c33c : fetch_word Ubsan.M.loaded_segments (0x1c33c : word) = Some W_1c33c.
Proof. vm_refl. Qed.
Lemma D_1c33c : decode_any W_1c33c = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c340 : bv 32 := 0x0006c683.
Lemma F_1c340 : fetch_word Ubsan.M.loaded_segments (0x1c340 : word) = Some W_1c340.
Proof. vm_refl. Qed.
Lemma D_1c340 : decode_any W_1c340 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c344 : bv 32 := 0x00068463.
Lemma F_1c344 : fetch_word Ubsan.M.loaded_segments (0x1c344 : word) = Some W_1c344.
Proof. vm_refl. Qed.
Lemma D_1c344 : decode_any W_1c344 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c34c : bv 32 := 0x00064603.
Lemma F_1c34c : fetch_word Ubsan.M.loaded_segments (0x1c34c : word) = Some W_1c34c.
Proof. vm_refl. Qed.
Lemma D_1c34c : decode_any W_1c34c = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c350 : bv 32 := 0x00060463.
Lemma F_1c350 : fetch_word Ubsan.M.loaded_segments (0x1c350 : word) = Some W_1c350.
Proof. vm_refl. Qed.
Lemma D_1c350 : decode_any W_1c350 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c430 : bv 32 := 0x02013403.
Lemma F_1c430 : fetch_word Ubsan.M.loaded_segments (0x1c430 : word) = Some W_1c430.
Proof. vm_refl. Qed.
Lemma D_1c430 : decode_any W_1c430 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c434 : bv 32 := 0x01813483.
Lemma F_1c434 : fetch_word Ubsan.M.loaded_segments (0x1c434 : word) = Some W_1c434.
Proof. vm_refl. Qed.
Lemma D_1c434 : decode_any W_1c434 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c438 : bv 32 := 0x01013903.
Lemma F_1c438 : fetch_word Ubsan.M.loaded_segments (0x1c438 : word) = Some W_1c438.
Proof. vm_refl. Qed.
Lemma D_1c438 : decode_any W_1c438 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c43c : bv 32 := 0x00813983.
Lemma F_1c43c : fetch_word Ubsan.M.loaded_segments (0x1c43c : word) = Some W_1c43c.
Proof. vm_refl. Qed.
Lemma D_1c43c : decode_any W_1c43c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c440 : bv 32 := 0x03010113.
Lemma F_1c440 : fetch_word Ubsan.M.loaded_segments (0x1c440 : word) = Some W_1c440.
Proof. vm_refl. Qed.
Lemma D_1c440 : decode_any W_1c440 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c444 : bv 32 := 0x00008067.
Lemma F_1c444 : fetch_word Ubsan.M.loaded_segments (0x1c444 : word) = Some W_1c444.
Proof. vm_refl. Qed.
Lemma D_1c444 : decode_any W_1c444 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c448 : bv 32 := 0x00f57593.
Lemma F_1c448 : fetch_word Ubsan.M.loaded_segments (0x1c448 : word) = Some W_1c448.
Proof. vm_refl. Qed.
Lemma D_1c448 : decode_any W_1c448 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c44c : bv 32 := 0x00058463.
Lemma F_1c44c : fetch_word Ubsan.M.loaded_segments (0x1c44c : word) = Some W_1c44c.
Proof. vm_refl. Qed.
Lemma D_1c44c : decode_any W_1c44c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c454 : bv 32 := 0xffc54603.
Lemma F_1c454 : fetch_word Ubsan.M.loaded_segments (0x1c454 : word) = Some W_1c454.
Proof. vm_refl. Qed.
Lemma D_1c454 : decode_any W_1c454 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c458 : bv 32 := 0xffd54683.
Lemma F_1c458 : fetch_word Ubsan.M.loaded_segments (0x1c458 : word) = Some W_1c458.
Proof. vm_refl. Qed.
Lemma D_1c458 : decode_any W_1c458 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c45c : bv 32 := 0xffe55583.
Lemma F_1c45c : fetch_word Ubsan.M.loaded_segments (0x1c45c : word) = Some W_1c45c.
Proof. vm_refl. Qed.
Lemma D_1c45c : decode_any W_1c45c = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c460 : bv 32 := 0x00060e63.
Lemma F_1c460 : fetch_word Ubsan.M.loaded_segments (0x1c460 : word) = Some W_1c460.
Proof. vm_refl. Qed.
Lemma D_1c460 : decode_any W_1c460 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c47c : bv 32 := 0x00459613.
Lemma F_1c47c : fetch_word Ubsan.M.loaded_segments (0x1c47c : word) = Some W_1c47c.
Proof. vm_refl. Qed.
Lemma D_1c47c : decode_any W_1c47c = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c480 : bv 32 := 0x40c50633.
Lemma F_1c480 : fetch_word Ubsan.M.loaded_segments (0x1c480 : word) = Some W_1c480.
Proof. vm_refl. Qed.
Lemma D_1c480 : decode_any W_1c480 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c484 : bv 32 := 0xff063503.
Lemma F_1c484 : fetch_word Ubsan.M.loaded_segments (0x1c484 : word) = Some W_1c484.
Proof. vm_refl. Qed.
Lemma D_1c484 : decode_any W_1c484 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c488 : bv 32 := 0x01053703.
Lemma F_1c488 : fetch_word Ubsan.M.loaded_segments (0x1c488 : word) = Some W_1c488.
Proof. vm_refl. Qed.
Lemma D_1c488 : decode_any W_1c488 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c48c : bv 32 := 0xff060613.
Lemma F_1c48c : fetch_word Ubsan.M.loaded_segments (0x1c48c : word) = Some W_1c48c.
Proof. vm_refl. Qed.
Lemma D_1c48c : decode_any W_1c48c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c490 : bv 32 := 0x01f6f693.
Lemma F_1c490 : fetch_word Ubsan.M.loaded_segments (0x1c490 : word) = Some W_1c490.
Proof. vm_refl. Qed.
Lemma D_1c490 : decode_any W_1c490 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c494 : bv 32 := 0x00c70463.
Lemma F_1c494 : fetch_word Ubsan.M.loaded_segments (0x1c494 : word) = Some W_1c494.
Proof. vm_refl. Qed.
Lemma D_1c494 : decode_any W_1c494 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c49c : bv 32 := 0x02053603.
Lemma F_1c49c : fetch_word Ubsan.M.loaded_segments (0x1c49c : word) = Some W_1c49c.
Proof. vm_refl. Qed.
Lemma D_1c49c : decode_any W_1c49c = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4a0 : bv 32 := 0x01f67713.
Lemma F_1c4a0 : fetch_word Ubsan.M.loaded_segments (0x1c4a0 : word) = Some W_1c4a0.
Proof. vm_refl. Qed.
Lemma D_1c4a0 : decode_any W_1c4a0 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4a4 : bv 32 := 0x00d77463.
Lemma F_1c4a4 : fetch_word Ubsan.M.loaded_segments (0x1c4a4 : word) = Some W_1c4a4.
Proof. vm_refl. Qed.
Lemma D_1c4a4 : decode_any W_1c4a4 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4ac : bv 32 := 0x01852783.
Lemma F_1c4ac : fetch_word Ubsan.M.loaded_segments (0x1c4ac : word) = Some W_1c4ac.
Proof. vm_refl. Qed.
Lemma D_1c4ac : decode_any W_1c4ac = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4b0 : bv 32 := 0x00100713.
Lemma F_1c4b0 : fetch_word Ubsan.M.loaded_segments (0x1c4b0 : word) = Some W_1c4b0.
Proof. vm_refl. Qed.
Lemma D_1c4b0 : decode_any W_1c4b0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4b4 : bv 32 := 0x00d7173b.
Lemma F_1c4b4 : fetch_word Ubsan.M.loaded_segments (0x1c4b4 : word) = Some W_1c4b4.
Proof. vm_refl. Qed.
Lemma D_1c4b4 : decode_any W_1c4b4 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4b8 : bv 32 := 0x00e7f7b3.
Lemma F_1c4b8 : fetch_word Ubsan.M.loaded_segments (0x1c4b8 : word) = Some W_1c4b8.
Proof. vm_refl. Qed.
Lemma D_1c4b8 : decode_any W_1c4b8 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4bc : bv 32 := 0x00078463.
Lemma F_1c4bc : fetch_word Ubsan.M.loaded_segments (0x1c4bc : word) = Some W_1c4bc.
Proof. vm_refl. Qed.
Lemma D_1c4bc : decode_any W_1c4bc = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4c4 : bv 32 := 0x01c52783.
Lemma F_1c4c4 : fetch_word Ubsan.M.loaded_segments (0x1c4c4 : word) = Some W_1c4c4.
Proof. vm_refl. Qed.
Lemma D_1c4c4 : decode_any W_1c4c4 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4c8 : bv 32 := 0x00e7f733.
Lemma F_1c4c8 : fetch_word Ubsan.M.loaded_segments (0x1c4c8 : word) = Some W_1c4c8.
Proof. vm_refl. Qed.
Lemma D_1c4c8 : decode_any W_1c4c8 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4cc : bv 32 := 0x00070463.
Lemma F_1c4cc : fetch_word Ubsan.M.loaded_segments (0x1c4cc : word) = Some W_1c4cc.
Proof. vm_refl. Qed.
Lemma D_1c4cc : decode_any W_1c4cc = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4d4 : bv 32 := 0xfffff737.
Lemma F_1c4d4 : fetch_word Ubsan.M.loaded_segments (0x1c4d4 : word) = Some W_1c4d4.
Proof. vm_refl. Qed.
Lemma D_1c4d4 : decode_any W_1c4d4 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4d8 : bv 32 := 0x0003b797.
Lemma F_1c4d8 : fetch_word Ubsan.M.loaded_segments (0x1c4d8 : word) = Some W_1c4d8.
Proof. vm_refl. Qed.
Lemma D_1c4d8 : decode_any W_1c4d8 = Some (Auipc 15 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4dc : bv 32 := 0x00e57733.
Lemma F_1c4dc : fetch_word Ubsan.M.loaded_segments (0x1c4dc : word) = Some W_1c4dc.
Proof. vm_refl. Qed.
Lemma D_1c4dc : decode_any W_1c4dc = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4e0 : bv 32 := 0x00073703.
Lemma F_1c4e0 : fetch_word Ubsan.M.loaded_segments (0x1c4e0 : word) = Some W_1c4e0.
Proof. vm_refl. Qed.
Lemma D_1c4e0 : decode_any W_1c4e0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4e4 : bv 32 := 0xa887b783.
Lemma F_1c4e4 : fetch_word Ubsan.M.loaded_segments (0x1c4e4 : word) = Some W_1c4e4.
Proof. vm_refl. Qed.
Lemma D_1c4e4 : decode_any W_1c4e4 = Some (Load SZ8 true 15 15 2696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4e8 : bv 32 := 0x00f70463.
Lemma F_1c4e8 : fetch_word Ubsan.M.loaded_segments (0x1c4e8 : word) = Some W_1c4e8.
Proof. vm_refl. Qed.
Lemma D_1c4e8 : decode_any W_1c4e8 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4f0 : bv 32 := 0x03461713.
Lemma F_1c4f0 : fetch_word Ubsan.M.loaded_segments (0x1c4f0 : word) = Some W_1c4f0.
Proof. vm_refl. Qed.
Lemma D_1c4f0 : decode_any W_1c4f0 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4f4 : bv 32 := 0x03a75713.
Lemma F_1c4f4 : fetch_word Ubsan.M.loaded_segments (0x1c4f4 : word) = Some W_1c4f4.
Proof. vm_refl. Qed.
Lemma D_1c4f4 : decode_any W_1c4f4 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4f8 : bv 32 := 0x02f00793.
Lemma F_1c4f8 : fetch_word Ubsan.M.loaded_segments (0x1c4f8 : word) = Some W_1c4f8.
Proof. vm_refl. Qed.
Lemma D_1c4f8 : decode_any W_1c4f8 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c4fc : bv 32 := 0x02e7ea63.
Lemma F_1c4fc : fetch_word Ubsan.M.loaded_segments (0x1c4fc : word) = Some W_1c4fc.
Proof. vm_refl. Qed.
Lemma D_1c4fc : decode_any W_1c4fc = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c500 : bv 32 := 0x00171713.
Lemma F_1c500 : fetch_word Ubsan.M.loaded_segments (0x1c500 : word) = Some W_1c500.
Proof. vm_refl. Qed.
Lemma D_1c500 : decode_any W_1c500 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c504 : bv 32 := 0xffff5797.
Lemma F_1c504 : fetch_word Ubsan.M.loaded_segments (0x1c504 : word) = Some W_1c504.
Proof. vm_refl. Qed.
Lemma D_1c504 : decode_any W_1c504 = Some (Auipc 15 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c508 : bv 32 := 0xbb478793.
Lemma F_1c508 : fetch_word Ubsan.M.loaded_segments (0x1c508 : word) = Some W_1c508.
Proof. vm_refl. Qed.
Lemma D_1c508 : decode_any W_1c508 = Some (OpImm ALU_ADD 15 15 2996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50c : bv 32 := 0x00e78733.
Lemma F_1c50c : fetch_word Ubsan.M.loaded_segments (0x1c50c : word) = Some W_1c50c.
Proof. vm_refl. Qed.
Lemma D_1c50c : decode_any W_1c50c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c510 : bv 32 := 0x00075703.
Lemma F_1c510 : fetch_word Ubsan.M.loaded_segments (0x1c510 : word) = Some W_1c510.
Proof. vm_refl. Qed.
Lemma D_1c510 : decode_any W_1c510 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c514 : bv 32 := 0x02d707b3.
Lemma F_1c514 : fetch_word Ubsan.M.loaded_segments (0x1c514 : word) = Some W_1c514.
Proof. vm_refl. Qed.
Lemma D_1c514 : decode_any W_1c514 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c518 : bv 32 := 0x00f5f463.
Lemma F_1c518 : fetch_word Ubsan.M.loaded_segments (0x1c518 : word) = Some W_1c518.
Proof. vm_refl. Qed.
Lemma D_1c518 : decode_any W_1c518 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c520 : bv 32 := 0x00168693.
Lemma F_1c520 : fetch_word Ubsan.M.loaded_segments (0x1c520 : word) = Some W_1c520.
Proof. vm_refl. Qed.
Lemma D_1c520 : decode_any W_1c520 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c524 : bv 32 := 0x02e686b3.
Lemma F_1c524 : fetch_word Ubsan.M.loaded_segments (0x1c524 : word) = Some W_1c524.
Proof. vm_refl. Qed.
Lemma D_1c524 : decode_any W_1c524 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c528 : bv 32 := 0x00d5f863.
Lemma F_1c528 : fetch_word Ubsan.M.loaded_segments (0x1c528 : word) = Some W_1c528.
Proof. vm_refl. Qed.
Lemma D_1c528 : decode_any W_1c528 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c52c : bv 32 := 0x0100006f.
Lemma F_1c52c : fetch_word Ubsan.M.loaded_segments (0x1c52c : word) = Some W_1c52c.
Proof. vm_refl. Qed.
Lemma D_1c52c : decode_any W_1c52c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c530 : bv 32 := 0x03f00693.
Lemma F_1c530 : fetch_word Ubsan.M.loaded_segments (0x1c530 : word) = Some W_1c530.
Proof. vm_refl. Qed.
Lemma D_1c530 : decode_any W_1c530 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c534 : bv 32 := 0x00d70463.
Lemma F_1c534 : fetch_word Ubsan.M.loaded_segments (0x1c534 : word) = Some W_1c534.
Proof. vm_refl. Qed.
Lemma D_1c534 : decode_any W_1c534 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c53c : bv 32 := 0x00c65613.
Lemma F_1c53c : fetch_word Ubsan.M.loaded_segments (0x1c53c : word) = Some W_1c53c.
Proof. vm_refl. Qed.
Lemma D_1c53c : decode_any W_1c53c = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c540 : bv 32 := 0x00060a63.
Lemma F_1c540 : fetch_word Ubsan.M.loaded_segments (0x1c540 : word) = Some W_1c540.
Proof. vm_refl. Qed.
Lemma D_1c540 : decode_any W_1c540 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c544 : bv 32 := 0x00861613.
Lemma F_1c544 : fetch_word Ubsan.M.loaded_segments (0x1c544 : word) = Some W_1c544.
Proof. vm_refl. Qed.
Lemma D_1c544 : decode_any W_1c544 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c548 : bv 32 := 0xfff60613.
Lemma F_1c548 : fetch_word Ubsan.M.loaded_segments (0x1c548 : word) = Some W_1c548.
Proof. vm_refl. Qed.
Lemma D_1c548 : decode_any W_1c548 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c54c : bv 32 := 0x00b67463.
Lemma F_1c54c : fetch_word Ubsan.M.loaded_segments (0x1c54c : word) = Some W_1c54c.
Proof. vm_refl. Qed.
Lemma D_1c54c : decode_any W_1c54c = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c554 : bv 32 := 0x00008067.
Lemma F_1c554 : fetch_word Ubsan.M.loaded_segments (0x1c554 : word) = Some W_1c554.
Proof. vm_refl. Qed.
Lemma D_1c554 : decode_any W_1c554 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8d8 : bv 32 := 0x00072503.
Lemma F_1c8d8 : fetch_word Ubsan.M.loaded_segments (0x1c8d8 : word) = Some W_1c8d8.
Proof. vm_refl. Qed.
Lemma D_1c8d8 : decode_any W_1c8d8 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8dc : bv 32 := 0x00b56633.
Lemma F_1c8dc : fetch_word Ubsan.M.loaded_segments (0x1c8dc : word) = Some W_1c8dc.
Proof. vm_refl. Qed.
Lemma D_1c8dc : decode_any W_1c8dc = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8e0 : bv 32 := 0x160726af.
Lemma F_1c8e0 : fetch_word Ubsan.M.loaded_segments (0x1c8e0 : word) = Some W_1c8e0.
Proof. vm_refl. Qed.
Lemma D_1c8e0 : decode_any W_1c8e0 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8e4 : bv 32 := 0x00a69663.
Lemma F_1c8e4 : fetch_word Ubsan.M.loaded_segments (0x1c8e4 : word) = Some W_1c8e4.
Proof. vm_refl. Qed.
Lemma D_1c8e4 : decode_any W_1c8e4 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8e8 : bv 32 := 0x1ec727af.
Lemma F_1c8e8 : fetch_word Ubsan.M.loaded_segments (0x1c8e8 : word) = Some W_1c8e8.
Proof. vm_refl. Qed.
Lemma D_1c8e8 : decode_any W_1c8e8 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8ec : bv 32 := 0xfe079ae3.
Lemma F_1c8ec : fetch_word Ubsan.M.loaded_segments (0x1c8ec : word) = Some W_1c8ec.
Proof. vm_refl. Qed.
Lemma D_1c8ec : decode_any W_1c8ec = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8f0 : bv 32 := 0x0006869b.
Lemma F_1c8f0 : fetch_word Ubsan.M.loaded_segments (0x1c8f0 : word) = Some W_1c8f0.
Proof. vm_refl. Qed.
Lemma D_1c8f0 : decode_any W_1c8f0 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c8f4 : bv 32 := 0xfea692e3.
Lemma F_1c8f4 : fetch_word Ubsan.M.loaded_segments (0x1c8f4 : word) = Some W_1c8f4.
Proof. vm_refl. Qed.
Lemma D_1c8f4 : decode_any W_1c8f4 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc10 : bv 32 := 0x02813023.
Lemma F_1cc10 : fetch_word Ubsan.M.loaded_segments (0x1cc10 : word) = Some W_1cc10.
Proof. vm_refl. Qed.
Lemma D_1cc10 : decode_any W_1cc10 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc14 : bv 32 := 0x00913c23.
Lemma F_1cc14 : fetch_word Ubsan.M.loaded_segments (0x1cc14 : word) = Some W_1cc14.
Proof. vm_refl. Qed.
Lemma D_1cc14 : decode_any W_1cc14 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc18 : bv 32 := 0x01213823.
Lemma F_1cc18 : fetch_word Ubsan.M.loaded_segments (0x1cc18 : word) = Some W_1cc18.
Proof. vm_refl. Qed.
Lemma D_1cc18 : decode_any W_1cc18 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc1c : bv 32 := 0x01313423.
Lemma F_1cc1c : fetch_word Ubsan.M.loaded_segments (0x1cc1c : word) = Some W_1cc1c.
Proof. vm_refl. Qed.
Lemma D_1cc1c : decode_any W_1cc1c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc20 : bv 32 := 0x01413023.
Lemma F_1cc20 : fetch_word Ubsan.M.loaded_segments (0x1cc20 : word) = Some W_1cc20.
Proof. vm_refl. Qed.
Lemma D_1cc20 : decode_any W_1cc20 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc24 : bv 32 := 0xffffe5b7.
Lemma F_1cc24 : fetch_word Ubsan.M.loaded_segments (0x1cc24 : word) = Some W_1cc24.
Proof. vm_refl. Qed.
Lemma D_1cc24 : decode_any W_1cc24 = Some (Lui 11 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc28 : bv 32 := 0xfff5859b.
Lemma F_1cc28 : fetch_word Ubsan.M.loaded_segments (0x1cc28 : word) = Some W_1cc28.
Proof. vm_refl. Qed.
Lemma D_1cc28 : decode_any W_1cc28 = Some (OpImm32 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc2c : bv 32 := 0x0015d593.
Lemma F_1cc2c : fetch_word Ubsan.M.loaded_segments (0x1cc2c : word) = Some W_1cc2c.
Proof. vm_refl. Qed.
Lemma D_1cc2c : decode_any W_1cc2c = Some (ShiftImm ALU_SRL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0b8 : bv 32 := 0x00062703.
Lemma F_1d0b8 : fetch_word Ubsan.M.loaded_segments (0x1d0b8 : word) = Some W_1d0b8.
Proof. vm_refl. Qed.
Lemma D_1d0b8 : decode_any W_1d0b8 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0bc : bv 32 := 0x00d777b3.
Lemma F_1d0bc : fetch_word Ubsan.M.loaded_segments (0x1d0bc : word) = Some W_1d0bc.
Proof. vm_refl. Qed.
Lemma D_1d0bc : decode_any W_1d0bc = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0c0 : bv 32 := 0x1606282f.
Lemma F_1d0c0 : fetch_word Ubsan.M.loaded_segments (0x1d0c0 : word) = Some W_1d0c0.
Proof. vm_refl. Qed.
Lemma D_1d0c0 : decode_any W_1d0c0 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0c4 : bv 32 := 0x00e81663.
Lemma F_1d0c4 : fetch_word Ubsan.M.loaded_segments (0x1d0c4 : word) = Some W_1d0c4.
Proof. vm_refl. Qed.
Lemma D_1d0c4 : decode_any W_1d0c4 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0c8 : bv 32 := 0x1ef628af.
Lemma F_1d0c8 : fetch_word Ubsan.M.loaded_segments (0x1d0c8 : word) = Some W_1d0c8.
Proof. vm_refl. Qed.
Lemma D_1d0c8 : decode_any W_1d0c8 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0cc : bv 32 := 0xfe089ae3.
Lemma F_1d0cc : fetch_word Ubsan.M.loaded_segments (0x1d0cc : word) = Some W_1d0cc.
Proof. vm_refl. Qed.
Lemma D_1d0cc : decode_any W_1d0cc = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0d0 : bv 32 := 0x0008081b.
Lemma F_1d0d0 : fetch_word Ubsan.M.loaded_segments (0x1d0d0 : word) = Some W_1d0d0.
Proof. vm_refl. Qed.
Lemma D_1d0d0 : decode_any W_1d0d0 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d0d4 : bv 32 := 0xfee812e3.
Lemma F_1d0d4 : fetch_word Ubsan.M.loaded_segments (0x1d0d4 : word) = Some W_1d0d4.
Proof. vm_refl. Qed.
Lemma D_1d0d4 : decode_any W_1d0d4 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.
