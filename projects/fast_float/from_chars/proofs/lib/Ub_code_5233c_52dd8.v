(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5233c : bv 32 := 0x00008067.
Lemma F_5233c : fetch_word Ubsan.M.loaded_segments (0x5233c : word) = Some W_5233c.
Proof. vm_refl. Qed.
Lemma D_5233c : decode_any W_5233c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52340 : bv 32 := 0xe8010113.
Lemma F_52340 : fetch_word Ubsan.M.loaded_segments (0x52340 : word) = Some W_52340.
Proof. vm_refl. Qed.
Lemma D_52340 : decode_any W_52340 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52344 : bv 32 := 0x16113c23.
Lemma F_52344 : fetch_word Ubsan.M.loaded_segments (0x52344 : word) = Some W_52344.
Proof. vm_refl. Qed.
Lemma D_52344 : decode_any W_52344 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52348 : bv 32 := 0x16813823.
Lemma F_52348 : fetch_word Ubsan.M.loaded_segments (0x52348 : word) = Some W_52348.
Proof. vm_refl. Qed.
Lemma D_52348 : decode_any W_52348 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5234c : bv 32 := 0x16913423.
Lemma F_5234c : fetch_word Ubsan.M.loaded_segments (0x5234c : word) = Some W_5234c.
Proof. vm_refl. Qed.
Lemma D_5234c : decode_any W_5234c = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52350 : bv 32 := 0x17213023.
Lemma F_52350 : fetch_word Ubsan.M.loaded_segments (0x52350 : word) = Some W_52350.
Proof. vm_refl. Qed.
Lemma D_52350 : decode_any W_52350 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52354 : bv 32 := 0x00058413.
Lemma F_52354 : fetch_word Ubsan.M.loaded_segments (0x52354 : word) = Some W_52354.
Proof. vm_refl. Qed.
Lemma D_52354 : decode_any W_52354 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52358 : bv 32 := 0x00050493.
Lemma F_52358 : fetch_word Ubsan.M.loaded_segments (0x52358 : word) = Some W_52358.
Proof. vm_refl. Qed.
Lemma D_52358 : decode_any W_52358 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5235c : bv 32 := 0x03010513.
Lemma F_5235c : fetch_word Ubsan.M.loaded_segments (0x5235c : word) = Some W_5235c.
Proof. vm_refl. Qed.
Lemma D_5235c : decode_any W_5235c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52360 : bv 32 := 0x13000613.
Lemma F_52360 : fetch_word Ubsan.M.loaded_segments (0x52360 : word) = Some W_52360.
Proof. vm_refl. Qed.
Lemma D_52360 : decode_any W_52360 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52364 : bv 32 := 0x00000593.
Lemma F_52364 : fetch_word Ubsan.M.loaded_segments (0x52364 : word) = Some W_52364.
Proof. vm_refl. Qed.
Lemma D_52364 : decode_any W_52364 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52368 : bv 32 := 0x2c00e0ef.
Lemma F_52368 : fetch_word Ubsan.M.loaded_segments (0x52368 : word) = Some W_52368.
Proof. vm_refl. Qed.
Lemma D_52368 : decode_any W_52368 = Some (Jal 1 58048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5236c : bv 32 := 0x00013517.
Lemma F_5236c : fetch_word Ubsan.M.loaded_segments (0x5236c : word) = Some W_5236c.
Proof. vm_refl. Qed.
Lemma D_5236c : decode_any W_5236c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52370 : bv 32 := 0x7c453503.
Lemma F_52370 : fetch_word Ubsan.M.loaded_segments (0x52370 : word) = Some W_52370.
Proof. vm_refl. Qed.
Lemma D_52370 : decode_any W_52370 = Some (Load SZ8 true 10 10 1988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52374 : bv 32 := 0x00953023.
Lemma F_52374 : fetch_word Ubsan.M.loaded_segments (0x52374 : word) = Some W_52374.
Proof. vm_refl. Qed.
Lemma D_52374 : decode_any W_52374 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52378 : bv 32 := 0x0004b503.
Lemma F_52378 : fetch_word Ubsan.M.loaded_segments (0x52378 : word) = Some W_52378.
Proof. vm_refl. Qed.
Lemma D_52378 : decode_any W_52378 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5237c : bv 32 := 0x00848493.
Lemma F_5237c : fetch_word Ubsan.M.loaded_segments (0x5237c : word) = Some W_5237c.
Proof. vm_refl. Qed.
Lemma D_5237c : decode_any W_5237c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52380 : bv 32 := 0xfe051ce3.
Lemma F_52380 : fetch_word Ubsan.M.loaded_segments (0x52380 : word) = Some W_52380.
Proof. vm_refl. Qed.
Lemma D_52380 : decode_any W_52380 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52384 : bv 32 := 0x00046517.
Lemma F_52384 : fetch_word Ubsan.M.loaded_segments (0x52384 : word) = Some W_52384.
Proof. vm_refl. Qed.
Lemma D_52384 : decode_any W_52384 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52388 : bv 32 := 0x89c50913.
Lemma F_52388 : fetch_word Ubsan.M.loaded_segments (0x52388 : word) = Some W_52388.
Proof. vm_refl. Qed.
Lemma D_52388 : decode_any W_52388 = Some (OpImm ALU_ADD 18 10 2204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5238c : bv 32 := 0x00993423.
Lemma F_5238c : fetch_word Ubsan.M.loaded_segments (0x5238c : word) = Some W_5238c.
Proof. vm_refl. Qed.
Lemma D_5238c : decode_any W_5238c = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52390 : bv 32 := 0x0004b583.
Lemma F_52390 : fetch_word Ubsan.M.loaded_segments (0x52390 : word) = Some W_52390.
Proof. vm_refl. Qed.
Lemma D_52390 : decode_any W_52390 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52394 : bv 32 := 0x04058c63.
Lemma F_52394 : fetch_word Ubsan.M.loaded_segments (0x52394 : word) = Some W_52394.
Proof. vm_refl. Qed.
Lemma D_52394 : decode_any W_52394 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52398 : bv 32 := 0x01048493.
Lemma F_52398 : fetch_word Ubsan.M.loaded_segments (0x52398 : word) = Some W_52398.
Proof. vm_refl. Qed.
Lemma D_52398 : decode_any W_52398 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5239c : bv 32 := 0x02500513.
Lemma F_5239c : fetch_word Ubsan.M.loaded_segments (0x5239c : word) = Some W_5239c.
Proof. vm_refl. Qed.
Lemma D_5239c : decode_any W_5239c = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523a0 : bv 32 := 0x03010613.
Lemma F_523a0 : fetch_word Ubsan.M.loaded_segments (0x523a0 : word) = Some W_523a0.
Proof. vm_refl. Qed.
Lemma D_523a0 : decode_any W_523a0 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523a4 : bv 32 := 0x0100006f.
Lemma F_523a4 : fetch_word Ubsan.M.loaded_segments (0x523a4 : word) = Some W_523a4.
Proof. vm_refl. Qed.
Lemma D_523a4 : decode_any W_523a4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523a8 : bv 32 := 0x0004b583.
Lemma F_523a8 : fetch_word Ubsan.M.loaded_segments (0x523a8 : word) = Some W_523a8.
Proof. vm_refl. Qed.
Lemma D_523a8 : decode_any W_523a8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523ac : bv 32 := 0x01048493.
Lemma F_523ac : fetch_word Ubsan.M.loaded_segments (0x523ac : word) = Some W_523ac.
Proof. vm_refl. Qed.
Lemma D_523ac : decode_any W_523ac = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523b0 : bv 32 := 0x00058e63.
Lemma F_523b0 : fetch_word Ubsan.M.loaded_segments (0x523b0 : word) = Some W_523b0.
Proof. vm_refl. Qed.
Lemma D_523b0 : decode_any W_523b0 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523b4 : bv 32 := 0xfeb56ae3.
Lemma F_523b4 : fetch_word Ubsan.M.loaded_segments (0x523b4 : word) = Some W_523b4.
Proof. vm_refl. Qed.
Lemma D_523b4 : decode_any W_523b4 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523b8 : bv 32 := 0xff84b683.
Lemma F_523b8 : fetch_word Ubsan.M.loaded_segments (0x523b8 : word) = Some W_523b8.
Proof. vm_refl. Qed.
Lemma D_523b8 : decode_any W_523b8 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523bc : bv 32 := 0x00359593.
Lemma F_523bc : fetch_word Ubsan.M.loaded_segments (0x523bc : word) = Some W_523bc.
Proof. vm_refl. Qed.
Lemma D_523bc : decode_any W_523bc = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523c0 : bv 32 := 0x00b605b3.
Lemma F_523c0 : fetch_word Ubsan.M.loaded_segments (0x523c0 : word) = Some W_523c0.
Proof. vm_refl. Qed.
Lemma D_523c0 : decode_any W_523c0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523c4 : bv 32 := 0x00d5b023.
Lemma F_523c4 : fetch_word Ubsan.M.loaded_segments (0x523c4 : word) = Some W_523c4.
Proof. vm_refl. Qed.
Lemma D_523c4 : decode_any W_523c4 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523c8 : bv 32 := 0xfe1ff06f.
Lemma F_523c8 : fetch_word Ubsan.M.loaded_segments (0x523c8 : word) = Some W_523c8.
Proof. vm_refl. Qed.
Lemma D_523c8 : decode_any W_523c8 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523cc : bv 32 := 0x0b013583.
Lemma F_523cc : fetch_word Ubsan.M.loaded_segments (0x523cc : word) = Some W_523cc.
Proof. vm_refl. Qed.
Lemma D_523cc : decode_any W_523cc = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523d0 : bv 32 := 0x13013503.
Lemma F_523d0 : fetch_word Ubsan.M.loaded_segments (0x523d0 : word) = Some W_523d0.
Proof. vm_refl. Qed.
Lemma D_523d0 : decode_any W_523d0 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523d4 : bv 32 := 0x00046617.
Lemma F_523d4 : fetch_word Ubsan.M.loaded_segments (0x523d4 : word) = Some W_523d4.
Proof. vm_refl. Qed.
Lemma D_523d4 : decode_any W_523d4 = Some (Auipc 12 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523d8 : bv 32 := 0x8ab63a23.
Lemma F_523d8 : fetch_word Ubsan.M.loaded_segments (0x523d8 : word) = Some W_523d8.
Proof. vm_refl. Qed.
Lemma D_523d8 : decode_any W_523d8 = Some (Store SZ8 12 11 2228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523dc : bv 32 := 0x00050c63.
Lemma F_523dc : fetch_word Ubsan.M.loaded_segments (0x523dc : word) = Some W_523dc.
Proof. vm_refl. Qed.
Lemma D_523dc : decode_any W_523dc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523e0 : bv 32 := 0x00046597.
Lemma F_523e0 : fetch_word Ubsan.M.loaded_segments (0x523e0 : word) = Some W_523e0.
Proof. vm_refl. Qed.
Lemma D_523e0 : decode_any W_523e0 = Some (Auipc 11 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523e4 : bv 32 := 0x82a5b423.
Lemma F_523e4 : fetch_word Ubsan.M.loaded_segments (0x523e4 : word) = Some W_523e4.
Proof. vm_refl. Qed.
Lemma D_523e4 : decode_any W_523e4 = Some (Store SZ8 11 10 2088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523e8 : bv 32 := 0x00c0006f.
Lemma F_523e8 : fetch_word Ubsan.M.loaded_segments (0x523e8 : word) = Some W_523e8.
Proof. vm_refl. Qed.
Lemma D_523e8 : decode_any W_523e8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523ec : bv 32 := 0x00046517.
Lemma F_523ec : fetch_word Ubsan.M.loaded_segments (0x523ec : word) = Some W_523ec.
Proof. vm_refl. Qed.
Lemma D_523ec : decode_any W_523ec = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523f0 : bv 32 := 0x88053e23.
Lemma F_523f0 : fetch_word Ubsan.M.loaded_segments (0x523f0 : word) = Some W_523f0.
Proof. vm_refl. Qed.
Lemma D_523f0 : decode_any W_523f0 = Some (Store SZ8 10 0 2204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523f4 : bv 32 := 0x06013503.
Lemma F_523f4 : fetch_word Ubsan.M.loaded_segments (0x523f4 : word) = Some W_523f4.
Proof. vm_refl. Qed.
Lemma D_523f4 : decode_any W_523f4 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523f8 : bv 32 := 0x02a93823.
Lemma F_523f8 : fetch_word Ubsan.M.loaded_segments (0x523f8 : word) = Some W_523f8.
Proof. vm_refl. Qed.
Lemma D_523f8 : decode_any W_523f8 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_523fc : bv 32 := 0x00041463.
Lemma F_523fc : fetch_word Ubsan.M.loaded_segments (0x523fc : word) = Some W_523fc.
Proof. vm_refl. Qed.
Lemma D_523fc : decode_any W_523fc = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52400 : bv 32 := 0x12813403.
Lemma F_52400 : fetch_word Ubsan.M.loaded_segments (0x52400 : word) = Some W_52400.
Proof. vm_refl. Qed.
Lemma D_52400 : decode_any W_52400 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52404 : bv 32 := 0x00041663.
Lemma F_52404 : fetch_word Ubsan.M.loaded_segments (0x52404 : word) = Some W_52404.
Proof. vm_refl. Qed.
Lemma D_52404 : decode_any W_52404 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52408 : bv 32 := 0xfffbe517.
Lemma F_52408 : fetch_word Ubsan.M.loaded_segments (0x52408 : word) = Some W_52408.
Proof. vm_refl. Qed.
Lemma D_52408 : decode_any W_52408 = Some (Auipc 10 1048510, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5240c : bv 32 := 0x7e950413.
Lemma F_5240c : fetch_word Ubsan.M.loaded_segments (0x5240c : word) = Some W_5240c.
Proof. vm_refl. Qed.
Lemma D_5240c : decode_any W_5240c = Some (OpImm ALU_ADD 8 10 2025, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52410 : bv 32 := 0x00013517.
Lemma F_52410 : fetch_word Ubsan.M.loaded_segments (0x52410 : word) = Some W_52410.
Proof. vm_refl. Qed.
Lemma D_52410 : decode_any W_52410 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52414 : bv 32 := 0x72853583.
Lemma F_52414 : fetch_word Ubsan.M.loaded_segments (0x52414 : word) = Some W_52414.
Proof. vm_refl. Qed.
Lemma D_52414 : decode_any W_52414 = Some (Load SZ8 true 11 10 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52418 : bv 32 := 0x00013517.
Lemma F_52418 : fetch_word Ubsan.M.loaded_segments (0x52418 : word) = Some W_52418.
Proof. vm_refl. Qed.
Lemma D_52418 : decode_any W_52418 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5241c : bv 32 := 0x72853503.
Lemma F_5241c : fetch_word Ubsan.M.loaded_segments (0x5241c : word) = Some W_5241c.
Proof. vm_refl. Qed.
Lemma D_5241c : decode_any W_5241c = Some (Load SZ8 true 10 10 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52420 : bv 32 := 0x0085b023.
Lemma F_52420 : fetch_word Ubsan.M.loaded_segments (0x52420 : word) = Some W_52420.
Proof. vm_refl. Qed.
Lemma D_52420 : decode_any W_52420 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52424 : bv 32 := 0x00140593.
Lemma F_52424 : fetch_word Ubsan.M.loaded_segments (0x52424 : word) = Some W_52424.
Proof. vm_refl. Qed.
Lemma D_52424 : decode_any W_52424 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52428 : bv 32 := 0x00853023.
Lemma F_52428 : fetch_word Ubsan.M.loaded_segments (0x52428 : word) = Some W_52428.
Proof. vm_refl. Qed.
Lemma D_52428 : decode_any W_52428 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5242c : bv 32 := 0x02f00613.
Lemma F_5242c : fetch_word Ubsan.M.loaded_segments (0x5242c : word) = Some W_5242c.
Proof. vm_refl. Qed.
Lemma D_5242c : decode_any W_5242c = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52430 : bv 32 := 0x00c0006f.
Lemma F_52430 : fetch_word Ubsan.M.loaded_segments (0x52430 : word) = Some W_52430.
Proof. vm_refl. Qed.
Lemma D_52430 : decode_any W_52430 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52434 : bv 32 := 0x00b53023.
Lemma F_52434 : fetch_word Ubsan.M.loaded_segments (0x52434 : word) = Some W_52434.
Proof. vm_refl. Qed.
Lemma D_52434 : decode_any W_52434 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52438 : bv 32 := 0x00158593.
Lemma F_52438 : fetch_word Ubsan.M.loaded_segments (0x52438 : word) = Some W_52438.
Proof. vm_refl. Qed.
Lemma D_52438 : decode_any W_52438 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5243c : bv 32 := 0xfff5c683.
Lemma F_5243c : fetch_word Ubsan.M.loaded_segments (0x5243c : word) = Some W_5243c.
Proof. vm_refl. Qed.
Lemma D_5243c : decode_any W_5243c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52440 : bv 32 := 0xfec68ae3.
Lemma F_52440 : fetch_word Ubsan.M.loaded_segments (0x52440 : word) = Some W_52440.
Proof. vm_refl. Qed.
Lemma D_52440 : decode_any W_52440 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52444 : bv 32 := 0xfe069ae3.
Lemma F_52444 : fetch_word Ubsan.M.loaded_segments (0x52444 : word) = Some W_52444.
Proof. vm_refl. Qed.
Lemma D_52444 : decode_any W_52444 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52448 : bv 32 := 0x03010513.
Lemma F_52448 : fetch_word Ubsan.M.loaded_segments (0x52448 : word) = Some W_52448.
Proof. vm_refl. Qed.
Lemma D_52448 : decode_any W_52448 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5244c : bv 32 := 0x214000ef.
Lemma F_5244c : fetch_word Ubsan.M.loaded_segments (0x5244c : word) = Some W_5244c.
Proof. vm_refl. Qed.
Lemma D_5244c : decode_any W_5244c = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52450 : bv 32 := 0x0f813503.
Lemma F_52450 : fetch_word Ubsan.M.loaded_segments (0x52450 : word) = Some W_52450.
Proof. vm_refl. Qed.
Lemma D_52450 : decode_any W_52450 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52454 : bv 32 := 0x0e5000ef.
Lemma F_52454 : fetch_word Ubsan.M.loaded_segments (0x52454 : word) = Some W_52454.
Proof. vm_refl. Qed.
Lemma D_52454 : decode_any W_52454 = Some (Jal 1 2276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52458 : bv 32 := 0x08813503.
Lemma F_52458 : fetch_word Ubsan.M.loaded_segments (0x52458 : word) = Some W_52458.
Proof. vm_refl. Qed.
Lemma D_52458 : decode_any W_52458 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5245c : bv 32 := 0x09013583.
Lemma F_5245c : fetch_word Ubsan.M.loaded_segments (0x5245c : word) = Some W_5245c.
Proof. vm_refl. Qed.
Lemma D_5245c : decode_any W_5245c = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52460 : bv 32 := 0x00b51c63.
Lemma F_52460 : fetch_word Ubsan.M.loaded_segments (0x52460 : word) = Some W_52460.
Proof. vm_refl. Qed.
Lemma D_52460 : decode_any W_52460 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52464 : bv 32 := 0x09813503.
Lemma F_52464 : fetch_word Ubsan.M.loaded_segments (0x52464 : word) = Some W_52464.
Proof. vm_refl. Qed.
Lemma D_52464 : decode_any W_52464 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52468 : bv 32 := 0x0a013583.
Lemma F_52468 : fetch_word Ubsan.M.loaded_segments (0x52468 : word) = Some W_52468.
Proof. vm_refl. Qed.
Lemma D_52468 : decode_any W_52468 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5246c : bv 32 := 0x00b51663.
Lemma F_5246c : fetch_word Ubsan.M.loaded_segments (0x5246c : word) = Some W_5246c.
Proof. vm_refl. Qed.
Lemma D_5246c : decode_any W_5246c = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52470 : bv 32 := 0x0e813503.
Lemma F_52470 : fetch_word Ubsan.M.loaded_segments (0x52470 : word) = Some W_52470.
Proof. vm_refl. Qed.
Lemma D_52470 : decode_any W_52470 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52474 : bv 32 := 0x0e050063.
Lemma F_52474 : fetch_word Ubsan.M.loaded_segments (0x52474 : word) = Some W_52474.
Proof. vm_refl. Qed.
Lemma D_52474 : decode_any W_52474 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52478 : bv 32 := 0x00200693.
Lemma F_52478 : fetch_word Ubsan.M.loaded_segments (0x52478 : word) = Some W_52478.
Proof. vm_refl. Qed.
Lemma D_52478 : decode_any W_52478 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5247c : bv 32 := 0x00100793.
Lemma F_5247c : fetch_word Ubsan.M.loaded_segments (0x5247c : word) = Some W_5247c.
Proof. vm_refl. Qed.
Lemma D_5247c : decode_any W_5247c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52480 : bv 32 := 0x00013423.
Lemma F_52480 : fetch_word Ubsan.M.loaded_segments (0x52480 : word) = Some W_52480.
Proof. vm_refl. Qed.
Lemma D_52480 : decode_any W_52480 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52484 : bv 32 := 0x00013823.
Lemma F_52484 : fetch_word Ubsan.M.loaded_segments (0x52484 : word) = Some W_52484.
Proof. vm_refl. Qed.
Lemma D_52484 : decode_any W_52484 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52488 : bv 32 := 0x04900893.
Lemma F_52488 : fetch_word Ubsan.M.loaded_segments (0x52488 : word) = Some W_52488.
Proof. vm_refl. Qed.
Lemma D_52488 : decode_any W_52488 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5248c : bv 32 := 0x01810513.
Lemma F_5248c : fetch_word Ubsan.M.loaded_segments (0x5248c : word) = Some W_5248c.
Proof. vm_refl. Qed.
Lemma D_5248c : decode_any W_5248c = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52490 : bv 32 := 0x00300593.
Lemma F_52490 : fetch_word Ubsan.M.loaded_segments (0x52490 : word) = Some W_52490.
Proof. vm_refl. Qed.
Lemma D_52490 : decode_any W_52490 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52494 : bv 32 := 0x00810613.
Lemma F_52494 : fetch_word Ubsan.M.loaded_segments (0x52494 : word) = Some W_52494.
Proof. vm_refl. Qed.
Lemma D_52494 : decode_any W_52494 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52498 : bv 32 := 0x00800713.
Lemma F_52498 : fetch_word Ubsan.M.loaded_segments (0x52498 : word) = Some W_52498.
Proof. vm_refl. Qed.
Lemma D_52498 : decode_any W_52498 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5249c : bv 32 := 0x00013c23.
Lemma F_5249c : fetch_word Ubsan.M.loaded_segments (0x5249c : word) = Some W_5249c.
Proof. vm_refl. Qed.
Lemma D_5249c : decode_any W_5249c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524a0 : bv 32 := 0x02f13023.
Lemma F_524a0 : fetch_word Ubsan.M.loaded_segments (0x524a0 : word) = Some W_524a0.
Proof. vm_refl. Qed.
Lemma D_524a0 : decode_any W_524a0 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524a4 : bv 32 := 0x02d13423.
Lemma F_524a4 : fetch_word Ubsan.M.loaded_segments (0x524a4 : word) = Some W_524a4.
Proof. vm_refl. Qed.
Lemma D_524a4 : decode_any W_524a4 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524a8 : bv 32 := 0x00000693.
Lemma F_524a8 : fetch_word Ubsan.M.loaded_segments (0x524a8 : word) = Some W_524a8.
Proof. vm_refl. Qed.
Lemma D_524a8 : decode_any W_524a8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524ac : bv 32 := 0x00000073.
Lemma F_524ac : fetch_word Ubsan.M.loaded_segments (0x524ac : word) = Some W_524ac.
Proof. vm_refl. Qed.
Lemma D_524ac : decode_any W_524ac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_524ac : is_ecall W_524ac = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_524b0 : bv 32 := 0x02051513.
Lemma F_524b0 : fetch_word Ubsan.M.loaded_segments (0x524b0 : word) = Some W_524b0.
Proof. vm_refl. Qed.
Lemma D_524b0 : decode_any W_524b0 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524b4 : bv 32 := 0x00055463.
Lemma F_524b4 : fetch_word Ubsan.M.loaded_segments (0x524b4 : word) = Some W_524b4.
Proof. vm_refl. Qed.
Lemma D_524b4 : decode_any W_524b4 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524b8 : bv 32 := 0x00000023.
Lemma F_524b8 : fetch_word Ubsan.M.loaded_segments (0x524b8 : word) = Some W_524b8.
Proof. vm_refl. Qed.
Lemma D_524b8 : decode_any W_524b8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524bc : bv 32 := 0x01e15503.
Lemma F_524bc : fetch_word Ubsan.M.loaded_segments (0x524bc : word) = Some W_524bc.
Proof. vm_refl. Qed.
Lemma D_524bc : decode_any W_524bc = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524c0 : bv 32 := 0x02057513.
Lemma F_524c0 : fetch_word Ubsan.M.loaded_segments (0x524c0 : word) = Some W_524c0.
Proof. vm_refl. Qed.
Lemma D_524c0 : decode_any W_524c0 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524c4 : bv 32 := 0x02050463.
Lemma F_524c4 : fetch_word Ubsan.M.loaded_segments (0x524c4 : word) = Some W_524c4.
Proof. vm_refl. Qed.
Lemma D_524c4 : decode_any W_524c4 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524c8 : bv 32 := 0xfffc1517.
Lemma F_524c8 : fetch_word Ubsan.M.loaded_segments (0x524c8 : word) = Some W_524c8.
Proof. vm_refl. Qed.
Lemma D_524c8 : decode_any W_524c8 = Some (Auipc 10 1048513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524cc : bv 32 := 0x00008637.
Lemma F_524cc : fetch_word Ubsan.M.loaded_segments (0x524cc : word) = Some W_524cc.
Proof. vm_refl. Qed.
Lemma D_524cc : decode_any W_524cc = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524d0 : bv 32 := 0x03800893.
Lemma F_524d0 : fetch_word Ubsan.M.loaded_segments (0x524d0 : word) = Some W_524d0.
Proof. vm_refl. Qed.
Lemma D_524d0 : decode_any W_524d0 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524d4 : bv 32 := 0xa5e50593.
Lemma F_524d4 : fetch_word Ubsan.M.loaded_segments (0x524d4 : word) = Some W_524d4.
Proof. vm_refl. Qed.
Lemma D_524d4 : decode_any W_524d4 = Some (OpImm ALU_ADD 11 10 2654, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524d8 : bv 32 := 0x0026061b.
Lemma F_524d8 : fetch_word Ubsan.M.loaded_segments (0x524d8 : word) = Some W_524d8.
Proof. vm_refl. Qed.
Lemma D_524d8 : decode_any W_524d8 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524dc : bv 32 := 0xf9c00513.
Lemma F_524dc : fetch_word Ubsan.M.loaded_segments (0x524dc : word) = Some W_524dc.
Proof. vm_refl. Qed.
Lemma D_524dc : decode_any W_524dc = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524e0 : bv 32 := 0x00000073.
Lemma F_524e0 : fetch_word Ubsan.M.loaded_segments (0x524e0 : word) = Some W_524e0.
Proof. vm_refl. Qed.
Lemma D_524e0 : decode_any W_524e0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_524e0 : is_ecall W_524e0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_524e4 : bv 32 := 0x00055463.
Lemma F_524e4 : fetch_word Ubsan.M.loaded_segments (0x524e4 : word) = Some W_524e4.
Proof. vm_refl. Qed.
Lemma D_524e4 : decode_any W_524e4 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524e8 : bv 32 := 0x00000023.
Lemma F_524e8 : fetch_word Ubsan.M.loaded_segments (0x524e8 : word) = Some W_524e8.
Proof. vm_refl. Qed.
Lemma D_524e8 : decode_any W_524e8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524ec : bv 32 := 0x02615503.
Lemma F_524ec : fetch_word Ubsan.M.loaded_segments (0x524ec : word) = Some W_524ec.
Proof. vm_refl. Qed.
Lemma D_524ec : decode_any W_524ec = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524f0 : bv 32 := 0x02057513.
Lemma F_524f0 : fetch_word Ubsan.M.loaded_segments (0x524f0 : word) = Some W_524f0.
Proof. vm_refl. Qed.
Lemma D_524f0 : decode_any W_524f0 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524f4 : bv 32 := 0x02050463.
Lemma F_524f4 : fetch_word Ubsan.M.loaded_segments (0x524f4 : word) = Some W_524f4.
Proof. vm_refl. Qed.
Lemma D_524f4 : decode_any W_524f4 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524f8 : bv 32 := 0xfffc1517.
Lemma F_524f8 : fetch_word Ubsan.M.loaded_segments (0x524f8 : word) = Some W_524f8.
Proof. vm_refl. Qed.
Lemma D_524f8 : decode_any W_524f8 = Some (Auipc 10 1048513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_524fc : bv 32 := 0x00008637.
Lemma F_524fc : fetch_word Ubsan.M.loaded_segments (0x524fc : word) = Some W_524fc.
Proof. vm_refl. Qed.
Lemma D_524fc : decode_any W_524fc = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52500 : bv 32 := 0x03800893.
Lemma F_52500 : fetch_word Ubsan.M.loaded_segments (0x52500 : word) = Some W_52500.
Proof. vm_refl. Qed.
Lemma D_52500 : decode_any W_52500 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52504 : bv 32 := 0xa2e50593.
Lemma F_52504 : fetch_word Ubsan.M.loaded_segments (0x52504 : word) = Some W_52504.
Proof. vm_refl. Qed.
Lemma D_52504 : decode_any W_52504 = Some (OpImm ALU_ADD 11 10 2606, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52508 : bv 32 := 0x0026061b.
Lemma F_52508 : fetch_word Ubsan.M.loaded_segments (0x52508 : word) = Some W_52508.
Proof. vm_refl. Qed.
Lemma D_52508 : decode_any W_52508 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5250c : bv 32 := 0xf9c00513.
Lemma F_5250c : fetch_word Ubsan.M.loaded_segments (0x5250c : word) = Some W_5250c.
Proof. vm_refl. Qed.
Lemma D_5250c : decode_any W_5250c = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52510 : bv 32 := 0x00000073.
Lemma F_52510 : fetch_word Ubsan.M.loaded_segments (0x52510 : word) = Some W_52510.
Proof. vm_refl. Qed.
Lemma D_52510 : decode_any W_52510 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52510 : is_ecall W_52510 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52514 : bv 32 := 0x00055463.
Lemma F_52514 : fetch_word Ubsan.M.loaded_segments (0x52514 : word) = Some W_52514.
Proof. vm_refl. Qed.
Lemma D_52514 : decode_any W_52514 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52518 : bv 32 := 0x00000023.
Lemma F_52518 : fetch_word Ubsan.M.loaded_segments (0x52518 : word) = Some W_52518.
Proof. vm_refl. Qed.
Lemma D_52518 : decode_any W_52518 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5251c : bv 32 := 0x02e15503.
Lemma F_5251c : fetch_word Ubsan.M.loaded_segments (0x5251c : word) = Some W_5251c.
Proof. vm_refl. Qed.
Lemma D_5251c : decode_any W_5251c = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52520 : bv 32 := 0x02057513.
Lemma F_52520 : fetch_word Ubsan.M.loaded_segments (0x52520 : word) = Some W_52520.
Proof. vm_refl. Qed.
Lemma D_52520 : decode_any W_52520 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52524 : bv 32 := 0x02050463.
Lemma F_52524 : fetch_word Ubsan.M.loaded_segments (0x52524 : word) = Some W_52524.
Proof. vm_refl. Qed.
Lemma D_52524 : decode_any W_52524 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52528 : bv 32 := 0xfffc1517.
Lemma F_52528 : fetch_word Ubsan.M.loaded_segments (0x52528 : word) = Some W_52528.
Proof. vm_refl. Qed.
Lemma D_52528 : decode_any W_52528 = Some (Auipc 10 1048513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5252c : bv 32 := 0x00008637.
Lemma F_5252c : fetch_word Ubsan.M.loaded_segments (0x5252c : word) = Some W_5252c.
Proof. vm_refl. Qed.
Lemma D_5252c : decode_any W_5252c = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52530 : bv 32 := 0x03800893.
Lemma F_52530 : fetch_word Ubsan.M.loaded_segments (0x52530 : word) = Some W_52530.
Proof. vm_refl. Qed.
Lemma D_52530 : decode_any W_52530 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52534 : bv 32 := 0x9fe50593.
Lemma F_52534 : fetch_word Ubsan.M.loaded_segments (0x52534 : word) = Some W_52534.
Proof. vm_refl. Qed.
Lemma D_52534 : decode_any W_52534 = Some (OpImm ALU_ADD 11 10 2558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52538 : bv 32 := 0x0026061b.
Lemma F_52538 : fetch_word Ubsan.M.loaded_segments (0x52538 : word) = Some W_52538.
Proof. vm_refl. Qed.
Lemma D_52538 : decode_any W_52538 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5253c : bv 32 := 0xf9c00513.
Lemma F_5253c : fetch_word Ubsan.M.loaded_segments (0x5253c : word) = Some W_5253c.
Proof. vm_refl. Qed.
Lemma D_5253c : decode_any W_5253c = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52540 : bv 32 := 0x00000073.
Lemma F_52540 : fetch_word Ubsan.M.loaded_segments (0x52540 : word) = Some W_52540.
Proof. vm_refl. Qed.
Lemma D_52540 : decode_any W_52540 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52540 : is_ecall W_52540 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52544 : bv 32 := 0x00055463.
Lemma F_52544 : fetch_word Ubsan.M.loaded_segments (0x52544 : word) = Some W_52544.
Proof. vm_refl. Qed.
Lemma D_52544 : decode_any W_52544 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52548 : bv 32 := 0x00000023.
Lemma F_52548 : fetch_word Ubsan.M.loaded_segments (0x52548 : word) = Some W_52548.
Proof. vm_refl. Qed.
Lemma D_52548 : decode_any W_52548 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5254c : bv 32 := 0x00100513.
Lemma F_5254c : fetch_word Ubsan.M.loaded_segments (0x5254c : word) = Some W_5254c.
Proof. vm_refl. Qed.
Lemma D_5254c : decode_any W_5254c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52550 : bv 32 := 0x00a90123.
Lemma F_52550 : fetch_word Ubsan.M.loaded_segments (0x52550 : word) = Some W_52550.
Proof. vm_refl. Qed.
Lemma D_52550 : decode_any W_52550 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52554 : bv 32 := 0x17813083.
Lemma F_52554 : fetch_word Ubsan.M.loaded_segments (0x52554 : word) = Some W_52554.
Proof. vm_refl. Qed.
Lemma D_52554 : decode_any W_52554 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52558 : bv 32 := 0x17013403.
Lemma F_52558 : fetch_word Ubsan.M.loaded_segments (0x52558 : word) = Some W_52558.
Proof. vm_refl. Qed.
Lemma D_52558 : decode_any W_52558 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5255c : bv 32 := 0x16813483.
Lemma F_5255c : fetch_word Ubsan.M.loaded_segments (0x5255c : word) = Some W_5255c.
Proof. vm_refl. Qed.
Lemma D_5255c : decode_any W_5255c = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52560 : bv 32 := 0x16013903.
Lemma F_52560 : fetch_word Ubsan.M.loaded_segments (0x52560 : word) = Some W_52560.
Proof. vm_refl. Qed.
Lemma D_52560 : decode_any W_52560 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52564 : bv 32 := 0x18010113.
Lemma F_52564 : fetch_word Ubsan.M.loaded_segments (0x52564 : word) = Some W_52564.
Proof. vm_refl. Qed.
Lemma D_52564 : decode_any W_52564 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52568 : bv 32 := 0x00008067.
Lemma F_52568 : fetch_word Ubsan.M.loaded_segments (0x52568 : word) = Some W_52568.
Proof. vm_refl. Qed.
Lemma D_52568 : decode_any W_52568 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5256c : bv 32 := 0xfe010113.
Lemma F_5256c : fetch_word Ubsan.M.loaded_segments (0x5256c : word) = Some W_5256c.
Proof. vm_refl. Qed.
Lemma D_5256c : decode_any W_5256c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52570 : bv 32 := 0x00113c23.
Lemma F_52570 : fetch_word Ubsan.M.loaded_segments (0x52570 : word) = Some W_52570.
Proof. vm_refl. Qed.
Lemma D_52570 : decode_any W_52570 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52574 : bv 32 := 0x00813823.
Lemma F_52574 : fetch_word Ubsan.M.loaded_segments (0x52574 : word) = Some W_52574.
Proof. vm_refl. Qed.
Lemma D_52574 : decode_any W_52574 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52578 : bv 32 := 0x00913423.
Lemma F_52578 : fetch_word Ubsan.M.loaded_segments (0x52578 : word) = Some W_52578.
Proof. vm_refl. Qed.
Lemma D_52578 : decode_any W_52578 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5257c : bv 32 := 0xdc1ff0ef.
Lemma F_5257c : fetch_word Ubsan.M.loaded_segments (0x5257c : word) = Some W_5257c.
Proof. vm_refl. Qed.
Lemma D_5257c : decode_any W_5257c = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52580 : bv 32 := 0x00013517.
Lemma F_52580 : fetch_word Ubsan.M.loaded_segments (0x52580 : word) = Some W_52580.
Proof. vm_refl. Qed.
Lemma D_52580 : decode_any W_52580 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52584 : bv 32 := 0x00013597.
Lemma F_52584 : fetch_word Ubsan.M.loaded_segments (0x52584 : word) = Some W_52584.
Proof. vm_refl. Qed.
Lemma D_52584 : decode_any W_52584 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52588 : bv 32 := 0x5c853403.
Lemma F_52588 : fetch_word Ubsan.M.loaded_segments (0x52588 : word) = Some W_52588.
Proof. vm_refl. Qed.
Lemma D_52588 : decode_any W_52588 = Some (Load SZ8 true 8 10 1480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5258c : bv 32 := 0x5cc5b483.
Lemma F_5258c : fetch_word Ubsan.M.loaded_segments (0x5258c : word) = Some W_5258c.
Proof. vm_refl. Qed.
Lemma D_5258c : decode_any W_5258c = Some (Load SZ8 true 9 11 1484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52590 : bv 32 := 0x0084fa63.
Lemma F_52590 : fetch_word Ubsan.M.loaded_segments (0x52590 : word) = Some W_52590.
Proof. vm_refl. Qed.
Lemma D_52590 : decode_any W_52590 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52594 : bv 32 := 0x0004b503.
Lemma F_52594 : fetch_word Ubsan.M.loaded_segments (0x52594 : word) = Some W_52594.
Proof. vm_refl. Qed.
Lemma D_52594 : decode_any W_52594 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52598 : bv 32 := 0x000500e7.
Lemma F_52598 : fetch_word Ubsan.M.loaded_segments (0x52598 : word) = Some W_52598.
Proof. vm_refl. Qed.
Lemma D_52598 : decode_any W_52598 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5259c : bv 32 := 0x00848493.
Lemma F_5259c : fetch_word Ubsan.M.loaded_segments (0x5259c : word) = Some W_5259c.
Proof. vm_refl. Qed.
Lemma D_5259c : decode_any W_5259c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525a0 : bv 32 := 0xfe84eae3.
Lemma F_525a0 : fetch_word Ubsan.M.loaded_segments (0x525a0 : word) = Some W_525a0.
Proof. vm_refl. Qed.
Lemma D_525a0 : decode_any W_525a0 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525a4 : bv 32 := 0x01813083.
Lemma F_525a4 : fetch_word Ubsan.M.loaded_segments (0x525a4 : word) = Some W_525a4.
Proof. vm_refl. Qed.
Lemma D_525a4 : decode_any W_525a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525a8 : bv 32 := 0x01013403.
Lemma F_525a8 : fetch_word Ubsan.M.loaded_segments (0x525a8 : word) = Some W_525a8.
Proof. vm_refl. Qed.
Lemma D_525a8 : decode_any W_525a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525ac : bv 32 := 0x00813483.
Lemma F_525ac : fetch_word Ubsan.M.loaded_segments (0x525ac : word) = Some W_525ac.
Proof. vm_refl. Qed.
Lemma D_525ac : decode_any W_525ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525b0 : bv 32 := 0x02010113.
Lemma F_525b0 : fetch_word Ubsan.M.loaded_segments (0x525b0 : word) = Some W_525b0.
Proof. vm_refl. Qed.
Lemma D_525b0 : decode_any W_525b0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525b4 : bv 32 := 0x00008067.
Lemma F_525b4 : fetch_word Ubsan.M.loaded_segments (0x525b4 : word) = Some W_525b4.
Proof. vm_refl. Qed.
Lemma D_525b4 : decode_any W_525b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525b8 : bv 32 := 0xfe010113.
Lemma F_525b8 : fetch_word Ubsan.M.loaded_segments (0x525b8 : word) = Some W_525b8.
Proof. vm_refl. Qed.
Lemma D_525b8 : decode_any W_525b8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525bc : bv 32 := 0x00113c23.
Lemma F_525bc : fetch_word Ubsan.M.loaded_segments (0x525bc : word) = Some W_525bc.
Proof. vm_refl. Qed.
Lemma D_525bc : decode_any W_525bc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525c0 : bv 32 := 0x00813823.
Lemma F_525c0 : fetch_word Ubsan.M.loaded_segments (0x525c0 : word) = Some W_525c0.
Proof. vm_refl. Qed.
Lemma D_525c0 : decode_any W_525c0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525c4 : bv 32 := 0x00913423.
Lemma F_525c4 : fetch_word Ubsan.M.loaded_segments (0x525c4 : word) = Some W_525c4.
Proof. vm_refl. Qed.
Lemma D_525c4 : decode_any W_525c4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525c8 : bv 32 := 0x01213023.
Lemma F_525c8 : fetch_word Ubsan.M.loaded_segments (0x525c8 : word) = Some W_525c8.
Proof. vm_refl. Qed.
Lemma D_525c8 : decode_any W_525c8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525cc : bv 32 := 0x00060413.
Lemma F_525cc : fetch_word Ubsan.M.loaded_segments (0x525cc : word) = Some W_525cc.
Proof. vm_refl. Qed.
Lemma D_525cc : decode_any W_525cc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525d0 : bv 32 := 0x00058493.
Lemma F_525d0 : fetch_word Ubsan.M.loaded_segments (0x525d0 : word) = Some W_525d0.
Proof. vm_refl. Qed.
Lemma D_525d0 : decode_any W_525d0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525d4 : bv 32 := 0x00050913.
Lemma F_525d4 : fetch_word Ubsan.M.loaded_segments (0x525d4 : word) = Some W_525d4.
Proof. vm_refl. Qed.
Lemma D_525d4 : decode_any W_525d4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525d8 : bv 32 := 0x00063583.
Lemma F_525d8 : fetch_word Ubsan.M.loaded_segments (0x525d8 : word) = Some W_525d8.
Proof. vm_refl. Qed.
Lemma D_525d8 : decode_any W_525d8 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525dc : bv 32 := 0x00349513.
Lemma F_525dc : fetch_word Ubsan.M.loaded_segments (0x525dc : word) = Some W_525dc.
Proof. vm_refl. Qed.
Lemma D_525dc : decode_any W_525dc = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525e0 : bv 32 := 0x00a60533.
Lemma F_525e0 : fetch_word Ubsan.M.loaded_segments (0x525e0 : word) = Some W_525e0.
Proof. vm_refl. Qed.
Lemma D_525e0 : decode_any W_525e0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525e4 : bv 32 := 0x00850513.
Lemma F_525e4 : fetch_word Ubsan.M.loaded_segments (0x525e4 : word) = Some W_525e4.
Proof. vm_refl. Qed.
Lemma D_525e4 : decode_any W_525e4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525e8 : bv 32 := 0xd59ff0ef.
Lemma F_525e8 : fetch_word Ubsan.M.loaded_segments (0x525e8 : word) = Some W_525e8.
Proof. vm_refl. Qed.
Lemma D_525e8 : decode_any W_525e8 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525ec : bv 32 := 0x00000517.
Lemma F_525ec : fetch_word Ubsan.M.loaded_segments (0x525ec : word) = Some W_525ec.
Proof. vm_refl. Qed.
Lemma D_525ec : decode_any W_525ec = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525f0 : bv 32 := 0x02c50313.
Lemma F_525f0 : fetch_word Ubsan.M.loaded_segments (0x525f0 : word) = Some W_525f0.
Proof. vm_refl. Qed.
Lemma D_525f0 : decode_any W_525f0 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525f4 : bv 32 := 0x00090513.
Lemma F_525f4 : fetch_word Ubsan.M.loaded_segments (0x525f4 : word) = Some W_525f4.
Proof. vm_refl. Qed.
Lemma D_525f4 : decode_any W_525f4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525f8 : bv 32 := 0x00048593.
Lemma F_525f8 : fetch_word Ubsan.M.loaded_segments (0x525f8 : word) = Some W_525f8.
Proof. vm_refl. Qed.
Lemma D_525f8 : decode_any W_525f8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_525fc : bv 32 := 0x00040613.
Lemma F_525fc : fetch_word Ubsan.M.loaded_segments (0x525fc : word) = Some W_525fc.
Proof. vm_refl. Qed.
Lemma D_525fc : decode_any W_525fc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52600 : bv 32 := 0x01813083.
Lemma F_52600 : fetch_word Ubsan.M.loaded_segments (0x52600 : word) = Some W_52600.
Proof. vm_refl. Qed.
Lemma D_52600 : decode_any W_52600 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52604 : bv 32 := 0x01013403.
Lemma F_52604 : fetch_word Ubsan.M.loaded_segments (0x52604 : word) = Some W_52604.
Proof. vm_refl. Qed.
Lemma D_52604 : decode_any W_52604 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52608 : bv 32 := 0x00813483.
Lemma F_52608 : fetch_word Ubsan.M.loaded_segments (0x52608 : word) = Some W_52608.
Proof. vm_refl. Qed.
Lemma D_52608 : decode_any W_52608 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5260c : bv 32 := 0x00013903.
Lemma F_5260c : fetch_word Ubsan.M.loaded_segments (0x5260c : word) = Some W_5260c.
Proof. vm_refl. Qed.
Lemma D_5260c : decode_any W_5260c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52610 : bv 32 := 0x02010113.
Lemma F_52610 : fetch_word Ubsan.M.loaded_segments (0x52610 : word) = Some W_52610.
Proof. vm_refl. Qed.
Lemma D_52610 : decode_any W_52610 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52614 : bv 32 := 0x00030067.
Lemma F_52614 : fetch_word Ubsan.M.loaded_segments (0x52614 : word) = Some W_52614.
Proof. vm_refl. Qed.
Lemma D_52614 : decode_any W_52614 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52618 : bv 32 := 0xfd010113.
Lemma F_52618 : fetch_word Ubsan.M.loaded_segments (0x52618 : word) = Some W_52618.
Proof. vm_refl. Qed.
Lemma D_52618 : decode_any W_52618 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5261c : bv 32 := 0x02113423.
Lemma F_5261c : fetch_word Ubsan.M.loaded_segments (0x5261c : word) = Some W_5261c.
Proof. vm_refl. Qed.
Lemma D_5261c : decode_any W_5261c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52620 : bv 32 := 0x02813023.
Lemma F_52620 : fetch_word Ubsan.M.loaded_segments (0x52620 : word) = Some W_52620.
Proof. vm_refl. Qed.
Lemma D_52620 : decode_any W_52620 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52624 : bv 32 := 0x00913c23.
Lemma F_52624 : fetch_word Ubsan.M.loaded_segments (0x52624 : word) = Some W_52624.
Proof. vm_refl. Qed.
Lemma D_52624 : decode_any W_52624 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52628 : bv 32 := 0x01213823.
Lemma F_52628 : fetch_word Ubsan.M.loaded_segments (0x52628 : word) = Some W_52628.
Proof. vm_refl. Qed.
Lemma D_52628 : decode_any W_52628 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5262c : bv 32 := 0x01313423.
Lemma F_5262c : fetch_word Ubsan.M.loaded_segments (0x5262c : word) = Some W_5262c.
Proof. vm_refl. Qed.
Lemma D_5262c : decode_any W_5262c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52630 : bv 32 := 0x00060413.
Lemma F_52630 : fetch_word Ubsan.M.loaded_segments (0x52630 : word) = Some W_52630.
Proof. vm_refl. Qed.
Lemma D_52630 : decode_any W_52630 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52634 : bv 32 := 0x00058493.
Lemma F_52634 : fetch_word Ubsan.M.loaded_segments (0x52634 : word) = Some W_52634.
Proof. vm_refl. Qed.
Lemma D_52634 : decode_any W_52634 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52638 : bv 32 := 0x00050913.
Lemma F_52638 : fetch_word Ubsan.M.loaded_segments (0x52638 : word) = Some W_52638.
Proof. vm_refl. Qed.
Lemma D_52638 : decode_any W_52638 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5263c : bv 32 := 0x00359513.
Lemma F_5263c : fetch_word Ubsan.M.loaded_segments (0x5263c : word) = Some W_5263c.
Proof. vm_refl. Qed.
Lemma D_5263c : decode_any W_5263c = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52640 : bv 32 := 0x00a60533.
Lemma F_52640 : fetch_word Ubsan.M.loaded_segments (0x52640 : word) = Some W_52640.
Proof. vm_refl. Qed.
Lemma D_52640 : decode_any W_52640 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52644 : bv 32 := 0x00850993.
Lemma F_52644 : fetch_word Ubsan.M.loaded_segments (0x52644 : word) = Some W_52644.
Proof. vm_refl. Qed.
Lemma D_52644 : decode_any W_52644 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52648 : bv 32 := 0xf25ff0ef.
Lemma F_52648 : fetch_word Ubsan.M.loaded_segments (0x52648 : word) = Some W_52648.
Proof. vm_refl. Qed.
Lemma D_52648 : decode_any W_52648 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5264c : bv 32 := 0x00048513.
Lemma F_5264c : fetch_word Ubsan.M.loaded_segments (0x5264c : word) = Some W_5264c.
Proof. vm_refl. Qed.
Lemma D_5264c : decode_any W_5264c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52650 : bv 32 := 0x00040593.
Lemma F_52650 : fetch_word Ubsan.M.loaded_segments (0x52650 : word) = Some W_52650.
Proof. vm_refl. Qed.
Lemma D_52650 : decode_any W_52650 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52654 : bv 32 := 0x00098613.
Lemma F_52654 : fetch_word Ubsan.M.loaded_segments (0x52654 : word) = Some W_52654.
Proof. vm_refl. Qed.
Lemma D_52654 : decode_any W_52654 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52658 : bv 32 := 0x000900e7.
Lemma F_52658 : fetch_word Ubsan.M.loaded_segments (0x52658 : word) = Some W_52658.
Proof. vm_refl. Qed.
Lemma D_52658 : decode_any W_52658 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5265c : bv 32 := 0x584000ef.
Lemma F_5265c : fetch_word Ubsan.M.loaded_segments (0x5265c : word) = Some W_5265c.
Proof. vm_refl. Qed.
Lemma D_5265c : decode_any W_5265c = Some (Jal 1 1412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52910 : bv 32 := 0x00020513.
Lemma F_52910 : fetch_word Ubsan.M.loaded_segments (0x52910 : word) = Some W_52910.
Proof. vm_refl. Qed.
Lemma D_52910 : decode_any W_52910 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52914 : bv 32 := 0xf5c50513.
Lemma F_52914 : fetch_word Ubsan.M.loaded_segments (0x52914 : word) = Some W_52914.
Proof. vm_refl. Qed.
Lemma D_52914 : decode_any W_52914 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52918 : bv 32 := 0x00008067.
Lemma F_52918 : fetch_word Ubsan.M.loaded_segments (0x52918 : word) = Some W_52918.
Proof. vm_refl. Qed.
Lemma D_52918 : decode_any W_52918 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5291c : bv 32 := 0xfd010113.
Lemma F_5291c : fetch_word Ubsan.M.loaded_segments (0x5291c : word) = Some W_5291c.
Proof. vm_refl. Qed.
Lemma D_5291c : decode_any W_5291c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52920 : bv 32 := 0x02113423.
Lemma F_52920 : fetch_word Ubsan.M.loaded_segments (0x52920 : word) = Some W_52920.
Proof. vm_refl. Qed.
Lemma D_52920 : decode_any W_52920 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52924 : bv 32 := 0x00600513.
Lemma F_52924 : fetch_word Ubsan.M.loaded_segments (0x52924 : word) = Some W_52924.
Proof. vm_refl. Qed.
Lemma D_52924 : decode_any W_52924 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52928 : bv 32 := 0x265020ef.
Lemma F_52928 : fetch_word Ubsan.M.loaded_segments (0x52928 : word) = Some W_52928.
Proof. vm_refl. Qed.
Lemma D_52928 : decode_any W_52928 = Some (Jal 1 10852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5292c : bv 32 := 0x00000513.
Lemma F_5292c : fetch_word Ubsan.M.loaded_segments (0x5292c : word) = Some W_5292c.
Proof. vm_refl. Qed.
Lemma D_5292c : decode_any W_5292c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52930 : bv 32 := 0x201020ef.
Lemma F_52930 : fetch_word Ubsan.M.loaded_segments (0x52930 : word) = Some W_52930.
Proof. vm_refl. Qed.
Lemma D_52930 : decode_any W_52930 = Some (Jal 1 10752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52934 : bv 32 := 0x00045517.
Lemma F_52934 : fetch_word Ubsan.M.loaded_segments (0x52934 : word) = Some W_52934.
Proof. vm_refl. Qed.
Lemma D_52934 : decode_any W_52934 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52938 : bv 32 := 0x09c50513.
Lemma F_52938 : fetch_word Ubsan.M.loaded_segments (0x52938 : word) = Some W_52938.
Proof. vm_refl. Qed.
Lemma D_52938 : decode_any W_52938 = Some (OpImm ALU_ADD 10 10 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5293c : bv 32 := 0x7d90d0ef.
Lemma F_5293c : fetch_word Ubsan.M.loaded_segments (0x5293c : word) = Some W_5293c.
Proof. vm_refl. Qed.
Lemma D_5293c : decode_any W_5293c = Some (Jal 1 57304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52940 : bv 32 := 0x00000613.
Lemma F_52940 : fetch_word Ubsan.M.loaded_segments (0x52940 : word) = Some W_52940.
Proof. vm_refl. Qed.
Lemma D_52940 : decode_any W_52940 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52944 : bv 32 := 0x00013423.
Lemma F_52944 : fetch_word Ubsan.M.loaded_segments (0x52944 : word) = Some W_52944.
Proof. vm_refl. Qed.
Lemma D_52944 : decode_any W_52944 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52948 : bv 32 := 0x00013823.
Lemma F_52948 : fetch_word Ubsan.M.loaded_segments (0x52948 : word) = Some W_52948.
Proof. vm_refl. Qed.
Lemma D_52948 : decode_any W_52948 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5294c : bv 32 := 0x00013c23.
Lemma F_5294c : fetch_word Ubsan.M.loaded_segments (0x5294c : word) = Some W_5294c.
Proof. vm_refl. Qed.
Lemma D_5294c : decode_any W_5294c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52950 : bv 32 := 0x02013023.
Lemma F_52950 : fetch_word Ubsan.M.loaded_segments (0x52950 : word) = Some W_52950.
Proof. vm_refl. Qed.
Lemma D_52950 : decode_any W_52950 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52954 : bv 32 := 0x08600893.
Lemma F_52954 : fetch_word Ubsan.M.loaded_segments (0x52954 : word) = Some W_52954.
Proof. vm_refl. Qed.
Lemma D_52954 : decode_any W_52954 = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52958 : bv 32 := 0x00600513.
Lemma F_52958 : fetch_word Ubsan.M.loaded_segments (0x52958 : word) = Some W_52958.
Proof. vm_refl. Qed.
Lemma D_52958 : decode_any W_52958 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5295c : bv 32 := 0x00810593.
Lemma F_5295c : fetch_word Ubsan.M.loaded_segments (0x5295c : word) = Some W_5295c.
Proof. vm_refl. Qed.
Lemma D_5295c : decode_any W_5295c = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52960 : bv 32 := 0x00800693.
Lemma F_52960 : fetch_word Ubsan.M.loaded_segments (0x52960 : word) = Some W_52960.
Proof. vm_refl. Qed.
Lemma D_52960 : decode_any W_52960 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52964 : bv 32 := 0x00000073.
Lemma F_52964 : fetch_word Ubsan.M.loaded_segments (0x52964 : word) = Some W_52964.
Proof. vm_refl. Qed.
Lemma D_52964 : decode_any W_52964 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52964 : is_ecall W_52964 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52968 : bv 32 := 0x00020513.
Lemma F_52968 : fetch_word Ubsan.M.loaded_segments (0x52968 : word) = Some W_52968.
Proof. vm_refl. Qed.
Lemma D_52968 : decode_any W_52968 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5296c : bv 32 := 0xf5852503.
Lemma F_5296c : fetch_word Ubsan.M.loaded_segments (0x5296c : word) = Some W_5296c.
Proof. vm_refl. Qed.
Lemma D_5296c : decode_any W_5296c = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52970 : bv 32 := 0x02000613.
Lemma F_52970 : fetch_word Ubsan.M.loaded_segments (0x52970 : word) = Some W_52970.
Proof. vm_refl. Qed.
Lemma D_52970 : decode_any W_52970 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52974 : bv 32 := 0x08200893.
Lemma F_52974 : fetch_word Ubsan.M.loaded_segments (0x52974 : word) = Some W_52974.
Proof. vm_refl. Qed.
Lemma D_52974 : decode_any W_52974 = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52978 : bv 32 := 0x00600593.
Lemma F_52978 : fetch_word Ubsan.M.loaded_segments (0x52978 : word) = Some W_52978.
Proof. vm_refl. Qed.
Lemma D_52978 : decode_any W_52978 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5297c : bv 32 := 0x00000073.
Lemma F_5297c : fetch_word Ubsan.M.loaded_segments (0x5297c : word) = Some W_5297c.
Proof. vm_refl. Qed.
Lemma D_5297c : decode_any W_5297c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5297c : is_ecall W_5297c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52980 : bv 32 := 0x00c13023.
Lemma F_52980 : fetch_word Ubsan.M.loaded_segments (0x52980 : word) = Some W_52980.
Proof. vm_refl. Qed.
Lemma D_52980 : decode_any W_52980 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52984 : bv 32 := 0x08700893.
Lemma F_52984 : fetch_word Ubsan.M.loaded_segments (0x52984 : word) = Some W_52984.
Proof. vm_refl. Qed.
Lemma D_52984 : decode_any W_52984 = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52988 : bv 32 := 0x00010593.
Lemma F_52988 : fetch_word Ubsan.M.loaded_segments (0x52988 : word) = Some W_52988.
Proof. vm_refl. Qed.
Lemma D_52988 : decode_any W_52988 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5298c : bv 32 := 0x00100513.
Lemma F_5298c : fetch_word Ubsan.M.loaded_segments (0x5298c : word) = Some W_5298c.
Proof. vm_refl. Qed.
Lemma D_5298c : decode_any W_5298c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52990 : bv 32 := 0x00800693.
Lemma F_52990 : fetch_word Ubsan.M.loaded_segments (0x52990 : word) = Some W_52990.
Proof. vm_refl. Qed.
Lemma D_52990 : decode_any W_52990 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52994 : bv 32 := 0x00000613.
Lemma F_52994 : fetch_word Ubsan.M.loaded_segments (0x52994 : word) = Some W_52994.
Proof. vm_refl. Qed.
Lemma D_52994 : decode_any W_52994 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52998 : bv 32 := 0x00000073.
Lemma F_52998 : fetch_word Ubsan.M.loaded_segments (0x52998 : word) = Some W_52998.
Proof. vm_refl. Qed.
Lemma D_52998 : decode_any W_52998 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52998 : is_ecall W_52998 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5299c : bv 32 := 0x00000023.
Lemma F_5299c : fetch_word Ubsan.M.loaded_segments (0x5299c : word) = Some W_5299c.
Proof. vm_refl. Qed.
Lemma D_5299c : decode_any W_5299c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529a0 : bv 32 := 0x00900513.
Lemma F_529a0 : fetch_word Ubsan.M.loaded_segments (0x529a0 : word) = Some W_529a0.
Proof. vm_refl. Qed.
Lemma D_529a0 : decode_any W_529a0 = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529a4 : bv 32 := 0x1e9020ef.
Lemma F_529a4 : fetch_word Ubsan.M.loaded_segments (0x529a4 : word) = Some W_529a4.
Proof. vm_refl. Qed.
Lemma D_529a4 : decode_any W_529a4 = Some (Jal 1 10728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529a8 : bv 32 := 0x07f00513.
Lemma F_529a8 : fetch_word Ubsan.M.loaded_segments (0x529a8 : word) = Some W_529a8.
Proof. vm_refl. Qed.
Lemma D_529a8 : decode_any W_529a8 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529ac : bv 32 := 0x004000ef.
Lemma F_529ac : fetch_word Ubsan.M.loaded_segments (0x529ac : word) = Some W_529ac.
Proof. vm_refl. Qed.
Lemma D_529ac : decode_any W_529ac = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529b0 : bv 32 := 0x00050593.
Lemma F_529b0 : fetch_word Ubsan.M.loaded_segments (0x529b0 : word) = Some W_529b0.
Proof. vm_refl. Qed.
Lemma D_529b0 : decode_any W_529b0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529b4 : bv 32 := 0x05e00893.
Lemma F_529b4 : fetch_word Ubsan.M.loaded_segments (0x529b4 : word) = Some W_529b4.
Proof. vm_refl. Qed.
Lemma D_529b4 : decode_any W_529b4 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529b8 : bv 32 := 0x00000073.
Lemma F_529b8 : fetch_word Ubsan.M.loaded_segments (0x529b8 : word) = Some W_529b8.
Proof. vm_refl. Qed.
Lemma D_529b8 : decode_any W_529b8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_529b8 : is_ecall W_529b8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_529bc : bv 32 := 0x05d00893.
Lemma F_529bc : fetch_word Ubsan.M.loaded_segments (0x529bc : word) = Some W_529bc.
Proof. vm_refl. Qed.
Lemma D_529bc : decode_any W_529bc = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529c0 : bv 32 := 0x00058513.
Lemma F_529c0 : fetch_word Ubsan.M.loaded_segments (0x529c0 : word) = Some W_529c0.
Proof. vm_refl. Qed.
Lemma D_529c0 : decode_any W_529c0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529c4 : bv 32 := 0x00000073.
Lemma F_529c4 : fetch_word Ubsan.M.loaded_segments (0x529c4 : word) = Some W_529c4.
Proof. vm_refl. Qed.
Lemma D_529c4 : decode_any W_529c4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_529c4 : is_ecall W_529c4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_529c8 : bv 32 := 0xff9ff06f.
Lemma F_529c8 : fetch_word Ubsan.M.loaded_segments (0x529c8 : word) = Some W_529c8.
Proof. vm_refl. Qed.
Lemma D_529c8 : decode_any W_529c8 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529cc : bv 32 := 0xff010113.
Lemma F_529cc : fetch_word Ubsan.M.loaded_segments (0x529cc : word) = Some W_529cc.
Proof. vm_refl. Qed.
Lemma D_529cc : decode_any W_529cc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529d0 : bv 32 := 0x00113423.
Lemma F_529d0 : fetch_word Ubsan.M.loaded_segments (0x529d0 : word) = Some W_529d0.
Proof. vm_refl. Qed.
Lemma D_529d0 : decode_any W_529d0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529d4 : bv 32 := 0x00068713.
Lemma F_529d4 : fetch_word Ubsan.M.loaded_segments (0x529d4 : word) = Some W_529d4.
Proof. vm_refl. Qed.
Lemma D_529d4 : decode_any W_529d4 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529d8 : bv 32 := 0x00060793.
Lemma F_529d8 : fetch_word Ubsan.M.loaded_segments (0x529d8 : word) = Some W_529d8.
Proof. vm_refl. Qed.
Lemma D_529d8 : decode_any W_529d8 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529dc : bv 32 := 0x00058693.
Lemma F_529dc : fetch_word Ubsan.M.loaded_segments (0x529dc : word) = Some W_529dc.
Proof. vm_refl. Qed.
Lemma D_529dc : decode_any W_529dc = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529e0 : bv 32 := 0x00050613.
Lemma F_529e0 : fetch_word Ubsan.M.loaded_segments (0x529e0 : word) = Some W_529e0.
Proof. vm_refl. Qed.
Lemma D_529e0 : decode_any W_529e0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529e4 : bv 32 := 0x00014517.
Lemma F_529e4 : fetch_word Ubsan.M.loaded_segments (0x529e4 : word) = Some W_529e4.
Proof. vm_refl. Qed.
Lemma D_529e4 : decode_any W_529e4 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529e8 : bv 32 := 0xfffbf597.
Lemma F_529e8 : fetch_word Ubsan.M.loaded_segments (0x529e8 : word) = Some W_529e8.
Proof. vm_refl. Qed.
Lemma D_529e8 : decode_any W_529e8 = Some (Auipc 11 1048511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529ec : bv 32 := 0x1f450513.
Lemma F_529ec : fetch_word Ubsan.M.loaded_segments (0x529ec : word) = Some W_529ec.
Proof. vm_refl. Qed.
Lemma D_529ec : decode_any W_529ec = Some (OpImm ALU_ADD 10 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529f0 : bv 32 := 0x83b58593.
Lemma F_529f0 : fetch_word Ubsan.M.loaded_segments (0x529f0 : word) = Some W_529f0.
Proof. vm_refl. Qed.
Lemma D_529f0 : decode_any W_529f0 = Some (OpImm ALU_ADD 11 11 2107, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529f4 : bv 32 := 0x4dd020ef.
Lemma F_529f4 : fetch_word Ubsan.M.loaded_segments (0x529f4 : word) = Some W_529f4.
Proof. vm_refl. Qed.
Lemma D_529f4 : decode_any W_529f4 = Some (Jal 1 11484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529f8 : bv 32 := 0xf25ff0ef.
Lemma F_529f8 : fetch_word Ubsan.M.loaded_segments (0x529f8 : word) = Some W_529f8.
Proof. vm_refl. Qed.
Lemma D_529f8 : decode_any W_529f8 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_529fc : bv 32 := 0xfd010113.
Lemma F_529fc : fetch_word Ubsan.M.loaded_segments (0x529fc : word) = Some W_529fc.
Proof. vm_refl. Qed.
Lemma D_529fc : decode_any W_529fc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a00 : bv 32 := 0x02113423.
Lemma F_52a00 : fetch_word Ubsan.M.loaded_segments (0x52a00 : word) = Some W_52a00.
Proof. vm_refl. Qed.
Lemma D_52a00 : decode_any W_52a00 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a04 : bv 32 := 0x02813023.
Lemma F_52a04 : fetch_word Ubsan.M.loaded_segments (0x52a04 : word) = Some W_52a04.
Proof. vm_refl. Qed.
Lemma D_52a04 : decode_any W_52a04 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a08 : bv 32 := 0x00913c23.
Lemma F_52a08 : fetch_word Ubsan.M.loaded_segments (0x52a08 : word) = Some W_52a08.
Proof. vm_refl. Qed.
Lemma D_52a08 : decode_any W_52a08 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a0c : bv 32 := 0x01213823.
Lemma F_52a0c : fetch_word Ubsan.M.loaded_segments (0x52a0c : word) = Some W_52a0c.
Proof. vm_refl. Qed.
Lemma D_52a0c : decode_any W_52a0c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a10 : bv 32 := 0x01313423.
Lemma F_52a10 : fetch_word Ubsan.M.loaded_segments (0x52a10 : word) = Some W_52a10.
Proof. vm_refl. Qed.
Lemma D_52a10 : decode_any W_52a10 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a14 : bv 32 := 0x00045517.
Lemma F_52a14 : fetch_word Ubsan.M.loaded_segments (0x52a14 : word) = Some W_52a14.
Proof. vm_refl. Qed.
Lemma D_52a14 : decode_any W_52a14 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a18 : bv 32 := 0xfc450913.
Lemma F_52a18 : fetch_word Ubsan.M.loaded_segments (0x52a18 : word) = Some W_52a18.
Proof. vm_refl. Qed.
Lemma D_52a18 : decode_any W_52a18 = Some (OpImm ALU_ADD 18 10 4036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a1c : bv 32 := 0x00490413.
Lemma F_52a1c : fetch_word Ubsan.M.loaded_segments (0x52a1c : word) = Some W_52a1c.
Proof. vm_refl. Qed.
Lemma D_52a1c : decode_any W_52a1c = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a20 : bv 32 := 0x00040513.
Lemma F_52a20 : fetch_word Ubsan.M.loaded_segments (0x52a20 : word) = Some W_52a20.
Proof. vm_refl. Qed.
Lemma D_52a20 : decode_any W_52a20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a24 : bv 32 := 0x6f10d0ef.
Lemma F_52a24 : fetch_word Ubsan.M.loaded_segments (0x52a24 : word) = Some W_52a24.
Proof. vm_refl. Qed.
Lemma D_52a24 : decode_any W_52a24 = Some (Jal 1 57072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a28 : bv 32 := 0x01093503.
Lemma F_52a28 : fetch_word Ubsan.M.loaded_segments (0x52a28 : word) = Some W_52a28.
Proof. vm_refl. Qed.
Lemma D_52a28 : decode_any W_52a28 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a2c : bv 32 := 0x06050863.
Lemma F_52a2c : fetch_word Ubsan.M.loaded_segments (0x52a2c : word) = Some W_52a2c.
Proof. vm_refl. Qed.
Lemma D_52a2c : decode_any W_52a2c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a30 : bv 32 := 0x00892583.
Lemma F_52a30 : fetch_word Ubsan.M.loaded_segments (0x52a30 : word) = Some W_52a30.
Proof. vm_refl. Qed.
Lemma D_52a30 : decode_any W_52a30 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a34 : bv 32 := 0x0180006f.
Lemma F_52a34 : fetch_word Ubsan.M.loaded_segments (0x52a34 : word) = Some W_52a34.
Proof. vm_refl. Qed.
Lemma D_52a34 : decode_any W_52a34 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a38 : bv 32 := 0x00053503.
Lemma F_52a38 : fetch_word Ubsan.M.loaded_segments (0x52a38 : word) = Some W_52a38.
Proof. vm_refl. Qed.
Lemma D_52a38 : decode_any W_52a38 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a3c : bv 32 := 0x02000593.
Lemma F_52a3c : fetch_word Ubsan.M.loaded_segments (0x52a3c : word) = Some W_52a3c.
Proof. vm_refl. Qed.
Lemma D_52a3c : decode_any W_52a3c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a40 : bv 32 := 0x00b92423.
Lemma F_52a40 : fetch_word Ubsan.M.loaded_segments (0x52a40 : word) = Some W_52a40.
Proof. vm_refl. Qed.
Lemma D_52a40 : decode_any W_52a40 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a44 : bv 32 := 0x00a93823.
Lemma F_52a44 : fetch_word Ubsan.M.loaded_segments (0x52a44 : word) = Some W_52a44.
Proof. vm_refl. Qed.
Lemma D_52a44 : decode_any W_52a44 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a48 : bv 32 := 0x04050a63.
Lemma F_52a48 : fetch_word Ubsan.M.loaded_segments (0x52a48 : word) = Some W_52a48.
Proof. vm_refl. Qed.
Lemma D_52a48 : decode_any W_52a48 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4c : bv 32 := 0xfff5861b.
Lemma F_52a4c : fetch_word Ubsan.M.loaded_segments (0x52a4c : word) = Some W_52a4c.
Proof. vm_refl. Qed.
Lemma D_52a4c : decode_any W_52a4c = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a50 : bv 32 := 0x00c92423.
Lemma F_52a50 : fetch_word Ubsan.M.loaded_segments (0x52a50 : word) = Some W_52a50.
Proof. vm_refl. Qed.
Lemma D_52a50 : decode_any W_52a50 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a54 : bv 32 := 0xfeb052e3.
Lemma F_52a54 : fetch_word Ubsan.M.loaded_segments (0x52a54 : word) = Some W_52a54.
Proof. vm_refl. Qed.
Lemma D_52a54 : decode_any W_52a54 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a58 : bv 32 := 0x01093503.
Lemma F_52a58 : fetch_word Ubsan.M.loaded_segments (0x52a58 : word) = Some W_52a58.
Proof. vm_refl. Qed.
Lemma D_52a58 : decode_any W_52a58 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5c : bv 32 := 0x00361613.
Lemma F_52a5c : fetch_word Ubsan.M.loaded_segments (0x52a5c : word) = Some W_52a5c.
Proof. vm_refl. Qed.
Lemma D_52a5c : decode_any W_52a5c = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a60 : bv 32 := 0x00c50533.
Lemma F_52a60 : fetch_word Ubsan.M.loaded_segments (0x52a60 : word) = Some W_52a60.
Proof. vm_refl. Qed.
Lemma D_52a60 : decode_any W_52a60 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a64 : bv 32 := 0x00853983.
Lemma F_52a64 : fetch_word Ubsan.M.loaded_segments (0x52a64 : word) = Some W_52a64.
Proof. vm_refl. Qed.
Lemma D_52a64 : decode_any W_52a64 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a68 : bv 32 := 0x10853483.
Lemma F_52a68 : fetch_word Ubsan.M.loaded_segments (0x52a68 : word) = Some W_52a68.
Proof. vm_refl. Qed.
Lemma D_52a68 : decode_any W_52a68 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6c : bv 32 := 0x00040513.
Lemma F_52a6c : fetch_word Ubsan.M.loaded_segments (0x52a6c : word) = Some W_52a6c.
Proof. vm_refl. Qed.
Lemma D_52a6c : decode_any W_52a6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a70 : bv 32 := 0x12c0e0ef.
Lemma F_52a70 : fetch_word Ubsan.M.loaded_segments (0x52a70 : word) = Some W_52a70.
Proof. vm_refl. Qed.
Lemma D_52a70 : decode_any W_52a70 = Some (Jal 1 57644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a74 : bv 32 := 0x00048513.
Lemma F_52a74 : fetch_word Ubsan.M.loaded_segments (0x52a74 : word) = Some W_52a74.
Proof. vm_refl. Qed.
Lemma D_52a74 : decode_any W_52a74 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a78 : bv 32 := 0x000980e7.
Lemma F_52a78 : fetch_word Ubsan.M.loaded_segments (0x52a78 : word) = Some W_52a78.
Proof. vm_refl. Qed.
Lemma D_52a78 : decode_any W_52a78 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7c : bv 32 := 0x00040513.
Lemma F_52a7c : fetch_word Ubsan.M.loaded_segments (0x52a7c : word) = Some W_52a7c.
Proof. vm_refl. Qed.
Lemma D_52a7c : decode_any W_52a7c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a80 : bv 32 := 0x6950d0ef.
Lemma F_52a80 : fetch_word Ubsan.M.loaded_segments (0x52a80 : word) = Some W_52a80.
Proof. vm_refl. Qed.
Lemma D_52a80 : decode_any W_52a80 = Some (Jal 1 56980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a84 : bv 32 := 0x00892503.
Lemma F_52a84 : fetch_word Ubsan.M.loaded_segments (0x52a84 : word) = Some W_52a84.
Proof. vm_refl. Qed.
Lemma D_52a84 : decode_any W_52a84 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a88 : bv 32 := 0xfff5061b.
Lemma F_52a88 : fetch_word Ubsan.M.loaded_segments (0x52a88 : word) = Some W_52a88.
Proof. vm_refl. Qed.
Lemma D_52a88 : decode_any W_52a88 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8c : bv 32 := 0x00c92423.
Lemma F_52a8c : fetch_word Ubsan.M.loaded_segments (0x52a8c : word) = Some W_52a8c.
Proof. vm_refl. Qed.
Lemma D_52a8c : decode_any W_52a8c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a90 : bv 32 := 0xfca044e3.
Lemma F_52a90 : fetch_word Ubsan.M.loaded_segments (0x52a90 : word) = Some W_52a90.
Proof. vm_refl. Qed.
Lemma D_52a90 : decode_any W_52a90 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a94 : bv 32 := 0x01093503.
Lemma F_52a94 : fetch_word Ubsan.M.loaded_segments (0x52a94 : word) = Some W_52a94.
Proof. vm_refl. Qed.
Lemma D_52a94 : decode_any W_52a94 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a98 : bv 32 := 0xfa1ff06f.
Lemma F_52a98 : fetch_word Ubsan.M.loaded_segments (0x52a98 : word) = Some W_52a98.
Proof. vm_refl. Qed.
Lemma D_52a98 : decode_any W_52a98 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9c : bv 32 := 0x00100513.
Lemma F_52a9c : fetch_word Ubsan.M.loaded_segments (0x52a9c : word) = Some W_52a9c.
Proof. vm_refl. Qed.
Lemma D_52a9c : decode_any W_52a9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa0 : bv 32 := 0x00a90023.
Lemma F_52aa0 : fetch_word Ubsan.M.loaded_segments (0x52aa0 : word) = Some W_52aa0.
Proof. vm_refl. Qed.
Lemma D_52aa0 : decode_any W_52aa0 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa4 : bv 32 := 0x00040513.
Lemma F_52aa4 : fetch_word Ubsan.M.loaded_segments (0x52aa4 : word) = Some W_52aa4.
Proof. vm_refl. Qed.
Lemma D_52aa4 : decode_any W_52aa4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa8 : bv 32 := 0x02813083.
Lemma F_52aa8 : fetch_word Ubsan.M.loaded_segments (0x52aa8 : word) = Some W_52aa8.
Proof. vm_refl. Qed.
Lemma D_52aa8 : decode_any W_52aa8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aac : bv 32 := 0x02013403.
Lemma F_52aac : fetch_word Ubsan.M.loaded_segments (0x52aac : word) = Some W_52aac.
Proof. vm_refl. Qed.
Lemma D_52aac : decode_any W_52aac = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab0 : bv 32 := 0x01813483.
Lemma F_52ab0 : fetch_word Ubsan.M.loaded_segments (0x52ab0 : word) = Some W_52ab0.
Proof. vm_refl. Qed.
Lemma D_52ab0 : decode_any W_52ab0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab4 : bv 32 := 0x01013903.
Lemma F_52ab4 : fetch_word Ubsan.M.loaded_segments (0x52ab4 : word) = Some W_52ab4.
Proof. vm_refl. Qed.
Lemma D_52ab4 : decode_any W_52ab4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab8 : bv 32 := 0x00813983.
Lemma F_52ab8 : fetch_word Ubsan.M.loaded_segments (0x52ab8 : word) = Some W_52ab8.
Proof. vm_refl. Qed.
Lemma D_52ab8 : decode_any W_52ab8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52abc : bv 32 := 0x03010113.
Lemma F_52abc : fetch_word Ubsan.M.loaded_segments (0x52abc : word) = Some W_52abc.
Proof. vm_refl. Qed.
Lemma D_52abc : decode_any W_52abc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ac0 : bv 32 := 0x0dc0e06f.
Lemma F_52ac0 : fetch_word Ubsan.M.loaded_segments (0x52ac0 : word) = Some W_52ac0.
Proof. vm_refl. Qed.
Lemma D_52ac0 : decode_any W_52ac0 = Some (Jal 0 57564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ac4 : bv 32 := 0x00008067.
Lemma F_52ac4 : fetch_word Ubsan.M.loaded_segments (0x52ac4 : word) = Some W_52ac4.
Proof. vm_refl. Qed.
Lemma D_52ac4 : decode_any W_52ac4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ac8 : bv 32 := 0xfd010113.
Lemma F_52ac8 : fetch_word Ubsan.M.loaded_segments (0x52ac8 : word) = Some W_52ac8.
Proof. vm_refl. Qed.
Lemma D_52ac8 : decode_any W_52ac8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52acc : bv 32 := 0x02113423.
Lemma F_52acc : fetch_word Ubsan.M.loaded_segments (0x52acc : word) = Some W_52acc.
Proof. vm_refl. Qed.
Lemma D_52acc : decode_any W_52acc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ad0 : bv 32 := 0x02813023.
Lemma F_52ad0 : fetch_word Ubsan.M.loaded_segments (0x52ad0 : word) = Some W_52ad0.
Proof. vm_refl. Qed.
Lemma D_52ad0 : decode_any W_52ad0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ad4 : bv 32 := 0x00913c23.
Lemma F_52ad4 : fetch_word Ubsan.M.loaded_segments (0x52ad4 : word) = Some W_52ad4.
Proof. vm_refl. Qed.
Lemma D_52ad4 : decode_any W_52ad4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ad8 : bv 32 := 0x01213823.
Lemma F_52ad8 : fetch_word Ubsan.M.loaded_segments (0x52ad8 : word) = Some W_52ad8.
Proof. vm_refl. Qed.
Lemma D_52ad8 : decode_any W_52ad8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52adc : bv 32 := 0x01313423.
Lemma F_52adc : fetch_word Ubsan.M.loaded_segments (0x52adc : word) = Some W_52adc.
Proof. vm_refl. Qed.
Lemma D_52adc : decode_any W_52adc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ae0 : bv 32 := 0x00050493.
Lemma F_52ae0 : fetch_word Ubsan.M.loaded_segments (0x52ae0 : word) = Some W_52ae0.
Proof. vm_refl. Qed.
Lemma D_52ae0 : decode_any W_52ae0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ae4 : bv 32 := 0x00045517.
Lemma F_52ae4 : fetch_word Ubsan.M.loaded_segments (0x52ae4 : word) = Some W_52ae4.
Proof. vm_refl. Qed.
Lemma D_52ae4 : decode_any W_52ae4 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ae8 : bv 32 := 0xef450993.
Lemma F_52ae8 : fetch_word Ubsan.M.loaded_segments (0x52ae8 : word) = Some W_52ae8.
Proof. vm_refl. Qed.
Lemma D_52ae8 : decode_any W_52ae8 = Some (OpImm ALU_ADD 19 10 3828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aec : bv 32 := 0x00498413.
Lemma F_52aec : fetch_word Ubsan.M.loaded_segments (0x52aec : word) = Some W_52aec.
Proof. vm_refl. Qed.
Lemma D_52aec : decode_any W_52aec = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52af0 : bv 32 := 0x00040513.
Lemma F_52af0 : fetch_word Ubsan.M.loaded_segments (0x52af0 : word) = Some W_52af0.
Proof. vm_refl. Qed.
Lemma D_52af0 : decode_any W_52af0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52af4 : bv 32 := 0x6210d0ef.
Lemma F_52af4 : fetch_word Ubsan.M.loaded_segments (0x52af4 : word) = Some W_52af4.
Proof. vm_refl. Qed.
Lemma D_52af4 : decode_any W_52af4 = Some (Jal 1 56864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52af8 : bv 32 := 0x0009c503.
Lemma F_52af8 : fetch_word Ubsan.M.loaded_segments (0x52af8 : word) = Some W_52af8.
Proof. vm_refl. Qed.
Lemma D_52af8 : decode_any W_52af8 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52afc : bv 32 := 0xfff00913.
Lemma F_52afc : fetch_word Ubsan.M.loaded_segments (0x52afc : word) = Some W_52afc.
Proof. vm_refl. Qed.
Lemma D_52afc : decode_any W_52afc = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b00 : bv 32 := 0x06051263.
Lemma F_52b00 : fetch_word Ubsan.M.loaded_segments (0x52b00 : word) = Some W_52b00.
Proof. vm_refl. Qed.
Lemma D_52b00 : decode_any W_52b00 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b04 : bv 32 := 0x0109b503.
Lemma F_52b04 : fetch_word Ubsan.M.loaded_segments (0x52b04 : word) = Some W_52b04.
Proof. vm_refl. Qed.
Lemma D_52b04 : decode_any W_52b04 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b08 : bv 32 := 0x00051663.
Lemma F_52b08 : fetch_word Ubsan.M.loaded_segments (0x52b08 : word) = Some W_52b08.
Proof. vm_refl. Qed.
Lemma D_52b08 : decode_any W_52b08 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b0c : bv 32 := 0x01898513.
Lemma F_52b0c : fetch_word Ubsan.M.loaded_segments (0x52b0c : word) = Some W_52b0c.
Proof. vm_refl. Qed.
Lemma D_52b0c : decode_any W_52b0c = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b10 : bv 32 := 0x00a9b823.
Lemma F_52b10 : fetch_word Ubsan.M.loaded_segments (0x52b10 : word) = Some W_52b10.
Proof. vm_refl. Qed.
Lemma D_52b10 : decode_any W_52b10 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b14 : bv 32 := 0x0089a583.
Lemma F_52b14 : fetch_word Ubsan.M.loaded_segments (0x52b14 : word) = Some W_52b14.
Proof. vm_refl. Qed.
Lemma D_52b14 : decode_any W_52b14 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b18 : bv 32 := 0x02000613.
Lemma F_52b18 : fetch_word Ubsan.M.loaded_segments (0x52b18 : word) = Some W_52b18.
Proof. vm_refl. Qed.
Lemma D_52b18 : decode_any W_52b18 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b1c : bv 32 := 0x02c59263.
Lemma F_52b1c : fetch_word Ubsan.M.loaded_segments (0x52b1c : word) = Some W_52b1c.
Proof. vm_refl. Qed.
Lemma D_52b1c : decode_any W_52b1c = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b20 : bv 32 := 0x20800513.
Lemma F_52b20 : fetch_word Ubsan.M.loaded_segments (0x52b20 : word) = Some W_52b20.
Proof. vm_refl. Qed.
Lemma D_52b20 : decode_any W_52b20 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b24 : bv 32 := 0x00100593.
Lemma F_52b24 : fetch_word Ubsan.M.loaded_segments (0x52b24 : word) = Some W_52b24.
Proof. vm_refl. Qed.
Lemma D_52b24 : decode_any W_52b24 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b28 : bv 32 := 0x464000ef.
Lemma F_52b28 : fetch_word Ubsan.M.loaded_segments (0x52b28 : word) = Some W_52b28.
Proof. vm_refl. Qed.
Lemma D_52b28 : decode_any W_52b28 = Some (Jal 1 1124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b2c : bv 32 := 0x02050c63.
Lemma F_52b2c : fetch_word Ubsan.M.loaded_segments (0x52b2c : word) = Some W_52b2c.
Proof. vm_refl. Qed.
Lemma D_52b2c : decode_any W_52b2c = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b30 : bv 32 := 0x00000593.
Lemma F_52b30 : fetch_word Ubsan.M.loaded_segments (0x52b30 : word) = Some W_52b30.
Proof. vm_refl. Qed.
Lemma D_52b30 : decode_any W_52b30 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b34 : bv 32 := 0x0109b603.
Lemma F_52b34 : fetch_word Ubsan.M.loaded_segments (0x52b34 : word) = Some W_52b34.
Proof. vm_refl. Qed.
Lemma D_52b34 : decode_any W_52b34 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b38 : bv 32 := 0x00c53023.
Lemma F_52b38 : fetch_word Ubsan.M.loaded_segments (0x52b38 : word) = Some W_52b38.
Proof. vm_refl. Qed.
Lemma D_52b38 : decode_any W_52b38 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b3c : bv 32 := 0x00a9b823.
Lemma F_52b3c : fetch_word Ubsan.M.loaded_segments (0x52b3c : word) = Some W_52b3c.
Proof. vm_refl. Qed.
Lemma D_52b3c : decode_any W_52b3c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b40 : bv 32 := 0x00000913.
Lemma F_52b40 : fetch_word Ubsan.M.loaded_segments (0x52b40 : word) = Some W_52b40.
Proof. vm_refl. Qed.
Lemma D_52b40 : decode_any W_52b40 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b44 : bv 32 := 0x00359613.
Lemma F_52b44 : fetch_word Ubsan.M.loaded_segments (0x52b44 : word) = Some W_52b44.
Proof. vm_refl. Qed.
Lemma D_52b44 : decode_any W_52b44 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b48 : bv 32 := 0x00c50533.
Lemma F_52b48 : fetch_word Ubsan.M.loaded_segments (0x52b48 : word) = Some W_52b48.
Proof. vm_refl. Qed.
Lemma D_52b48 : decode_any W_52b48 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b4c : bv 32 := 0x00000617.
Lemma F_52b4c : fetch_word Ubsan.M.loaded_segments (0x52b4c : word) = Some W_52b4c.
Proof. vm_refl. Qed.
Lemma D_52b4c : decode_any W_52b4c = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b50 : bv 32 := 0x00158593.
Lemma F_52b50 : fetch_word Ubsan.M.loaded_segments (0x52b50 : word) = Some W_52b50.
Proof. vm_refl. Qed.
Lemma D_52b50 : decode_any W_52b50 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b54 : bv 32 := 0x04060613.
Lemma F_52b54 : fetch_word Ubsan.M.loaded_segments (0x52b54 : word) = Some W_52b54.
Proof. vm_refl. Qed.
Lemma D_52b54 : decode_any W_52b54 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b58 : bv 32 := 0x00c53423.
Lemma F_52b58 : fetch_word Ubsan.M.loaded_segments (0x52b58 : word) = Some W_52b58.
Proof. vm_refl. Qed.
Lemma D_52b58 : decode_any W_52b58 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b5c : bv 32 := 0x10953423.
Lemma F_52b5c : fetch_word Ubsan.M.loaded_segments (0x52b5c : word) = Some W_52b5c.
Proof. vm_refl. Qed.
Lemma D_52b5c : decode_any W_52b5c = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b60 : bv 32 := 0x00b9a423.
Lemma F_52b60 : fetch_word Ubsan.M.loaded_segments (0x52b60 : word) = Some W_52b60.
Proof. vm_refl. Qed.
Lemma D_52b60 : decode_any W_52b60 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b64 : bv 32 := 0x00040513.
Lemma F_52b64 : fetch_word Ubsan.M.loaded_segments (0x52b64 : word) = Some W_52b64.
Proof. vm_refl. Qed.
Lemma D_52b64 : decode_any W_52b64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b68 : bv 32 := 0x0340e0ef.
Lemma F_52b68 : fetch_word Ubsan.M.loaded_segments (0x52b68 : word) = Some W_52b68.
Proof. vm_refl. Qed.
Lemma D_52b68 : decode_any W_52b68 = Some (Jal 1 57396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b6c : bv 32 := 0x00090513.
Lemma F_52b6c : fetch_word Ubsan.M.loaded_segments (0x52b6c : word) = Some W_52b6c.
Proof. vm_refl. Qed.
Lemma D_52b6c : decode_any W_52b6c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b70 : bv 32 := 0x02813083.
Lemma F_52b70 : fetch_word Ubsan.M.loaded_segments (0x52b70 : word) = Some W_52b70.
Proof. vm_refl. Qed.
Lemma D_52b70 : decode_any W_52b70 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b74 : bv 32 := 0x02013403.
Lemma F_52b74 : fetch_word Ubsan.M.loaded_segments (0x52b74 : word) = Some W_52b74.
Proof. vm_refl. Qed.
Lemma D_52b74 : decode_any W_52b74 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b78 : bv 32 := 0x01813483.
Lemma F_52b78 : fetch_word Ubsan.M.loaded_segments (0x52b78 : word) = Some W_52b78.
Proof. vm_refl. Qed.
Lemma D_52b78 : decode_any W_52b78 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b7c : bv 32 := 0x01013903.
Lemma F_52b7c : fetch_word Ubsan.M.loaded_segments (0x52b7c : word) = Some W_52b7c.
Proof. vm_refl. Qed.
Lemma D_52b7c : decode_any W_52b7c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b80 : bv 32 := 0x00813983.
Lemma F_52b80 : fetch_word Ubsan.M.loaded_segments (0x52b80 : word) = Some W_52b80.
Proof. vm_refl. Qed.
Lemma D_52b80 : decode_any W_52b80 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b84 : bv 32 := 0x03010113.
Lemma F_52b84 : fetch_word Ubsan.M.loaded_segments (0x52b84 : word) = Some W_52b84.
Proof. vm_refl. Qed.
Lemma D_52b84 : decode_any W_52b84 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b88 : bv 32 := 0x00008067.
Lemma F_52b88 : fetch_word Ubsan.M.loaded_segments (0x52b88 : word) = Some W_52b88.
Proof. vm_refl. Qed.
Lemma D_52b88 : decode_any W_52b88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b8c : bv 32 := 0x00050067.
Lemma F_52b8c : fetch_word Ubsan.M.loaded_segments (0x52b8c : word) = Some W_52b8c.
Proof. vm_refl. Qed.
Lemma D_52b8c : decode_any W_52b8c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b90 : bv 32 := 0x00008067.
Lemma F_52b90 : fetch_word Ubsan.M.loaded_segments (0x52b90 : word) = Some W_52b90.
Proof. vm_refl. Qed.
Lemma D_52b90 : decode_any W_52b90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b94 : bv 32 := 0xfe010113.
Lemma F_52b94 : fetch_word Ubsan.M.loaded_segments (0x52b94 : word) = Some W_52b94.
Proof. vm_refl. Qed.
Lemma D_52b94 : decode_any W_52b94 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b98 : bv 32 := 0x00113c23.
Lemma F_52b98 : fetch_word Ubsan.M.loaded_segments (0x52b98 : word) = Some W_52b98.
Proof. vm_refl. Qed.
Lemma D_52b98 : decode_any W_52b98 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52b9c : bv 32 := 0x00813823.
Lemma F_52b9c : fetch_word Ubsan.M.loaded_segments (0x52b9c : word) = Some W_52b9c.
Proof. vm_refl. Qed.
Lemma D_52b9c : decode_any W_52b9c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ba0 : bv 32 := 0x00913423.
Lemma F_52ba0 : fetch_word Ubsan.M.loaded_segments (0x52ba0 : word) = Some W_52ba0.
Proof. vm_refl. Qed.
Lemma D_52ba0 : decode_any W_52ba0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ba4 : bv 32 := 0x00013517.
Lemma F_52ba4 : fetch_word Ubsan.M.loaded_segments (0x52ba4 : word) = Some W_52ba4.
Proof. vm_refl. Qed.
Lemma D_52ba4 : decode_any W_52ba4 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ba8 : bv 32 := 0x00013597.
Lemma F_52ba8 : fetch_word Ubsan.M.loaded_segments (0x52ba8 : word) = Some W_52ba8.
Proof. vm_refl. Qed.
Lemma D_52ba8 : decode_any W_52ba8 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bac : bv 32 := 0xfbc53503.
Lemma F_52bac : fetch_word Ubsan.M.loaded_segments (0x52bac : word) = Some W_52bac.
Proof. vm_refl. Qed.
Lemma D_52bac : decode_any W_52bac = Some (Load SZ8 true 10 10 4028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bb0 : bv 32 := 0xfc05b403.
Lemma F_52bb0 : fetch_word Ubsan.M.loaded_segments (0x52bb0 : word) = Some W_52bb0.
Proof. vm_refl. Qed.
Lemma D_52bb0 : decode_any W_52bb0 = Some (Load SZ8 true 8 11 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bb4 : bv 32 := 0x00a47c63.
Lemma F_52bb4 : fetch_word Ubsan.M.loaded_segments (0x52bb4 : word) = Some W_52bb4.
Proof. vm_refl. Qed.
Lemma D_52bb4 : decode_any W_52bb4 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bb8 : bv 32 := 0xff853583.
Lemma F_52bb8 : fetch_word Ubsan.M.loaded_segments (0x52bb8 : word) = Some W_52bb8.
Proof. vm_refl. Qed.
Lemma D_52bb8 : decode_any W_52bb8 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bbc : bv 32 := 0xff850493.
Lemma F_52bbc : fetch_word Ubsan.M.loaded_segments (0x52bbc : word) = Some W_52bbc.
Proof. vm_refl. Qed.
Lemma D_52bbc : decode_any W_52bbc = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bc0 : bv 32 := 0x000580e7.
Lemma F_52bc0 : fetch_word Ubsan.M.loaded_segments (0x52bc0 : word) = Some W_52bc0.
Proof. vm_refl. Qed.
Lemma D_52bc0 : decode_any W_52bc0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bc4 : bv 32 := 0x00048513.
Lemma F_52bc4 : fetch_word Ubsan.M.loaded_segments (0x52bc4 : word) = Some W_52bc4.
Proof. vm_refl. Qed.
Lemma D_52bc4 : decode_any W_52bc4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bc8 : bv 32 := 0xfe9468e3.
Lemma F_52bc8 : fetch_word Ubsan.M.loaded_segments (0x52bc8 : word) = Some W_52bc8.
Proof. vm_refl. Qed.
Lemma D_52bc8 : decode_any W_52bc8 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bcc : bv 32 := 0x01813083.
Lemma F_52bcc : fetch_word Ubsan.M.loaded_segments (0x52bcc : word) = Some W_52bcc.
Proof. vm_refl. Qed.
Lemma D_52bcc : decode_any W_52bcc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bd0 : bv 32 := 0x01013403.
Lemma F_52bd0 : fetch_word Ubsan.M.loaded_segments (0x52bd0 : word) = Some W_52bd0.
Proof. vm_refl. Qed.
Lemma D_52bd0 : decode_any W_52bd0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bd4 : bv 32 := 0x00813483.
Lemma F_52bd4 : fetch_word Ubsan.M.loaded_segments (0x52bd4 : word) = Some W_52bd4.
Proof. vm_refl. Qed.
Lemma D_52bd4 : decode_any W_52bd4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bd8 : bv 32 := 0x02010113.
Lemma F_52bd8 : fetch_word Ubsan.M.loaded_segments (0x52bd8 : word) = Some W_52bd8.
Proof. vm_refl. Qed.
Lemma D_52bd8 : decode_any W_52bd8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bdc : bv 32 := 0xfb5ff06f.
Lemma F_52bdc : fetch_word Ubsan.M.loaded_segments (0x52bdc : word) = Some W_52bdc.
Proof. vm_refl. Qed.
Lemma D_52bdc : decode_any W_52bdc = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52be0 : bv 32 := 0xff010113.
Lemma F_52be0 : fetch_word Ubsan.M.loaded_segments (0x52be0 : word) = Some W_52be0.
Proof. vm_refl. Qed.
Lemma D_52be0 : decode_any W_52be0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52be4 : bv 32 := 0x00113423.
Lemma F_52be4 : fetch_word Ubsan.M.loaded_segments (0x52be4 : word) = Some W_52be4.
Proof. vm_refl. Qed.
Lemma D_52be4 : decode_any W_52be4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52be8 : bv 32 := 0x00813023.
Lemma F_52be8 : fetch_word Ubsan.M.loaded_segments (0x52be8 : word) = Some W_52be8.
Proof. vm_refl. Qed.
Lemma D_52be8 : decode_any W_52be8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bec : bv 32 := 0x00000593.
Lemma F_52bec : fetch_word Ubsan.M.loaded_segments (0x52bec : word) = Some W_52bec.
Proof. vm_refl. Qed.
Lemma D_52bec : decode_any W_52bec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bf0 : bv 32 := 0x00020613.
Lemma F_52bf0 : fetch_word Ubsan.M.loaded_segments (0x52bf0 : word) = Some W_52bf0.
Proof. vm_refl. Qed.
Lemma D_52bf0 : decode_any W_52bf0 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bf4 : bv 32 := 0xf5862603.
Lemma F_52bf4 : fetch_word Ubsan.M.loaded_segments (0x52bf4 : word) = Some W_52bf4.
Proof. vm_refl. Qed.
Lemma D_52bf4 : decode_any W_52bf4 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bf8 : bv 32 := 0x00045697.
Lemma F_52bf8 : fetch_word Ubsan.M.loaded_segments (0x52bf8 : word) = Some W_52bf8.
Proof. vm_refl. Qed.
Lemma D_52bf8 : decode_any W_52bf8 = Some (Auipc 13 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52bfc : bv 32 := 0x00068693.
Lemma F_52bfc : fetch_word Ubsan.M.loaded_segments (0x52bfc : word) = Some W_52bfc.
Proof. vm_refl. Qed.
Lemma D_52bfc : decode_any W_52bfc = Some (OpImm ALU_ADD 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c00 : bv 32 := 0x1606a72f.
Lemma F_52c00 : fetch_word Ubsan.M.loaded_segments (0x52c00 : word) = Some W_52c00.
Proof. vm_refl. Qed.
Lemma D_52c00 : decode_any W_52c00 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c04 : bv 32 := 0x00b71663.
Lemma F_52c04 : fetch_word Ubsan.M.loaded_segments (0x52c04 : word) = Some W_52c04.
Proof. vm_refl. Qed.
Lemma D_52c04 : decode_any W_52c04 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c08 : bv 32 := 0x1ec6a7af.
Lemma F_52c08 : fetch_word Ubsan.M.loaded_segments (0x52c08 : word) = Some W_52c08.
Proof. vm_refl. Qed.
Lemma D_52c08 : decode_any W_52c08 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c0c : bv 32 := 0xfe079ae3.
Lemma F_52c0c : fetch_word Ubsan.M.loaded_segments (0x52c0c : word) = Some W_52c0c.
Proof. vm_refl. Qed.
Lemma D_52c0c : decode_any W_52c0c = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c10 : bv 32 := 0x0007059b.
Lemma F_52c10 : fetch_word Ubsan.M.loaded_segments (0x52c10 : word) = Some W_52c10.
Proof. vm_refl. Qed.
Lemma D_52c10 : decode_any W_52c10 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c14 : bv 32 := 0x02c58263.
Lemma F_52c14 : fetch_word Ubsan.M.loaded_segments (0x52c14 : word) = Some W_52c14.
Proof. vm_refl. Qed.
Lemma D_52c14 : decode_any W_52c14 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c18 : bv 32 := 0x02058263.
Lemma F_52c18 : fetch_word Ubsan.M.loaded_segments (0x52c18 : word) = Some W_52c18.
Proof. vm_refl. Qed.
Lemma D_52c18 : decode_any W_52c18 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c1c : bv 32 := 0x04900893.
Lemma F_52c1c : fetch_word Ubsan.M.loaded_segments (0x52c1c : word) = Some W_52c1c.
Proof. vm_refl. Qed.
Lemma D_52c1c : decode_any W_52c1c = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c20 : bv 32 := 0x00000593.
Lemma F_52c20 : fetch_word Ubsan.M.loaded_segments (0x52c20 : word) = Some W_52c20.
Proof. vm_refl. Qed.
Lemma D_52c20 : decode_any W_52c20 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c24 : bv 32 := 0x00000613.
Lemma F_52c24 : fetch_word Ubsan.M.loaded_segments (0x52c24 : word) = Some W_52c24.
Proof. vm_refl. Qed.
Lemma D_52c24 : decode_any W_52c24 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c28 : bv 32 := 0x00000693.
Lemma F_52c28 : fetch_word Ubsan.M.loaded_segments (0x52c28 : word) = Some W_52c28.
Proof. vm_refl. Qed.
Lemma D_52c28 : decode_any W_52c28 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c2c : bv 32 := 0x00000513.
Lemma F_52c2c : fetch_word Ubsan.M.loaded_segments (0x52c2c : word) = Some W_52c2c.
Proof. vm_refl. Qed.
Lemma D_52c2c : decode_any W_52c2c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c30 : bv 32 := 0x00000073.
Lemma F_52c30 : fetch_word Ubsan.M.loaded_segments (0x52c30 : word) = Some W_52c30.
Proof. vm_refl. Qed.
Lemma D_52c30 : decode_any W_52c30 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52c30 : is_ecall W_52c30 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52c34 : bv 32 := 0xff9ff06f.
Lemma F_52c34 : fetch_word Ubsan.M.loaded_segments (0x52c34 : word) = Some W_52c34.
Proof. vm_refl. Qed.
Lemma D_52c34 : decode_any W_52c34 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c38 : bv 32 := 0x00000023.
Lemma F_52c38 : fetch_word Ubsan.M.loaded_segments (0x52c38 : word) = Some W_52c38.
Proof. vm_refl. Qed.
Lemma D_52c38 : decode_any W_52c38 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c3c : bv 32 := 0x00050413.
Lemma F_52c3c : fetch_word Ubsan.M.loaded_segments (0x52c3c : word) = Some W_52c3c.
Proof. vm_refl. Qed.
Lemma D_52c3c : decode_any W_52c3c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c40 : bv 32 := 0xdbdff0ef.
Lemma F_52c40 : fetch_word Ubsan.M.loaded_segments (0x52c40 : word) = Some W_52c40.
Proof. vm_refl. Qed.
Lemma D_52c40 : decode_any W_52c40 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c44 : bv 32 := 0xf51ff0ef.
Lemma F_52c44 : fetch_word Ubsan.M.loaded_segments (0x52c44 : word) = Some W_52c44.
Proof. vm_refl. Qed.
Lemma D_52c44 : decode_any W_52c44 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c48 : bv 32 := 0x561020ef.
Lemma F_52c48 : fetch_word Ubsan.M.loaded_segments (0x52c48 : word) = Some W_52c48.
Proof. vm_refl. Qed.
Lemma D_52c48 : decode_any W_52c48 = Some (Jal 1 11616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c4c : bv 32 := 0x00040513.
Lemma F_52c4c : fetch_word Ubsan.M.loaded_segments (0x52c4c : word) = Some W_52c4c.
Proof. vm_refl. Qed.
Lemma D_52c4c : decode_any W_52c4c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c50 : bv 32 := 0xd61ff0ef.
Lemma F_52c50 : fetch_word Ubsan.M.loaded_segments (0x52c50 : word) = Some W_52c50.
Proof. vm_refl. Qed.
Lemma D_52c50 : decode_any W_52c50 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c54 : bv 32 := 0xfa010113.
Lemma F_52c54 : fetch_word Ubsan.M.loaded_segments (0x52c54 : word) = Some W_52c54.
Proof. vm_refl. Qed.
Lemma D_52c54 : decode_any W_52c54 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c58 : bv 32 := 0x02113423.
Lemma F_52c58 : fetch_word Ubsan.M.loaded_segments (0x52c58 : word) = Some W_52c58.
Proof. vm_refl. Qed.
Lemma D_52c58 : decode_any W_52c58 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c5c : bv 32 := 0x02813023.
Lemma F_52c5c : fetch_word Ubsan.M.loaded_segments (0x52c5c : word) = Some W_52c5c.
Proof. vm_refl. Qed.
Lemma D_52c5c : decode_any W_52c5c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c60 : bv 32 := 0x00913c23.
Lemma F_52c60 : fetch_word Ubsan.M.loaded_segments (0x52c60 : word) = Some W_52c60.
Proof. vm_refl. Qed.
Lemma D_52c60 : decode_any W_52c60 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c64 : bv 32 := 0x00058413.
Lemma F_52c64 : fetch_word Ubsan.M.loaded_segments (0x52c64 : word) = Some W_52c64.
Proof. vm_refl. Qed.
Lemma D_52c64 : decode_any W_52c64 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c68 : bv 32 := 0x00050293.
Lemma F_52c68 : fetch_word Ubsan.M.loaded_segments (0x52c68 : word) = Some W_52c68.
Proof. vm_refl. Qed.
Lemma D_52c68 : decode_any W_52c68 = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c6c : bv 32 := 0x05013823.
Lemma F_52c6c : fetch_word Ubsan.M.loaded_segments (0x52c6c : word) = Some W_52c6c.
Proof. vm_refl. Qed.
Lemma D_52c6c : decode_any W_52c6c = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c70 : bv 32 := 0x05113c23.
Lemma F_52c70 : fetch_word Ubsan.M.loaded_segments (0x52c70 : word) = Some W_52c70.
Proof. vm_refl. Qed.
Lemma D_52c70 : decode_any W_52c70 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c74 : bv 32 := 0x00013517.
Lemma F_52c74 : fetch_word Ubsan.M.loaded_segments (0x52c74 : word) = Some W_52c74.
Proof. vm_refl. Qed.
Lemma D_52c74 : decode_any W_52c74 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c78 : bv 32 := 0xee453483.
Lemma F_52c78 : fetch_word Ubsan.M.loaded_segments (0x52c78 : word) = Some W_52c78.
Proof. vm_refl. Qed.
Lemma D_52c78 : decode_any W_52c78 = Some (Load SZ8 true 9 10 3812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c7c : bv 32 := 0x02c13823.
Lemma F_52c7c : fetch_word Ubsan.M.loaded_segments (0x52c7c : word) = Some W_52c7c.
Proof. vm_refl. Qed.
Lemma D_52c7c : decode_any W_52c7c = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c80 : bv 32 := 0x02d13c23.
Lemma F_52c80 : fetch_word Ubsan.M.loaded_segments (0x52c80 : word) = Some W_52c80.
Proof. vm_refl. Qed.
Lemma D_52c80 : decode_any W_52c80 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c84 : bv 32 := 0x04e13023.
Lemma F_52c84 : fetch_word Ubsan.M.loaded_segments (0x52c84 : word) = Some W_52c84.
Proof. vm_refl. Qed.
Lemma D_52c84 : decode_any W_52c84 = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c88 : bv 32 := 0x04f13423.
Lemma F_52c88 : fetch_word Ubsan.M.loaded_segments (0x52c88 : word) = Some W_52c88.
Proof. vm_refl. Qed.
Lemma D_52c88 : decode_any W_52c88 = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c8c : bv 32 := 0x0004b503.
Lemma F_52c8c : fetch_word Ubsan.M.loaded_segments (0x52c8c : word) = Some W_52c8c.
Proof. vm_refl. Qed.
Lemma D_52c8c : decode_any W_52c8c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c90 : bv 32 := 0x0405f593.
Lemma F_52c90 : fetch_word Ubsan.M.loaded_segments (0x52c90 : word) = Some W_52c90.
Proof. vm_refl. Qed.
Lemma D_52c90 : decode_any W_52c90 = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c94 : bv 32 := 0x00a13823.
Lemma F_52c94 : fetch_word Ubsan.M.loaded_segments (0x52c94 : word) = Some W_52c94.
Proof. vm_refl. Qed.
Lemma D_52c94 : decode_any W_52c94 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c98 : bv 32 := 0x00059c63.
Lemma F_52c98 : fetch_word Ubsan.M.loaded_segments (0x52c98 : word) = Some W_52c98.
Proof. vm_refl. Qed.
Lemma D_52c98 : decode_any W_52c98 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52c9c : bv 32 := 0x00410537.
Lemma F_52c9c : fetch_word Ubsan.M.loaded_segments (0x52c9c : word) = Some W_52c9c.
Proof. vm_refl. Qed.
Lemma D_52c9c : decode_any W_52c9c = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ca0 : bv 32 := 0x00a475b3.
Lemma F_52ca0 : fetch_word Ubsan.M.loaded_segments (0x52ca0 : word) = Some W_52ca0.
Proof. vm_refl. Qed.
Lemma D_52ca0 : decode_any W_52ca0 = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ca4 : bv 32 := 0x00a58663.
Lemma F_52ca4 : fetch_word Ubsan.M.loaded_segments (0x52ca4 : word) = Some W_52ca4.
Proof. vm_refl. Qed.
Lemma D_52ca4 : decode_any W_52ca4 = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ca8 : bv 32 := 0x00000713.
Lemma F_52ca8 : fetch_word Ubsan.M.loaded_segments (0x52ca8 : word) = Some W_52ca8.
Proof. vm_refl. Qed.
Lemma D_52ca8 : decode_any W_52ca8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cac : bv 32 := 0x0080006f.
Lemma F_52cac : fetch_word Ubsan.M.loaded_segments (0x52cac : word) = Some W_52cac.
Proof. vm_refl. Qed.
Lemma D_52cac : decode_any W_52cac = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cb0 : bv 32 := 0x03016703.
Lemma F_52cb0 : fetch_word Ubsan.M.loaded_segments (0x52cb0 : word) = Some W_52cb0.
Proof. vm_refl. Qed.
Lemma D_52cb0 : decode_any W_52cb0 = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cb4 : bv 32 := 0x000086b7.
Lemma F_52cb4 : fetch_word Ubsan.M.loaded_segments (0x52cb4 : word) = Some W_52cb4.
Proof. vm_refl. Qed.
Lemma D_52cb4 : decode_any W_52cb4 = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cb8 : bv 32 := 0x00d466b3.
Lemma F_52cb8 : fetch_word Ubsan.M.loaded_segments (0x52cb8 : word) = Some W_52cb8.
Proof. vm_refl. Qed.
Lemma D_52cb8 : decode_any W_52cb8 = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cbc : bv 32 := 0x03800513.
Lemma F_52cbc : fetch_word Ubsan.M.loaded_segments (0x52cbc : word) = Some W_52cbc.
Proof. vm_refl. Qed.
Lemma D_52cbc : decode_any W_52cbc = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cc0 : bv 32 := 0xf9c00593.
Lemma F_52cc0 : fetch_word Ubsan.M.loaded_segments (0x52cc0 : word) = Some W_52cc0.
Proof. vm_refl. Qed.
Lemma D_52cc0 : decode_any W_52cc0 = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cc4 : bv 32 := 0x00028613.
Lemma F_52cc4 : fetch_word Ubsan.M.loaded_segments (0x52cc4 : word) = Some W_52cc4.
Proof. vm_refl. Qed.
Lemma D_52cc4 : decode_any W_52cc4 = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cc8 : bv 32 := 0x00000793.
Lemma F_52cc8 : fetch_word Ubsan.M.loaded_segments (0x52cc8 : word) = Some W_52cc8.
Proof. vm_refl. Qed.
Lemma D_52cc8 : decode_any W_52cc8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ccc : bv 32 := 0x00000813.
Lemma F_52ccc : fetch_word Ubsan.M.loaded_segments (0x52ccc : word) = Some W_52ccc.
Proof. vm_refl. Qed.
Lemma D_52ccc : decode_any W_52ccc = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cd0 : bv 32 := 0x7650d0ef.
Lemma F_52cd0 : fetch_word Ubsan.M.loaded_segments (0x52cd0 : word) = Some W_52cd0.
Proof. vm_refl. Qed.
Lemma D_52cd0 : decode_any W_52cd0 = Some (Jal 1 57188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cd4 : bv 32 := 0x02c41413.
Lemma F_52cd4 : fetch_word Ubsan.M.loaded_segments (0x52cd4 : word) = Some W_52cd4.
Proof. vm_refl. Qed.
Lemma D_52cd4 : decode_any W_52cd4 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cd8 : bv 32 := 0x00050693.
Lemma F_52cd8 : fetch_word Ubsan.M.loaded_segments (0x52cd8 : word) = Some W_52cd8.
Proof. vm_refl. Qed.
Lemma D_52cd8 : decode_any W_52cd8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cdc : bv 32 := 0x02045663.
Lemma F_52cdc : fetch_word Ubsan.M.loaded_segments (0x52cdc : word) = Some W_52cdc.
Proof. vm_refl. Qed.
Lemma D_52cdc : decode_any W_52cdc = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ce0 : bv 32 := 0x80000537.
Lemma F_52ce0 : fetch_word Ubsan.M.loaded_segments (0x52ce0 : word) = Some W_52ce0.
Proof. vm_refl. Qed.
Lemma D_52ce0 : decode_any W_52ce0 = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ce4 : bv 32 := 0xfff5051b.
Lemma F_52ce4 : fetch_word Ubsan.M.loaded_segments (0x52ce4 : word) = Some W_52ce4.
Proof. vm_refl. Qed.
Lemma D_52ce4 : decode_any W_52ce4 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ce8 : bv 32 := 0x00150593.
Lemma F_52ce8 : fetch_word Ubsan.M.loaded_segments (0x52ce8 : word) = Some W_52ce8.
Proof. vm_refl. Qed.
Lemma D_52ce8 : decode_any W_52ce8 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cec : bv 32 := 0x00b6f5b3.
Lemma F_52cec : fetch_word Ubsan.M.loaded_segments (0x52cec : word) = Some W_52cec.
Proof. vm_refl. Qed.
Lemma D_52cec : decode_any W_52cec = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cf0 : bv 32 := 0x00059c63.
Lemma F_52cf0 : fetch_word Ubsan.M.loaded_segments (0x52cf0 : word) = Some W_52cf0.
Proof. vm_refl. Qed.
Lemma D_52cf0 : decode_any W_52cf0 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cf4 : bv 32 := 0x00a6f533.
Lemma F_52cf4 : fetch_word Ubsan.M.loaded_segments (0x52cf4 : word) = Some W_52cf4.
Proof. vm_refl. Qed.
Lemma D_52cf4 : decode_any W_52cf4 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cf8 : bv 32 := 0x01900893.
Lemma F_52cf8 : fetch_word Ubsan.M.loaded_segments (0x52cf8 : word) = Some W_52cf8.
Proof. vm_refl. Qed.
Lemma D_52cf8 : decode_any W_52cf8 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52cfc : bv 32 := 0x00200593.
Lemma F_52cfc : fetch_word Ubsan.M.loaded_segments (0x52cfc : word) = Some W_52cfc.
Proof. vm_refl. Qed.
Lemma D_52cfc : decode_any W_52cfc = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d00 : bv 32 := 0x00100613.
Lemma F_52d00 : fetch_word Ubsan.M.loaded_segments (0x52d00 : word) = Some W_52d00.
Proof. vm_refl. Qed.
Lemma D_52d00 : decode_any W_52d00 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d04 : bv 32 := 0x00000073.
Lemma F_52d04 : fetch_word Ubsan.M.loaded_segments (0x52d04 : word) = Some W_52d04.
Proof. vm_refl. Qed.
Lemma D_52d04 : decode_any W_52d04 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52d04 : is_ecall W_52d04 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52d08 : bv 32 := 0x0006851b.
Lemma F_52d08 : fetch_word Ubsan.M.loaded_segments (0x52d08 : word) = Some W_52d08.
Proof. vm_refl. Qed.
Lemma D_52d08 : decode_any W_52d08 = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d0c : bv 32 := 0x094000ef.
Lemma F_52d0c : fetch_word Ubsan.M.loaded_segments (0x52d0c : word) = Some W_52d0c.
Proof. vm_refl. Qed.
Lemma D_52d0c : decode_any W_52d0c = Some (Jal 1 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d10 : bv 32 := 0x0004b583.
Lemma F_52d10 : fetch_word Ubsan.M.loaded_segments (0x52d10 : word) = Some W_52d10.
Proof. vm_refl. Qed.
Lemma D_52d10 : decode_any W_52d10 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d14 : bv 32 := 0x01013603.
Lemma F_52d14 : fetch_word Ubsan.M.loaded_segments (0x52d14 : word) = Some W_52d14.
Proof. vm_refl. Qed.
Lemma D_52d14 : decode_any W_52d14 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d18 : bv 32 := 0x00c59e63.
Lemma F_52d18 : fetch_word Ubsan.M.loaded_segments (0x52d18 : word) = Some W_52d18.
Proof. vm_refl. Qed.
Lemma D_52d18 : decode_any W_52d18 = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d1c : bv 32 := 0x0005051b.
Lemma F_52d1c : fetch_word Ubsan.M.loaded_segments (0x52d1c : word) = Some W_52d1c.
Proof. vm_refl. Qed.
Lemma D_52d1c : decode_any W_52d1c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d20 : bv 32 := 0x02813083.
Lemma F_52d20 : fetch_word Ubsan.M.loaded_segments (0x52d20 : word) = Some W_52d20.
Proof. vm_refl. Qed.
Lemma D_52d20 : decode_any W_52d20 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d24 : bv 32 := 0x02013403.
Lemma F_52d24 : fetch_word Ubsan.M.loaded_segments (0x52d24 : word) = Some W_52d24.
Proof. vm_refl. Qed.
Lemma D_52d24 : decode_any W_52d24 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d28 : bv 32 := 0x01813483.
Lemma F_52d28 : fetch_word Ubsan.M.loaded_segments (0x52d28 : word) = Some W_52d28.
Proof. vm_refl. Qed.
Lemma D_52d28 : decode_any W_52d28 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d2c : bv 32 := 0x06010113.
Lemma F_52d2c : fetch_word Ubsan.M.loaded_segments (0x52d2c : word) = Some W_52d2c.
Proof. vm_refl. Qed.
Lemma D_52d2c : decode_any W_52d2c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d30 : bv 32 := 0x00008067.
Lemma F_52d30 : fetch_word Ubsan.M.loaded_segments (0x52d30 : word) = Some W_52d30.
Proof. vm_refl. Qed.
Lemma D_52d30 : decode_any W_52d30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d34 : bv 32 := 0x064000ef.
Lemma F_52d34 : fetch_word Ubsan.M.loaded_segments (0x52d34 : word) = Some W_52d34.
Proof. vm_refl. Qed.
Lemma D_52d34 : decode_any W_52d34 = Some (Jal 1 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d38 : bv 32 := 0xff010113.
Lemma F_52d38 : fetch_word Ubsan.M.loaded_segments (0x52d38 : word) = Some W_52d38.
Proof. vm_refl. Qed.
Lemma D_52d38 : decode_any W_52d38 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d3c : bv 32 := 0x00113423.
Lemma F_52d3c : fetch_word Ubsan.M.loaded_segments (0x52d3c : word) = Some W_52d3c.
Proof. vm_refl. Qed.
Lemma D_52d3c : decode_any W_52d3c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d40 : bv 32 := 0x00050e63.
Lemma F_52d40 : fetch_word Ubsan.M.loaded_segments (0x52d40 : word) = Some W_52d40.
Proof. vm_refl. Qed.
Lemma D_52d40 : decode_any W_52d40 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d44 : bv 32 := 0x00050593.
Lemma F_52d44 : fetch_word Ubsan.M.loaded_segments (0x52d44 : word) = Some W_52d44.
Proof. vm_refl. Qed.
Lemma D_52d44 : decode_any W_52d44 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d48 : bv 32 := 0x00013517.
Lemma F_52d48 : fetch_word Ubsan.M.loaded_segments (0x52d48 : word) = Some W_52d48.
Proof. vm_refl. Qed.
Lemma D_52d48 : decode_any W_52d48 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d4c : bv 32 := 0xe1053503.
Lemma F_52d4c : fetch_word Ubsan.M.loaded_segments (0x52d4c : word) = Some W_52d4c.
Proof. vm_refl. Qed.
Lemma D_52d4c : decode_any W_52d4c = Some (Load SZ8 true 10 10 3600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d50 : bv 32 := 0x00800613.
Lemma F_52d50 : fetch_word Ubsan.M.loaded_segments (0x52d50 : word) = Some W_52d50.
Proof. vm_refl. Qed.
Lemma D_52d50 : decode_any W_52d50 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d54 : bv 32 := 0x3540d0ef.
Lemma F_52d54 : fetch_word Ubsan.M.loaded_segments (0x52d54 : word) = Some W_52d54.
Proof. vm_refl. Qed.
Lemma D_52d54 : decode_any W_52d54 = Some (Jal 1 54100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d58 : bv 32 := 0x01c0006f.
Lemma F_52d58 : fetch_word Ubsan.M.loaded_segments (0x52d58 : word) = Some W_52d58.
Proof. vm_refl. Qed.
Lemma D_52d58 : decode_any W_52d58 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d5c : bv 32 := 0x00013517.
Lemma F_52d5c : fetch_word Ubsan.M.loaded_segments (0x52d5c : word) = Some W_52d5c.
Proof. vm_refl. Qed.
Lemma D_52d5c : decode_any W_52d5c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d60 : bv 32 := 0xdfc53503.
Lemma F_52d60 : fetch_word Ubsan.M.loaded_segments (0x52d60 : word) = Some W_52d60.
Proof. vm_refl. Qed.
Lemma D_52d60 : decode_any W_52d60 = Some (Load SZ8 true 10 10 3580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d64 : bv 32 := 0x41c655b7.
Lemma F_52d64 : fetch_word Ubsan.M.loaded_segments (0x52d64 : word) = Some W_52d64.
Proof. vm_refl. Qed.
Lemma D_52d64 : decode_any W_52d64 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d68 : bv 32 := 0xe6d5859b.
Lemma F_52d68 : fetch_word Ubsan.M.loaded_segments (0x52d68 : word) = Some W_52d68.
Proof. vm_refl. Qed.
Lemma D_52d68 : decode_any W_52d68 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d6c : bv 32 := 0x02b505b3.
Lemma F_52d6c : fetch_word Ubsan.M.loaded_segments (0x52d6c : word) = Some W_52d6c.
Proof. vm_refl. Qed.
Lemma D_52d6c : decode_any W_52d6c = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d70 : bv 32 := 0x00b53023.
Lemma F_52d70 : fetch_word Ubsan.M.loaded_segments (0x52d70 : word) = Some W_52d70.
Proof. vm_refl. Qed.
Lemma D_52d70 : decode_any W_52d70 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d74 : bv 32 := 0x00013517.
Lemma F_52d74 : fetch_word Ubsan.M.loaded_segments (0x52d74 : word) = Some W_52d74.
Proof. vm_refl. Qed.
Lemma D_52d74 : decode_any W_52d74 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d78 : bv 32 := 0xde453503.
Lemma F_52d78 : fetch_word Ubsan.M.loaded_segments (0x52d78 : word) = Some W_52d78.
Proof. vm_refl. Qed.
Lemma D_52d78 : decode_any W_52d78 = Some (Load SZ8 true 10 10 3556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d7c : bv 32 := 0x000500a3.
Lemma F_52d7c : fetch_word Ubsan.M.loaded_segments (0x52d7c : word) = Some W_52d7c.
Proof. vm_refl. Qed.
Lemma D_52d7c : decode_any W_52d7c = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d80 : bv 32 := 0x00053503.
Lemma F_52d80 : fetch_word Ubsan.M.loaded_segments (0x52d80 : word) = Some W_52d80.
Proof. vm_refl. Qed.
Lemma D_52d80 : decode_any W_52d80 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d84 : bv 32 := 0x00020593.
Lemma F_52d84 : fetch_word Ubsan.M.loaded_segments (0x52d84 : word) = Some W_52d84.
Proof. vm_refl. Qed.
Lemma D_52d84 : decode_any W_52d84 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d88 : bv 32 := 0xfea5b823.
Lemma F_52d88 : fetch_word Ubsan.M.loaded_segments (0x52d88 : word) = Some W_52d88.
Proof. vm_refl. Qed.
Lemma D_52d88 : decode_any W_52d88 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d8c : bv 32 := 0x00813083.
Lemma F_52d8c : fetch_word Ubsan.M.loaded_segments (0x52d8c : word) = Some W_52d8c.
Proof. vm_refl. Qed.
Lemma D_52d8c : decode_any W_52d8c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d90 : bv 32 := 0x01010113.
Lemma F_52d90 : fetch_word Ubsan.M.loaded_segments (0x52d90 : word) = Some W_52d90.
Proof. vm_refl. Qed.
Lemma D_52d90 : decode_any W_52d90 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d94 : bv 32 := 0x00008067.
Lemma F_52d94 : fetch_word Ubsan.M.loaded_segments (0x52d94 : word) = Some W_52d94.
Proof. vm_refl. Qed.
Lemma D_52d94 : decode_any W_52d94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d98 : bv 32 := 0x00000023.
Lemma F_52d98 : fetch_word Ubsan.M.loaded_segments (0x52d98 : word) = Some W_52d98.
Proof. vm_refl. Qed.
Lemma D_52d98 : decode_any W_52d98 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52d9c : bv 32 := 0x00008067.
Lemma F_52d9c : fetch_word Ubsan.M.loaded_segments (0x52d9c : word) = Some W_52d9c.
Proof. vm_refl. Qed.
Lemma D_52d9c : decode_any W_52d9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52da0 : bv 32 := 0xfffff5b7.
Lemma F_52da0 : fetch_word Ubsan.M.loaded_segments (0x52da0 : word) = Some W_52da0.
Proof. vm_refl. Qed.
Lemma D_52da0 : decode_any W_52da0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52da4 : bv 32 := 0x0015859b.
Lemma F_52da4 : fetch_word Ubsan.M.loaded_segments (0x52da4 : word) = Some W_52da4.
Proof. vm_refl. Qed.
Lemma D_52da4 : decode_any W_52da4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52da8 : bv 32 := 0x02b56663.
Lemma F_52da8 : fetch_word Ubsan.M.loaded_segments (0x52da8 : word) = Some W_52da8.
Proof. vm_refl. Qed.
Lemma D_52da8 : decode_any W_52da8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dac : bv 32 := 0xff010113.
Lemma F_52dac : fetch_word Ubsan.M.loaded_segments (0x52dac : word) = Some W_52dac.
Proof. vm_refl. Qed.
Lemma D_52dac : decode_any W_52dac = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52db0 : bv 32 := 0x00113423.
Lemma F_52db0 : fetch_word Ubsan.M.loaded_segments (0x52db0 : word) = Some W_52db0.
Proof. vm_refl. Qed.
Lemma D_52db0 : decode_any W_52db0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52db4 : bv 32 := 0x00813023.
Lemma F_52db4 : fetch_word Ubsan.M.loaded_segments (0x52db4 : word) = Some W_52db4.
Proof. vm_refl. Qed.
Lemma D_52db4 : decode_any W_52db4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52db8 : bv 32 := 0x40a0043b.
Lemma F_52db8 : fetch_word Ubsan.M.loaded_segments (0x52db8 : word) = Some W_52db8.
Proof. vm_refl. Qed.
Lemma D_52db8 : decode_any W_52db8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dbc : bv 32 := 0xb55ff0ef.
Lemma F_52dbc : fetch_word Ubsan.M.loaded_segments (0x52dbc : word) = Some W_52dbc.
Proof. vm_refl. Qed.
Lemma D_52dbc : decode_any W_52dbc = Some (Jal 1 2095956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dc0 : bv 32 := 0x00852023.
Lemma F_52dc0 : fetch_word Ubsan.M.loaded_segments (0x52dc0 : word) = Some W_52dc0.
Proof. vm_refl. Qed.
Lemma D_52dc0 : decode_any W_52dc0 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dc4 : bv 32 := 0xfff00513.
Lemma F_52dc4 : fetch_word Ubsan.M.loaded_segments (0x52dc4 : word) = Some W_52dc4.
Proof. vm_refl. Qed.
Lemma D_52dc4 : decode_any W_52dc4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dc8 : bv 32 := 0x00813083.
Lemma F_52dc8 : fetch_word Ubsan.M.loaded_segments (0x52dc8 : word) = Some W_52dc8.
Proof. vm_refl. Qed.
Lemma D_52dc8 : decode_any W_52dc8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dcc : bv 32 := 0x00013403.
Lemma F_52dcc : fetch_word Ubsan.M.loaded_segments (0x52dcc : word) = Some W_52dcc.
Proof. vm_refl. Qed.
Lemma D_52dcc : decode_any W_52dcc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dd0 : bv 32 := 0x01010113.
Lemma F_52dd0 : fetch_word Ubsan.M.loaded_segments (0x52dd0 : word) = Some W_52dd0.
Proof. vm_refl. Qed.
Lemma D_52dd0 : decode_any W_52dd0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52dd4 : bv 32 := 0x00008067.
Lemma F_52dd4 : fetch_word Ubsan.M.loaded_segments (0x52dd4 : word) = Some W_52dd4.
Proof. vm_refl. Qed.
Lemma D_52dd4 : decode_any W_52dd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
