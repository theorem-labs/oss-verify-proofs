(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_9d058 : bv 32 := 0x0035f693.
Lemma F_9d058 : fetch_word Asan.M.loaded_segments (0x9dcdc : word) = Some W_9d058.
Proof. vm_refl. Qed.
Lemma D_9d058 : decode_any W_9d058 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d05c : bv 32 := 0x10068863.
Lemma F_9d05c : fetch_word Asan.M.loaded_segments (0x9dce0 : word) = Some W_9d05c.
Proof. vm_refl. Qed.
Lemma D_9d05c : decode_any W_9d05c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d060 : bv 32 := 0x02060e63.
Lemma F_9d060 : fetch_word Asan.M.loaded_segments (0x9dce4 : word) = Some W_9d060.
Proof. vm_refl. Qed.
Lemma D_9d060 : decode_any W_9d060 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d064 : bv 32 := 0x00158713.
Lemma F_9d064 : fetch_word Asan.M.loaded_segments (0x9dce8 : word) = Some W_9d064.
Proof. vm_refl. Qed.
Lemma D_9d064 : decode_any W_9d064 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d068 : bv 32 := 0x00100793.
Lemma F_9d068 : fetch_word Asan.M.loaded_segments (0x9dcec : word) = Some W_9d068.
Proof. vm_refl. Qed.
Lemma D_9d068 : decode_any W_9d068 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d06c : bv 32 := 0x00050693.
Lemma F_9d06c : fetch_word Asan.M.loaded_segments (0x9dcf0 : word) = Some W_9d06c.
Proof. vm_refl. Qed.
Lemma D_9d06c : decode_any W_9d06c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d070 : bv 32 := 0x0005c883.
Lemma F_9d070 : fetch_word Asan.M.loaded_segments (0x9dcf4 : word) = Some W_9d070.
Proof. vm_refl. Qed.
Lemma D_9d070 : decode_any W_9d070 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d074 : bv 32 := 0x00060813.
Lemma F_9d074 : fetch_word Asan.M.loaded_segments (0x9dcf8 : word) = Some W_9d074.
Proof. vm_refl. Qed.
Lemma D_9d074 : decode_any W_9d074 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d078 : bv 32 := 0x00158593.
Lemma F_9d078 : fetch_word Asan.M.loaded_segments (0x9dcfc : word) = Some W_9d078.
Proof. vm_refl. Qed.
Lemma D_9d078 : decode_any W_9d078 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d07c : bv 32 := 0x00377293.
Lemma F_9d07c : fetch_word Asan.M.loaded_segments (0x9dd00 : word) = Some W_9d07c.
Proof. vm_refl. Qed.
Lemma D_9d07c : decode_any W_9d07c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d080 : bv 32 := 0x01168023.
Lemma F_9d080 : fetch_word Asan.M.loaded_segments (0x9dd04 : word) = Some W_9d080.
Proof. vm_refl. Qed.
Lemma D_9d080 : decode_any W_9d080 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d084 : bv 32 := 0x00168693.
Lemma F_9d084 : fetch_word Asan.M.loaded_segments (0x9dd08 : word) = Some W_9d084.
Proof. vm_refl. Qed.
Lemma D_9d084 : decode_any W_9d084 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d088 : bv 32 := 0xfff60613.
Lemma F_9d088 : fetch_word Asan.M.loaded_segments (0x9dd0c : word) = Some W_9d088.
Proof. vm_refl. Qed.
Lemma D_9d088 : decode_any W_9d088 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d08c : bv 32 := 0x00028a63.
Lemma F_9d08c : fetch_word Asan.M.loaded_segments (0x9dd10 : word) = Some W_9d08c.
Proof. vm_refl. Qed.
Lemma D_9d08c : decode_any W_9d08c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d090 : bv 32 := 0x00170713.
Lemma F_9d090 : fetch_word Asan.M.loaded_segments (0x9dd14 : word) = Some W_9d090.
Proof. vm_refl. Qed.
Lemma D_9d090 : decode_any W_9d090 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d094 : bv 32 := 0xfcf81ee3.
Lemma F_9d094 : fetch_word Asan.M.loaded_segments (0x9dd18 : word) = Some W_9d094.
Proof. vm_refl. Qed.
Lemma D_9d094 : decode_any W_9d094 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d098 : bv 32 := 0x0080006f.
Lemma F_9d098 : fetch_word Asan.M.loaded_segments (0x9dd1c : word) = Some W_9d098.
Proof. vm_refl. Qed.
Lemma D_9d098 : decode_any W_9d098 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d09c : bv 32 := 0x00050693.
Lemma F_9d09c : fetch_word Asan.M.loaded_segments (0x9dd20 : word) = Some W_9d09c.
Proof. vm_refl. Qed.
Lemma D_9d09c : decode_any W_9d09c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0a0 : bv 32 := 0x0036f793.
Lemma F_9d0a0 : fetch_word Asan.M.loaded_segments (0x9dd24 : word) = Some W_9d0a0.
Proof. vm_refl. Qed.
Lemma D_9d0a0 : decode_any W_9d0a0 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0a4 : bv 32 := 0x0c078a63.
Lemma F_9d0a4 : fetch_word Asan.M.loaded_segments (0x9dd28 : word) = Some W_9d0a4.
Proof. vm_refl. Qed.
Lemma D_9d0a4 : decode_any W_9d0a4 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0a8 : bv 32 := 0x02000713.
Lemma F_9d0a8 : fetch_word Asan.M.loaded_segments (0x9dd2c : word) = Some W_9d0a8.
Proof. vm_refl. Qed.
Lemma D_9d0a8 : decode_any W_9d0a8 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0ac : bv 32 := 0x02e67063.
Lemma F_9d0ac : fetch_word Asan.M.loaded_segments (0x9dd30 : word) = Some W_9d0ac.
Proof. vm_refl. Qed.
Lemma D_9d0ac : decode_any W_9d0ac = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0b0 : bv 32 := 0x01000713.
Lemma F_9d0b0 : fetch_word Asan.M.loaded_segments (0x9dd34 : word) = Some W_9d0b0.
Proof. vm_refl. Qed.
Lemma D_9d0b0 : decode_any W_9d0b0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0b4 : bv 32 := 0x24e67863.
Lemma F_9d0b4 : fetch_word Asan.M.loaded_segments (0x9dd38 : word) = Some W_9d0b4.
Proof. vm_refl. Qed.
Lemma D_9d0b4 : decode_any W_9d0b4 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0b8 : bv 32 := 0x00867713.
Lemma F_9d0b8 : fetch_word Asan.M.loaded_segments (0x9dd3c : word) = Some W_9d0b8.
Proof. vm_refl. Qed.
Lemma D_9d0b8 : decode_any W_9d0b8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0bc : bv 32 := 0x2c071e63.
Lemma F_9d0bc : fetch_word Asan.M.loaded_segments (0x9dd40 : word) = Some W_9d0bc.
Proof. vm_refl. Qed.
Lemma D_9d0bc : decode_any W_9d0bc = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0c0 : bv 32 := 0x00467713.
Lemma F_9d0c0 : fetch_word Asan.M.loaded_segments (0x9dd44 : word) = Some W_9d0c0.
Proof. vm_refl. Qed.
Lemma D_9d0c0 : decode_any W_9d0c0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0c4 : bv 32 := 0x32071463.
Lemma F_9d0c4 : fetch_word Asan.M.loaded_segments (0x9dd48 : word) = Some W_9d0c4.
Proof. vm_refl. Qed.
Lemma D_9d0c4 : decode_any W_9d0c4 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0c8 : bv 32 := 0x3500006f.
Lemma F_9d0c8 : fetch_word Asan.M.loaded_segments (0x9dd4c : word) = Some W_9d0c8.
Proof. vm_refl. Qed.
Lemma D_9d0c8 : decode_any W_9d0c8 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0cc : bv 32 := 0x0005a703.
Lemma F_9d0cc : fetch_word Asan.M.loaded_segments (0x9dd50 : word) = Some W_9d0cc.
Proof. vm_refl. Qed.
Lemma D_9d0cc : decode_any W_9d0cc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0d0 : bv 32 := 0x00300813.
Lemma F_9d0d0 : fetch_word Asan.M.loaded_segments (0x9dd54 : word) = Some W_9d0d0.
Proof. vm_refl. Qed.
Lemma D_9d0d0 : decode_any W_9d0d0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0d4 : bv 32 := 0x11078e63.
Lemma F_9d0d4 : fetch_word Asan.M.loaded_segments (0x9dd58 : word) = Some W_9d0d4.
Proof. vm_refl. Qed.
Lemma D_9d0d4 : decode_any W_9d0d4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0d8 : bv 32 := 0x00200813.
Lemma F_9d0d8 : fetch_word Asan.M.loaded_segments (0x9dd5c : word) = Some W_9d0d8.
Proof. vm_refl. Qed.
Lemma D_9d0d8 : decode_any W_9d0d8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0dc : bv 32 := 0x19079c63.
Lemma F_9d0dc : fetch_word Asan.M.loaded_segments (0x9dd60 : word) = Some W_9d0dc.
Proof. vm_refl. Qed.
Lemma D_9d0dc : decode_any W_9d0dc = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0e0 : bv 32 := 0x00875793.
Lemma F_9d0e0 : fetch_word Asan.M.loaded_segments (0x9dd64 : word) = Some W_9d0e0.
Proof. vm_refl. Qed.
Lemma D_9d0e0 : decode_any W_9d0e0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0e4 : bv 32 := 0xffe60613.
Lemma F_9d0e4 : fetch_word Asan.M.loaded_segments (0x9dd68 : word) = Some W_9d0e4.
Proof. vm_refl. Qed.
Lemma D_9d0e4 : decode_any W_9d0e4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0e8 : bv 32 := 0x00e68023.
Lemma F_9d0e8 : fetch_word Asan.M.loaded_segments (0x9dd6c : word) = Some W_9d0e8.
Proof. vm_refl. Qed.
Lemma D_9d0e8 : decode_any W_9d0e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0ec : bv 32 := 0x00f680a3.
Lemma F_9d0ec : fetch_word Asan.M.loaded_segments (0x9dd70 : word) = Some W_9d0ec.
Proof. vm_refl. Qed.
Lemma D_9d0ec : decode_any W_9d0ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0f0 : bv 32 := 0x00268693.
Lemma F_9d0f0 : fetch_word Asan.M.loaded_segments (0x9dd74 : word) = Some W_9d0f0.
Proof. vm_refl. Qed.
Lemma D_9d0f0 : decode_any W_9d0f0 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0f4 : bv 32 := 0x01058593.
Lemma F_9d0f4 : fetch_word Asan.M.loaded_segments (0x9dd78 : word) = Some W_9d0f4.
Proof. vm_refl. Qed.
Lemma D_9d0f4 : decode_any W_9d0f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0f8 : bv 32 := 0x01100793.
Lemma F_9d0f8 : fetch_word Asan.M.loaded_segments (0x9dd7c : word) = Some W_9d0f8.
Proof. vm_refl. Qed.
Lemma D_9d0f8 : decode_any W_9d0f8 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d0fc : bv 32 := 0x0107581b.
Lemma F_9d0fc : fetch_word Asan.M.loaded_segments (0x9dd80 : word) = Some W_9d0fc.
Proof. vm_refl. Qed.
Lemma D_9d0fc : decode_any W_9d0fc = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d100 : bv 32 := 0xff45a883.
Lemma F_9d100 : fetch_word Asan.M.loaded_segments (0x9dd84 : word) = Some W_9d100.
Proof. vm_refl. Qed.
Lemma D_9d100 : decode_any W_9d100 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d104 : bv 32 := 0xff85a283.
Lemma F_9d104 : fetch_word Asan.M.loaded_segments (0x9dd88 : word) = Some W_9d104.
Proof. vm_refl. Qed.
Lemma D_9d104 : decode_any W_9d104 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d108 : bv 32 := 0xffc5a303.
Lemma F_9d108 : fetch_word Asan.M.loaded_segments (0x9dd8c : word) = Some W_9d108.
Proof. vm_refl. Qed.
Lemma D_9d108 : decode_any W_9d108 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d10c : bv 32 := 0x0005a703.
Lemma F_9d10c : fetch_word Asan.M.loaded_segments (0x9dd90 : word) = Some W_9d10c.
Proof. vm_refl. Qed.
Lemma D_9d10c : decode_any W_9d10c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d110 : bv 32 := 0x01089393.
Lemma F_9d110 : fetch_word Asan.M.loaded_segments (0x9dd94 : word) = Some W_9d110.
Proof. vm_refl. Qed.
Lemma D_9d110 : decode_any W_9d110 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d114 : bv 32 := 0x0108d89b.
Lemma F_9d114 : fetch_word Asan.M.loaded_segments (0x9dd98 : word) = Some W_9d114.
Proof. vm_refl. Qed.
Lemma D_9d114 : decode_any W_9d114 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d118 : bv 32 := 0x0103e833.
Lemma F_9d118 : fetch_word Asan.M.loaded_segments (0x9dd9c : word) = Some W_9d118.
Proof. vm_refl. Qed.
Lemma D_9d118 : decode_any W_9d118 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d11c : bv 32 := 0x01029393.
Lemma F_9d11c : fetch_word Asan.M.loaded_segments (0x9dda0 : word) = Some W_9d11c.
Proof. vm_refl. Qed.
Lemma D_9d11c : decode_any W_9d11c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d120 : bv 32 := 0x0102d29b.
Lemma F_9d120 : fetch_word Asan.M.loaded_segments (0x9dda4 : word) = Some W_9d120.
Proof. vm_refl. Qed.
Lemma D_9d120 : decode_any W_9d120 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d124 : bv 32 := 0x0113e8b3.
Lemma F_9d124 : fetch_word Asan.M.loaded_segments (0x9dda8 : word) = Some W_9d124.
Proof. vm_refl. Qed.
Lemma D_9d124 : decode_any W_9d124 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d128 : bv 32 := 0x01031393.
Lemma F_9d128 : fetch_word Asan.M.loaded_segments (0x9ddac : word) = Some W_9d128.
Proof. vm_refl. Qed.
Lemma D_9d128 : decode_any W_9d128 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d12c : bv 32 := 0x0103531b.
Lemma F_9d12c : fetch_word Asan.M.loaded_segments (0x9ddb0 : word) = Some W_9d12c.
Proof. vm_refl. Qed.
Lemma D_9d12c : decode_any W_9d12c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d130 : bv 32 := 0x0053e2b3.
Lemma F_9d130 : fetch_word Asan.M.loaded_segments (0x9ddb4 : word) = Some W_9d130.
Proof. vm_refl. Qed.
Lemma D_9d130 : decode_any W_9d130 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d134 : bv 32 := 0x01071393.
Lemma F_9d134 : fetch_word Asan.M.loaded_segments (0x9ddb8 : word) = Some W_9d134.
Proof. vm_refl. Qed.
Lemma D_9d134 : decode_any W_9d134 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d138 : bv 32 := 0x0063e333.
Lemma F_9d138 : fetch_word Asan.M.loaded_segments (0x9ddbc : word) = Some W_9d138.
Proof. vm_refl. Qed.
Lemma D_9d138 : decode_any W_9d138 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d13c : bv 32 := 0xff060613.
Lemma F_9d13c : fetch_word Asan.M.loaded_segments (0x9ddc0 : word) = Some W_9d13c.
Proof. vm_refl. Qed.
Lemma D_9d13c : decode_any W_9d13c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d140 : bv 32 := 0x0106a023.
Lemma F_9d140 : fetch_word Asan.M.loaded_segments (0x9ddc4 : word) = Some W_9d140.
Proof. vm_refl. Qed.
Lemma D_9d140 : decode_any W_9d140 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d144 : bv 32 := 0x0116a223.
Lemma F_9d144 : fetch_word Asan.M.loaded_segments (0x9ddc8 : word) = Some W_9d144.
Proof. vm_refl. Qed.
Lemma D_9d144 : decode_any W_9d144 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d148 : bv 32 := 0x0056a423.
Lemma F_9d148 : fetch_word Asan.M.loaded_segments (0x9ddcc : word) = Some W_9d148.
Proof. vm_refl. Qed.
Lemma D_9d148 : decode_any W_9d148 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d14c : bv 32 := 0x0066a623.
Lemma F_9d14c : fetch_word Asan.M.loaded_segments (0x9ddd0 : word) = Some W_9d14c.
Proof. vm_refl. Qed.
Lemma D_9d14c : decode_any W_9d14c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d150 : bv 32 := 0x01068693.
Lemma F_9d150 : fetch_word Asan.M.loaded_segments (0x9ddd4 : word) = Some W_9d150.
Proof. vm_refl. Qed.
Lemma D_9d150 : decode_any W_9d150 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d154 : bv 32 := 0x01058593.
Lemma F_9d154 : fetch_word Asan.M.loaded_segments (0x9ddd8 : word) = Some W_9d154.
Proof. vm_refl. Qed.
Lemma D_9d154 : decode_any W_9d154 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d158 : bv 32 := 0xfac7e2e3.
Lemma F_9d158 : fetch_word Asan.M.loaded_segments (0x9dddc : word) = Some W_9d158.
Proof. vm_refl. Qed.
Lemma D_9d158 : decode_any W_9d158 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d15c : bv 32 := 0xff258593.
Lemma F_9d15c : fetch_word Asan.M.loaded_segments (0x9dde0 : word) = Some W_9d15c.
Proof. vm_refl. Qed.
Lemma D_9d15c : decode_any W_9d15c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d160 : bv 32 := 0x01000713.
Lemma F_9d160 : fetch_word Asan.M.loaded_segments (0x9dde4 : word) = Some W_9d160.
Proof. vm_refl. Qed.
Lemma D_9d160 : decode_any W_9d160 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d164 : bv 32 := 0xf4e66ae3.
Lemma F_9d164 : fetch_word Asan.M.loaded_segments (0x9dde8 : word) = Some W_9d164.
Proof. vm_refl. Qed.
Lemma D_9d164 : decode_any W_9d164 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d168 : bv 32 := 0x19c0006f.
Lemma F_9d168 : fetch_word Asan.M.loaded_segments (0x9ddec : word) = Some W_9d168.
Proof. vm_refl. Qed.
Lemma D_9d168 : decode_any W_9d168 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d16c : bv 32 := 0x00050693.
Lemma F_9d16c : fetch_word Asan.M.loaded_segments (0x9ddf0 : word) = Some W_9d16c.
Proof. vm_refl. Qed.
Lemma D_9d16c : decode_any W_9d16c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d170 : bv 32 := 0x00357793.
Lemma F_9d170 : fetch_word Asan.M.loaded_segments (0x9ddf4 : word) = Some W_9d170.
Proof. vm_refl. Qed.
Lemma D_9d170 : decode_any W_9d170 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d174 : bv 32 := 0xf2079ae3.
Lemma F_9d174 : fetch_word Asan.M.loaded_segments (0x9ddf8 : word) = Some W_9d174.
Proof. vm_refl. Qed.
Lemma D_9d174 : decode_any W_9d174 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d178 : bv 32 := 0x01000713.
Lemma F_9d178 : fetch_word Asan.M.loaded_segments (0x9ddfc : word) = Some W_9d178.
Proof. vm_refl. Qed.
Lemma D_9d178 : decode_any W_9d178 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d17c : bv 32 := 0x02e66c63.
Lemma F_9d17c : fetch_word Asan.M.loaded_segments (0x9de00 : word) = Some W_9d17c.
Proof. vm_refl. Qed.
Lemma D_9d17c : decode_any W_9d17c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d180 : bv 32 := 0x00f00713.
Lemma F_9d180 : fetch_word Asan.M.loaded_segments (0x9de04 : word) = Some W_9d180.
Proof. vm_refl. Qed.
Lemma D_9d180 : decode_any W_9d180 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d184 : bv 32 := 0x0005a783.
Lemma F_9d184 : fetch_word Asan.M.loaded_segments (0x9de08 : word) = Some W_9d184.
Proof. vm_refl. Qed.
Lemma D_9d184 : decode_any W_9d184 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d188 : bv 32 := 0x0045a803.
Lemma F_9d188 : fetch_word Asan.M.loaded_segments (0x9de0c : word) = Some W_9d188.
Proof. vm_refl. Qed.
Lemma D_9d188 : decode_any W_9d188 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d18c : bv 32 := 0x0085a883.
Lemma F_9d18c : fetch_word Asan.M.loaded_segments (0x9de10 : word) = Some W_9d18c.
Proof. vm_refl. Qed.
Lemma D_9d18c : decode_any W_9d18c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d190 : bv 32 := 0x00c5a283.
Lemma F_9d190 : fetch_word Asan.M.loaded_segments (0x9de14 : word) = Some W_9d190.
Proof. vm_refl. Qed.
Lemma D_9d190 : decode_any W_9d190 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d194 : bv 32 := 0x01058593.
Lemma F_9d194 : fetch_word Asan.M.loaded_segments (0x9de18 : word) = Some W_9d194.
Proof. vm_refl. Qed.
Lemma D_9d194 : decode_any W_9d194 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d198 : bv 32 := 0xff060613.
Lemma F_9d198 : fetch_word Asan.M.loaded_segments (0x9de1c : word) = Some W_9d198.
Proof. vm_refl. Qed.
Lemma D_9d198 : decode_any W_9d198 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d19c : bv 32 := 0x00f6a023.
Lemma F_9d19c : fetch_word Asan.M.loaded_segments (0x9de20 : word) = Some W_9d19c.
Proof. vm_refl. Qed.
Lemma D_9d19c : decode_any W_9d19c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1a0 : bv 32 := 0x0106a223.
Lemma F_9d1a0 : fetch_word Asan.M.loaded_segments (0x9de24 : word) = Some W_9d1a0.
Proof. vm_refl. Qed.
Lemma D_9d1a0 : decode_any W_9d1a0 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1a4 : bv 32 := 0x0116a423.
Lemma F_9d1a4 : fetch_word Asan.M.loaded_segments (0x9de28 : word) = Some W_9d1a4.
Proof. vm_refl. Qed.
Lemma D_9d1a4 : decode_any W_9d1a4 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1a8 : bv 32 := 0x0056a623.
Lemma F_9d1a8 : fetch_word Asan.M.loaded_segments (0x9de2c : word) = Some W_9d1a8.
Proof. vm_refl. Qed.
Lemma D_9d1a8 : decode_any W_9d1a8 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1ac : bv 32 := 0x01068693.
Lemma F_9d1ac : fetch_word Asan.M.loaded_segments (0x9de30 : word) = Some W_9d1ac.
Proof. vm_refl. Qed.
Lemma D_9d1ac : decode_any W_9d1ac = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1b0 : bv 32 := 0xfcc76ae3.
Lemma F_9d1b0 : fetch_word Asan.M.loaded_segments (0x9de34 : word) = Some W_9d1b0.
Proof. vm_refl. Qed.
Lemma D_9d1b0 : decode_any W_9d1b0 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1b4 : bv 32 := 0x00800713.
Lemma F_9d1b4 : fetch_word Asan.M.loaded_segments (0x9de38 : word) = Some W_9d1b4.
Proof. vm_refl. Qed.
Lemma D_9d1b4 : decode_any W_9d1b4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1b8 : bv 32 := 0x00e66e63.
Lemma F_9d1b8 : fetch_word Asan.M.loaded_segments (0x9de3c : word) = Some W_9d1b8.
Proof. vm_refl. Qed.
Lemma D_9d1b8 : decode_any W_9d1b8 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1bc : bv 32 := 0x0005a703.
Lemma F_9d1bc : fetch_word Asan.M.loaded_segments (0x9de40 : word) = Some W_9d1bc.
Proof. vm_refl. Qed.
Lemma D_9d1bc : decode_any W_9d1bc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1c0 : bv 32 := 0x0045a783.
Lemma F_9d1c0 : fetch_word Asan.M.loaded_segments (0x9de44 : word) = Some W_9d1c0.
Proof. vm_refl. Qed.
Lemma D_9d1c0 : decode_any W_9d1c0 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1c4 : bv 32 := 0x00e6a023.
Lemma F_9d1c4 : fetch_word Asan.M.loaded_segments (0x9de48 : word) = Some W_9d1c4.
Proof. vm_refl. Qed.
Lemma D_9d1c4 : decode_any W_9d1c4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1c8 : bv 32 := 0x00f6a223.
Lemma F_9d1c8 : fetch_word Asan.M.loaded_segments (0x9de4c : word) = Some W_9d1c8.
Proof. vm_refl. Qed.
Lemma D_9d1c8 : decode_any W_9d1c8 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1cc : bv 32 := 0x00868693.
Lemma F_9d1cc : fetch_word Asan.M.loaded_segments (0x9de50 : word) = Some W_9d1cc.
Proof. vm_refl. Qed.
Lemma D_9d1cc : decode_any W_9d1cc = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1d0 : bv 32 := 0x00858593.
Lemma F_9d1d0 : fetch_word Asan.M.loaded_segments (0x9de54 : word) = Some W_9d1d0.
Proof. vm_refl. Qed.
Lemma D_9d1d0 : decode_any W_9d1d0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1d4 : bv 32 := 0x00467713.
Lemma F_9d1d4 : fetch_word Asan.M.loaded_segments (0x9de58 : word) = Some W_9d1d4.
Proof. vm_refl. Qed.
Lemma D_9d1d4 : decode_any W_9d1d4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1d8 : bv 32 := 0x24070063.
Lemma F_9d1d8 : fetch_word Asan.M.loaded_segments (0x9de5c : word) = Some W_9d1d8.
Proof. vm_refl. Qed.
Lemma D_9d1d8 : decode_any W_9d1d8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1dc : bv 32 := 0x0005a703.
Lemma F_9d1dc : fetch_word Asan.M.loaded_segments (0x9de60 : word) = Some W_9d1dc.
Proof. vm_refl. Qed.
Lemma D_9d1dc : decode_any W_9d1dc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1e0 : bv 32 := 0x00458593.
Lemma F_9d1e0 : fetch_word Asan.M.loaded_segments (0x9de64 : word) = Some W_9d1e0.
Proof. vm_refl. Qed.
Lemma D_9d1e0 : decode_any W_9d1e0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1e4 : bv 32 := 0x00e6a023.
Lemma F_9d1e4 : fetch_word Asan.M.loaded_segments (0x9de68 : word) = Some W_9d1e4.
Proof. vm_refl. Qed.
Lemma D_9d1e4 : decode_any W_9d1e4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1e8 : bv 32 := 0x00468693.
Lemma F_9d1e8 : fetch_word Asan.M.loaded_segments (0x9de6c : word) = Some W_9d1e8.
Proof. vm_refl. Qed.
Lemma D_9d1e8 : decode_any W_9d1e8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1ec : bv 32 := 0x22c0006f.
Lemma F_9d1ec : fetch_word Asan.M.loaded_segments (0x9de70 : word) = Some W_9d1ec.
Proof. vm_refl. Qed.
Lemma D_9d1ec : decode_any W_9d1ec = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1f0 : bv 32 := 0x00e68023.
Lemma F_9d1f0 : fetch_word Asan.M.loaded_segments (0x9de74 : word) = Some W_9d1f0.
Proof. vm_refl. Qed.
Lemma D_9d1f0 : decode_any W_9d1f0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1f4 : bv 32 := 0x00168693.
Lemma F_9d1f4 : fetch_word Asan.M.loaded_segments (0x9de78 : word) = Some W_9d1f4.
Proof. vm_refl. Qed.
Lemma D_9d1f4 : decode_any W_9d1f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1f8 : bv 32 := 0xfff60613.
Lemma F_9d1f8 : fetch_word Asan.M.loaded_segments (0x9de7c : word) = Some W_9d1f8.
Proof. vm_refl. Qed.
Lemma D_9d1f8 : decode_any W_9d1f8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d1fc : bv 32 := 0x01058593.
Lemma F_9d1fc : fetch_word Asan.M.loaded_segments (0x9de80 : word) = Some W_9d1fc.
Proof. vm_refl. Qed.
Lemma D_9d1fc : decode_any W_9d1fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d200 : bv 32 := 0x01200793.
Lemma F_9d200 : fetch_word Asan.M.loaded_segments (0x9de84 : word) = Some W_9d200.
Proof. vm_refl. Qed.
Lemma D_9d200 : decode_any W_9d200 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d204 : bv 32 := 0x0087581b.
Lemma F_9d204 : fetch_word Asan.M.loaded_segments (0x9de88 : word) = Some W_9d204.
Proof. vm_refl. Qed.
Lemma D_9d204 : decode_any W_9d204 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d208 : bv 32 := 0xff45a883.
Lemma F_9d208 : fetch_word Asan.M.loaded_segments (0x9de8c : word) = Some W_9d208.
Proof. vm_refl. Qed.
Lemma D_9d208 : decode_any W_9d208 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d20c : bv 32 := 0xff85a283.
Lemma F_9d20c : fetch_word Asan.M.loaded_segments (0x9de90 : word) = Some W_9d20c.
Proof. vm_refl. Qed.
Lemma D_9d20c : decode_any W_9d20c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d210 : bv 32 := 0xffc5a303.
Lemma F_9d210 : fetch_word Asan.M.loaded_segments (0x9de94 : word) = Some W_9d210.
Proof. vm_refl. Qed.
Lemma D_9d210 : decode_any W_9d210 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d214 : bv 32 := 0x0005a703.
Lemma F_9d214 : fetch_word Asan.M.loaded_segments (0x9de98 : word) = Some W_9d214.
Proof. vm_refl. Qed.
Lemma D_9d214 : decode_any W_9d214 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d218 : bv 32 := 0x01889393.
Lemma F_9d218 : fetch_word Asan.M.loaded_segments (0x9de9c : word) = Some W_9d218.
Proof. vm_refl. Qed.
Lemma D_9d218 : decode_any W_9d218 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d21c : bv 32 := 0x0088d89b.
Lemma F_9d21c : fetch_word Asan.M.loaded_segments (0x9dea0 : word) = Some W_9d21c.
Proof. vm_refl. Qed.
Lemma D_9d21c : decode_any W_9d21c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d220 : bv 32 := 0x0103e833.
Lemma F_9d220 : fetch_word Asan.M.loaded_segments (0x9dea4 : word) = Some W_9d220.
Proof. vm_refl. Qed.
Lemma D_9d220 : decode_any W_9d220 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d224 : bv 32 := 0x01829393.
Lemma F_9d224 : fetch_word Asan.M.loaded_segments (0x9dea8 : word) = Some W_9d224.
Proof. vm_refl. Qed.
Lemma D_9d224 : decode_any W_9d224 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d228 : bv 32 := 0x0082d29b.
Lemma F_9d228 : fetch_word Asan.M.loaded_segments (0x9deac : word) = Some W_9d228.
Proof. vm_refl. Qed.
Lemma D_9d228 : decode_any W_9d228 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d22c : bv 32 := 0x0113e8b3.
Lemma F_9d22c : fetch_word Asan.M.loaded_segments (0x9deb0 : word) = Some W_9d22c.
Proof. vm_refl. Qed.
Lemma D_9d22c : decode_any W_9d22c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d230 : bv 32 := 0x01831393.
Lemma F_9d230 : fetch_word Asan.M.loaded_segments (0x9deb4 : word) = Some W_9d230.
Proof. vm_refl. Qed.
Lemma D_9d230 : decode_any W_9d230 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d234 : bv 32 := 0x0083531b.
Lemma F_9d234 : fetch_word Asan.M.loaded_segments (0x9deb8 : word) = Some W_9d234.
Proof. vm_refl. Qed.
Lemma D_9d234 : decode_any W_9d234 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d238 : bv 32 := 0x0053e2b3.
Lemma F_9d238 : fetch_word Asan.M.loaded_segments (0x9debc : word) = Some W_9d238.
Proof. vm_refl. Qed.
Lemma D_9d238 : decode_any W_9d238 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d23c : bv 32 := 0x01871393.
Lemma F_9d23c : fetch_word Asan.M.loaded_segments (0x9dec0 : word) = Some W_9d23c.
Proof. vm_refl. Qed.
Lemma D_9d23c : decode_any W_9d23c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d240 : bv 32 := 0x0063e333.
Lemma F_9d240 : fetch_word Asan.M.loaded_segments (0x9dec4 : word) = Some W_9d240.
Proof. vm_refl. Qed.
Lemma D_9d240 : decode_any W_9d240 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d244 : bv 32 := 0xff060613.
Lemma F_9d244 : fetch_word Asan.M.loaded_segments (0x9dec8 : word) = Some W_9d244.
Proof. vm_refl. Qed.
Lemma D_9d244 : decode_any W_9d244 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d248 : bv 32 := 0x0106a023.
Lemma F_9d248 : fetch_word Asan.M.loaded_segments (0x9decc : word) = Some W_9d248.
Proof. vm_refl. Qed.
Lemma D_9d248 : decode_any W_9d248 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d24c : bv 32 := 0x0116a223.
Lemma F_9d24c : fetch_word Asan.M.loaded_segments (0x9ded0 : word) = Some W_9d24c.
Proof. vm_refl. Qed.
Lemma D_9d24c : decode_any W_9d24c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d250 : bv 32 := 0x0056a423.
Lemma F_9d250 : fetch_word Asan.M.loaded_segments (0x9ded4 : word) = Some W_9d250.
Proof. vm_refl. Qed.
Lemma D_9d250 : decode_any W_9d250 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d254 : bv 32 := 0x0066a623.
Lemma F_9d254 : fetch_word Asan.M.loaded_segments (0x9ded8 : word) = Some W_9d254.
Proof. vm_refl. Qed.
Lemma D_9d254 : decode_any W_9d254 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d258 : bv 32 := 0x01068693.
Lemma F_9d258 : fetch_word Asan.M.loaded_segments (0x9dedc : word) = Some W_9d258.
Proof. vm_refl. Qed.
Lemma D_9d258 : decode_any W_9d258 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d25c : bv 32 := 0x01058593.
Lemma F_9d25c : fetch_word Asan.M.loaded_segments (0x9dee0 : word) = Some W_9d25c.
Proof. vm_refl. Qed.
Lemma D_9d25c : decode_any W_9d25c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d260 : bv 32 := 0xfac7e2e3.
Lemma F_9d260 : fetch_word Asan.M.loaded_segments (0x9dee4 : word) = Some W_9d260.
Proof. vm_refl. Qed.
Lemma D_9d260 : decode_any W_9d260 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d264 : bv 32 := 0xff158593.
Lemma F_9d264 : fetch_word Asan.M.loaded_segments (0x9dee8 : word) = Some W_9d264.
Proof. vm_refl. Qed.
Lemma D_9d264 : decode_any W_9d264 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d268 : bv 32 := 0x01000713.
Lemma F_9d268 : fetch_word Asan.M.loaded_segments (0x9deec : word) = Some W_9d268.
Proof. vm_refl. Qed.
Lemma D_9d268 : decode_any W_9d268 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d26c : bv 32 := 0xe4e666e3.
Lemma F_9d26c : fetch_word Asan.M.loaded_segments (0x9def0 : word) = Some W_9d26c.
Proof. vm_refl. Qed.
Lemma D_9d26c : decode_any W_9d26c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d270 : bv 32 := 0x0940006f.
Lemma F_9d270 : fetch_word Asan.M.loaded_segments (0x9def4 : word) = Some W_9d270.
Proof. vm_refl. Qed.
Lemma D_9d270 : decode_any W_9d270 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d274 : bv 32 := 0x00875793.
Lemma F_9d274 : fetch_word Asan.M.loaded_segments (0x9def8 : word) = Some W_9d274.
Proof. vm_refl. Qed.
Lemma D_9d274 : decode_any W_9d274 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d278 : bv 32 := 0x01075813.
Lemma F_9d278 : fetch_word Asan.M.loaded_segments (0x9defc : word) = Some W_9d278.
Proof. vm_refl. Qed.
Lemma D_9d278 : decode_any W_9d278 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d27c : bv 32 := 0xffd60613.
Lemma F_9d27c : fetch_word Asan.M.loaded_segments (0x9df00 : word) = Some W_9d27c.
Proof. vm_refl. Qed.
Lemma D_9d27c : decode_any W_9d27c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d280 : bv 32 := 0x00e68023.
Lemma F_9d280 : fetch_word Asan.M.loaded_segments (0x9df04 : word) = Some W_9d280.
Proof. vm_refl. Qed.
Lemma D_9d280 : decode_any W_9d280 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d284 : bv 32 := 0x00f680a3.
Lemma F_9d284 : fetch_word Asan.M.loaded_segments (0x9df08 : word) = Some W_9d284.
Proof. vm_refl. Qed.
Lemma D_9d284 : decode_any W_9d284 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d288 : bv 32 := 0x01068123.
Lemma F_9d288 : fetch_word Asan.M.loaded_segments (0x9df0c : word) = Some W_9d288.
Proof. vm_refl. Qed.
Lemma D_9d288 : decode_any W_9d288 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d28c : bv 32 := 0x00368693.
Lemma F_9d28c : fetch_word Asan.M.loaded_segments (0x9df10 : word) = Some W_9d28c.
Proof. vm_refl. Qed.
Lemma D_9d28c : decode_any W_9d28c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d290 : bv 32 := 0x01058593.
Lemma F_9d290 : fetch_word Asan.M.loaded_segments (0x9df14 : word) = Some W_9d290.
Proof. vm_refl. Qed.
Lemma D_9d290 : decode_any W_9d290 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d294 : bv 32 := 0x01000793.
Lemma F_9d294 : fetch_word Asan.M.loaded_segments (0x9df18 : word) = Some W_9d294.
Proof. vm_refl. Qed.
Lemma D_9d294 : decode_any W_9d294 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d298 : bv 32 := 0x0187581b.
Lemma F_9d298 : fetch_word Asan.M.loaded_segments (0x9df1c : word) = Some W_9d298.
Proof. vm_refl. Qed.
Lemma D_9d298 : decode_any W_9d298 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d29c : bv 32 := 0xff45a883.
Lemma F_9d29c : fetch_word Asan.M.loaded_segments (0x9df20 : word) = Some W_9d29c.
Proof. vm_refl. Qed.
Lemma D_9d29c : decode_any W_9d29c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2a0 : bv 32 := 0xff85a283.
Lemma F_9d2a0 : fetch_word Asan.M.loaded_segments (0x9df24 : word) = Some W_9d2a0.
Proof. vm_refl. Qed.
Lemma D_9d2a0 : decode_any W_9d2a0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2a4 : bv 32 := 0xffc5a303.
Lemma F_9d2a4 : fetch_word Asan.M.loaded_segments (0x9df28 : word) = Some W_9d2a4.
Proof. vm_refl. Qed.
Lemma D_9d2a4 : decode_any W_9d2a4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2a8 : bv 32 := 0x0005a703.
Lemma F_9d2a8 : fetch_word Asan.M.loaded_segments (0x9df2c : word) = Some W_9d2a8.
Proof. vm_refl. Qed.
Lemma D_9d2a8 : decode_any W_9d2a8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2ac : bv 32 := 0x00889393.
Lemma F_9d2ac : fetch_word Asan.M.loaded_segments (0x9df30 : word) = Some W_9d2ac.
Proof. vm_refl. Qed.
Lemma D_9d2ac : decode_any W_9d2ac = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2b0 : bv 32 := 0x0188d89b.
Lemma F_9d2b0 : fetch_word Asan.M.loaded_segments (0x9df34 : word) = Some W_9d2b0.
Proof. vm_refl. Qed.
Lemma D_9d2b0 : decode_any W_9d2b0 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2b4 : bv 32 := 0x0103e833.
Lemma F_9d2b4 : fetch_word Asan.M.loaded_segments (0x9df38 : word) = Some W_9d2b4.
Proof. vm_refl. Qed.
Lemma D_9d2b4 : decode_any W_9d2b4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2b8 : bv 32 := 0x00829393.
Lemma F_9d2b8 : fetch_word Asan.M.loaded_segments (0x9df3c : word) = Some W_9d2b8.
Proof. vm_refl. Qed.
Lemma D_9d2b8 : decode_any W_9d2b8 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2bc : bv 32 := 0x0182d29b.
Lemma F_9d2bc : fetch_word Asan.M.loaded_segments (0x9df40 : word) = Some W_9d2bc.
Proof. vm_refl. Qed.
Lemma D_9d2bc : decode_any W_9d2bc = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2c0 : bv 32 := 0x0113e8b3.
Lemma F_9d2c0 : fetch_word Asan.M.loaded_segments (0x9df44 : word) = Some W_9d2c0.
Proof. vm_refl. Qed.
Lemma D_9d2c0 : decode_any W_9d2c0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2c4 : bv 32 := 0x00831393.
Lemma F_9d2c4 : fetch_word Asan.M.loaded_segments (0x9df48 : word) = Some W_9d2c4.
Proof. vm_refl. Qed.
Lemma D_9d2c4 : decode_any W_9d2c4 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2c8 : bv 32 := 0x0183531b.
Lemma F_9d2c8 : fetch_word Asan.M.loaded_segments (0x9df4c : word) = Some W_9d2c8.
Proof. vm_refl. Qed.
Lemma D_9d2c8 : decode_any W_9d2c8 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2cc : bv 32 := 0x0053e2b3.
Lemma F_9d2cc : fetch_word Asan.M.loaded_segments (0x9df50 : word) = Some W_9d2cc.
Proof. vm_refl. Qed.
Lemma D_9d2cc : decode_any W_9d2cc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2d0 : bv 32 := 0x00871393.
Lemma F_9d2d0 : fetch_word Asan.M.loaded_segments (0x9df54 : word) = Some W_9d2d0.
Proof. vm_refl. Qed.
Lemma D_9d2d0 : decode_any W_9d2d0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2d4 : bv 32 := 0x0063e333.
Lemma F_9d2d4 : fetch_word Asan.M.loaded_segments (0x9df58 : word) = Some W_9d2d4.
Proof. vm_refl. Qed.
Lemma D_9d2d4 : decode_any W_9d2d4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2d8 : bv 32 := 0xff060613.
Lemma F_9d2d8 : fetch_word Asan.M.loaded_segments (0x9df5c : word) = Some W_9d2d8.
Proof. vm_refl. Qed.
Lemma D_9d2d8 : decode_any W_9d2d8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2dc : bv 32 := 0x0106a023.
Lemma F_9d2dc : fetch_word Asan.M.loaded_segments (0x9df60 : word) = Some W_9d2dc.
Proof. vm_refl. Qed.
Lemma D_9d2dc : decode_any W_9d2dc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2e0 : bv 32 := 0x0116a223.
Lemma F_9d2e0 : fetch_word Asan.M.loaded_segments (0x9df64 : word) = Some W_9d2e0.
Proof. vm_refl. Qed.
Lemma D_9d2e0 : decode_any W_9d2e0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2e4 : bv 32 := 0x0056a423.
Lemma F_9d2e4 : fetch_word Asan.M.loaded_segments (0x9df68 : word) = Some W_9d2e4.
Proof. vm_refl. Qed.
Lemma D_9d2e4 : decode_any W_9d2e4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2e8 : bv 32 := 0x0066a623.
Lemma F_9d2e8 : fetch_word Asan.M.loaded_segments (0x9df6c : word) = Some W_9d2e8.
Proof. vm_refl. Qed.
Lemma D_9d2e8 : decode_any W_9d2e8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2ec : bv 32 := 0x01068693.
Lemma F_9d2ec : fetch_word Asan.M.loaded_segments (0x9df70 : word) = Some W_9d2ec.
Proof. vm_refl. Qed.
Lemma D_9d2ec : decode_any W_9d2ec = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2f0 : bv 32 := 0x01058593.
Lemma F_9d2f0 : fetch_word Asan.M.loaded_segments (0x9df74 : word) = Some W_9d2f0.
Proof. vm_refl. Qed.
Lemma D_9d2f0 : decode_any W_9d2f0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2f4 : bv 32 := 0xfac7e2e3.
Lemma F_9d2f4 : fetch_word Asan.M.loaded_segments (0x9df78 : word) = Some W_9d2f4.
Proof. vm_refl. Qed.
Lemma D_9d2f4 : decode_any W_9d2f4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2f8 : bv 32 := 0xff358593.
Lemma F_9d2f8 : fetch_word Asan.M.loaded_segments (0x9df7c : word) = Some W_9d2f8.
Proof. vm_refl. Qed.
Lemma D_9d2f8 : decode_any W_9d2f8 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d2fc : bv 32 := 0x01000713.
Lemma F_9d2fc : fetch_word Asan.M.loaded_segments (0x9df80 : word) = Some W_9d2fc.
Proof. vm_refl. Qed.
Lemma D_9d2fc : decode_any W_9d2fc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d300 : bv 32 := 0xdae66ce3.
Lemma F_9d300 : fetch_word Asan.M.loaded_segments (0x9df84 : word) = Some W_9d300.
Proof. vm_refl. Qed.
Lemma D_9d300 : decode_any W_9d300 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d304 : bv 32 := 0x0005c703.
Lemma F_9d304 : fetch_word Asan.M.loaded_segments (0x9df88 : word) = Some W_9d304.
Proof. vm_refl. Qed.
Lemma D_9d304 : decode_any W_9d304 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d308 : bv 32 := 0x0015c783.
Lemma F_9d308 : fetch_word Asan.M.loaded_segments (0x9df8c : word) = Some W_9d308.
Proof. vm_refl. Qed.
Lemma D_9d308 : decode_any W_9d308 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d30c : bv 32 := 0x0025c803.
Lemma F_9d30c : fetch_word Asan.M.loaded_segments (0x9df90 : word) = Some W_9d30c.
Proof. vm_refl. Qed.
Lemma D_9d30c : decode_any W_9d30c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d310 : bv 32 := 0x0035c883.
Lemma F_9d310 : fetch_word Asan.M.loaded_segments (0x9df94 : word) = Some W_9d310.
Proof. vm_refl. Qed.
Lemma D_9d310 : decode_any W_9d310 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d314 : bv 32 := 0x0045c283.
Lemma F_9d314 : fetch_word Asan.M.loaded_segments (0x9df98 : word) = Some W_9d314.
Proof. vm_refl. Qed.
Lemma D_9d314 : decode_any W_9d314 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d318 : bv 32 := 0x0055c303.
Lemma F_9d318 : fetch_word Asan.M.loaded_segments (0x9df9c : word) = Some W_9d318.
Proof. vm_refl. Qed.
Lemma D_9d318 : decode_any W_9d318 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d31c : bv 32 := 0x0065c383.
Lemma F_9d31c : fetch_word Asan.M.loaded_segments (0x9dfa0 : word) = Some W_9d31c.
Proof. vm_refl. Qed.
Lemma D_9d31c : decode_any W_9d31c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d320 : bv 32 := 0x0075ce03.
Lemma F_9d320 : fetch_word Asan.M.loaded_segments (0x9dfa4 : word) = Some W_9d320.
Proof. vm_refl. Qed.
Lemma D_9d320 : decode_any W_9d320 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d324 : bv 32 := 0x00e68023.
Lemma F_9d324 : fetch_word Asan.M.loaded_segments (0x9dfa8 : word) = Some W_9d324.
Proof. vm_refl. Qed.
Lemma D_9d324 : decode_any W_9d324 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d328 : bv 32 := 0x00f680a3.
Lemma F_9d328 : fetch_word Asan.M.loaded_segments (0x9dfac : word) = Some W_9d328.
Proof. vm_refl. Qed.
Lemma D_9d328 : decode_any W_9d328 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d32c : bv 32 := 0x01068123.
Lemma F_9d32c : fetch_word Asan.M.loaded_segments (0x9dfb0 : word) = Some W_9d32c.
Proof. vm_refl. Qed.
Lemma D_9d32c : decode_any W_9d32c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d330 : bv 32 := 0x011681a3.
Lemma F_9d330 : fetch_word Asan.M.loaded_segments (0x9dfb4 : word) = Some W_9d330.
Proof. vm_refl. Qed.
Lemma D_9d330 : decode_any W_9d330 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d334 : bv 32 := 0x0085c703.
Lemma F_9d334 : fetch_word Asan.M.loaded_segments (0x9dfb8 : word) = Some W_9d334.
Proof. vm_refl. Qed.
Lemma D_9d334 : decode_any W_9d334 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d338 : bv 32 := 0x0095c783.
Lemma F_9d338 : fetch_word Asan.M.loaded_segments (0x9dfbc : word) = Some W_9d338.
Proof. vm_refl. Qed.
Lemma D_9d338 : decode_any W_9d338 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d33c : bv 32 := 0x00a5c803.
Lemma F_9d33c : fetch_word Asan.M.loaded_segments (0x9dfc0 : word) = Some W_9d33c.
Proof. vm_refl. Qed.
Lemma D_9d33c : decode_any W_9d33c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d340 : bv 32 := 0x00b5c883.
Lemma F_9d340 : fetch_word Asan.M.loaded_segments (0x9dfc4 : word) = Some W_9d340.
Proof. vm_refl. Qed.
Lemma D_9d340 : decode_any W_9d340 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d344 : bv 32 := 0x00568223.
Lemma F_9d344 : fetch_word Asan.M.loaded_segments (0x9dfc8 : word) = Some W_9d344.
Proof. vm_refl. Qed.
Lemma D_9d344 : decode_any W_9d344 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d348 : bv 32 := 0x006682a3.
Lemma F_9d348 : fetch_word Asan.M.loaded_segments (0x9dfcc : word) = Some W_9d348.
Proof. vm_refl. Qed.
Lemma D_9d348 : decode_any W_9d348 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d34c : bv 32 := 0x00768323.
Lemma F_9d34c : fetch_word Asan.M.loaded_segments (0x9dfd0 : word) = Some W_9d34c.
Proof. vm_refl. Qed.
Lemma D_9d34c : decode_any W_9d34c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d350 : bv 32 := 0x01c683a3.
Lemma F_9d350 : fetch_word Asan.M.loaded_segments (0x9dfd4 : word) = Some W_9d350.
Proof. vm_refl. Qed.
Lemma D_9d350 : decode_any W_9d350 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d354 : bv 32 := 0x00c5c283.
Lemma F_9d354 : fetch_word Asan.M.loaded_segments (0x9dfd8 : word) = Some W_9d354.
Proof. vm_refl. Qed.
Lemma D_9d354 : decode_any W_9d354 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d358 : bv 32 := 0x00d5c303.
Lemma F_9d358 : fetch_word Asan.M.loaded_segments (0x9dfdc : word) = Some W_9d358.
Proof. vm_refl. Qed.
Lemma D_9d358 : decode_any W_9d358 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d35c : bv 32 := 0x00e5c383.
Lemma F_9d35c : fetch_word Asan.M.loaded_segments (0x9dfe0 : word) = Some W_9d35c.
Proof. vm_refl. Qed.
Lemma D_9d35c : decode_any W_9d35c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d360 : bv 32 := 0x00f5ce03.
Lemma F_9d360 : fetch_word Asan.M.loaded_segments (0x9dfe4 : word) = Some W_9d360.
Proof. vm_refl. Qed.
Lemma D_9d360 : decode_any W_9d360 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d364 : bv 32 := 0x01058593.
Lemma F_9d364 : fetch_word Asan.M.loaded_segments (0x9dfe8 : word) = Some W_9d364.
Proof. vm_refl. Qed.
Lemma D_9d364 : decode_any W_9d364 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d368 : bv 32 := 0x00e68423.
Lemma F_9d368 : fetch_word Asan.M.loaded_segments (0x9dfec : word) = Some W_9d368.
Proof. vm_refl. Qed.
Lemma D_9d368 : decode_any W_9d368 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d36c : bv 32 := 0x00f684a3.
Lemma F_9d36c : fetch_word Asan.M.loaded_segments (0x9dff0 : word) = Some W_9d36c.
Proof. vm_refl. Qed.
Lemma D_9d36c : decode_any W_9d36c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d370 : bv 32 := 0x01068523.
Lemma F_9d370 : fetch_word Asan.M.loaded_segments (0x9dff4 : word) = Some W_9d370.
Proof. vm_refl. Qed.
Lemma D_9d370 : decode_any W_9d370 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d374 : bv 32 := 0x011685a3.
Lemma F_9d374 : fetch_word Asan.M.loaded_segments (0x9dff8 : word) = Some W_9d374.
Proof. vm_refl. Qed.
Lemma D_9d374 : decode_any W_9d374 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d378 : bv 32 := 0x01068713.
Lemma F_9d378 : fetch_word Asan.M.loaded_segments (0x9dffc : word) = Some W_9d378.
Proof. vm_refl. Qed.
Lemma D_9d378 : decode_any W_9d378 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d37c : bv 32 := 0x00568623.
Lemma F_9d37c : fetch_word Asan.M.loaded_segments (0x9e000 : word) = Some W_9d37c.
Proof. vm_refl. Qed.
Lemma D_9d37c : decode_any W_9d37c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d380 : bv 32 := 0x006686a3.
Lemma F_9d380 : fetch_word Asan.M.loaded_segments (0x9e004 : word) = Some W_9d380.
Proof. vm_refl. Qed.
Lemma D_9d380 : decode_any W_9d380 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d384 : bv 32 := 0x00768723.
Lemma F_9d384 : fetch_word Asan.M.loaded_segments (0x9e008 : word) = Some W_9d384.
Proof. vm_refl. Qed.
Lemma D_9d384 : decode_any W_9d384 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d388 : bv 32 := 0x01c687a3.
Lemma F_9d388 : fetch_word Asan.M.loaded_segments (0x9e00c : word) = Some W_9d388.
Proof. vm_refl. Qed.
Lemma D_9d388 : decode_any W_9d388 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d38c : bv 32 := 0x00070693.
Lemma F_9d38c : fetch_word Asan.M.loaded_segments (0x9e010 : word) = Some W_9d38c.
Proof. vm_refl. Qed.
Lemma D_9d38c : decode_any W_9d38c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d390 : bv 32 := 0x00867713.
Lemma F_9d390 : fetch_word Asan.M.loaded_segments (0x9e014 : word) = Some W_9d390.
Proof. vm_refl. Qed.
Lemma D_9d390 : decode_any W_9d390 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d394 : bv 32 := 0xd20706e3.
Lemma F_9d394 : fetch_word Asan.M.loaded_segments (0x9e018 : word) = Some W_9d394.
Proof. vm_refl. Qed.
Lemma D_9d394 : decode_any W_9d394 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d398 : bv 32 := 0x0005c703.
Lemma F_9d398 : fetch_word Asan.M.loaded_segments (0x9e01c : word) = Some W_9d398.
Proof. vm_refl. Qed.
Lemma D_9d398 : decode_any W_9d398 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d39c : bv 32 := 0x0015c783.
Lemma F_9d39c : fetch_word Asan.M.loaded_segments (0x9e020 : word) = Some W_9d39c.
Proof. vm_refl. Qed.
Lemma D_9d39c : decode_any W_9d39c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3a0 : bv 32 := 0x0025c803.
Lemma F_9d3a0 : fetch_word Asan.M.loaded_segments (0x9e024 : word) = Some W_9d3a0.
Proof. vm_refl. Qed.
Lemma D_9d3a0 : decode_any W_9d3a0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3a4 : bv 32 := 0x0035c883.
Lemma F_9d3a4 : fetch_word Asan.M.loaded_segments (0x9e028 : word) = Some W_9d3a4.
Proof. vm_refl. Qed.
Lemma D_9d3a4 : decode_any W_9d3a4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3a8 : bv 32 := 0x0045c283.
Lemma F_9d3a8 : fetch_word Asan.M.loaded_segments (0x9e02c : word) = Some W_9d3a8.
Proof. vm_refl. Qed.
Lemma D_9d3a8 : decode_any W_9d3a8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3ac : bv 32 := 0x0055c303.
Lemma F_9d3ac : fetch_word Asan.M.loaded_segments (0x9e030 : word) = Some W_9d3ac.
Proof. vm_refl. Qed.
Lemma D_9d3ac : decode_any W_9d3ac = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3b0 : bv 32 := 0x0065c383.
Lemma F_9d3b0 : fetch_word Asan.M.loaded_segments (0x9e034 : word) = Some W_9d3b0.
Proof. vm_refl. Qed.
Lemma D_9d3b0 : decode_any W_9d3b0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3b4 : bv 32 := 0x0075ce03.
Lemma F_9d3b4 : fetch_word Asan.M.loaded_segments (0x9e038 : word) = Some W_9d3b4.
Proof. vm_refl. Qed.
Lemma D_9d3b4 : decode_any W_9d3b4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3b8 : bv 32 := 0x00858593.
Lemma F_9d3b8 : fetch_word Asan.M.loaded_segments (0x9e03c : word) = Some W_9d3b8.
Proof. vm_refl. Qed.
Lemma D_9d3b8 : decode_any W_9d3b8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3bc : bv 32 := 0x00e68023.
Lemma F_9d3bc : fetch_word Asan.M.loaded_segments (0x9e040 : word) = Some W_9d3bc.
Proof. vm_refl. Qed.
Lemma D_9d3bc : decode_any W_9d3bc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3c0 : bv 32 := 0x00f680a3.
Lemma F_9d3c0 : fetch_word Asan.M.loaded_segments (0x9e044 : word) = Some W_9d3c0.
Proof. vm_refl. Qed.
Lemma D_9d3c0 : decode_any W_9d3c0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3c4 : bv 32 := 0x01068123.
Lemma F_9d3c4 : fetch_word Asan.M.loaded_segments (0x9e048 : word) = Some W_9d3c4.
Proof. vm_refl. Qed.
Lemma D_9d3c4 : decode_any W_9d3c4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3c8 : bv 32 := 0x011681a3.
Lemma F_9d3c8 : fetch_word Asan.M.loaded_segments (0x9e04c : word) = Some W_9d3c8.
Proof. vm_refl. Qed.
Lemma D_9d3c8 : decode_any W_9d3c8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3cc : bv 32 := 0x00868713.
Lemma F_9d3cc : fetch_word Asan.M.loaded_segments (0x9e050 : word) = Some W_9d3cc.
Proof. vm_refl. Qed.
Lemma D_9d3cc : decode_any W_9d3cc = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3d0 : bv 32 := 0x00568223.
Lemma F_9d3d0 : fetch_word Asan.M.loaded_segments (0x9e054 : word) = Some W_9d3d0.
Proof. vm_refl. Qed.
Lemma D_9d3d0 : decode_any W_9d3d0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3d4 : bv 32 := 0x006682a3.
Lemma F_9d3d4 : fetch_word Asan.M.loaded_segments (0x9e058 : word) = Some W_9d3d4.
Proof. vm_refl. Qed.
Lemma D_9d3d4 : decode_any W_9d3d4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3d8 : bv 32 := 0x00768323.
Lemma F_9d3d8 : fetch_word Asan.M.loaded_segments (0x9e05c : word) = Some W_9d3d8.
Proof. vm_refl. Qed.
Lemma D_9d3d8 : decode_any W_9d3d8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3dc : bv 32 := 0x01c683a3.
Lemma F_9d3dc : fetch_word Asan.M.loaded_segments (0x9e060 : word) = Some W_9d3dc.
Proof. vm_refl. Qed.
Lemma D_9d3dc : decode_any W_9d3dc = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3e0 : bv 32 := 0x00070693.
Lemma F_9d3e0 : fetch_word Asan.M.loaded_segments (0x9e064 : word) = Some W_9d3e0.
Proof. vm_refl. Qed.
Lemma D_9d3e0 : decode_any W_9d3e0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3e4 : bv 32 := 0x00467713.
Lemma F_9d3e4 : fetch_word Asan.M.loaded_segments (0x9e068 : word) = Some W_9d3e4.
Proof. vm_refl. Qed.
Lemma D_9d3e4 : decode_any W_9d3e4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3e8 : bv 32 := 0x02070863.
Lemma F_9d3e8 : fetch_word Asan.M.loaded_segments (0x9e06c : word) = Some W_9d3e8.
Proof. vm_refl. Qed.
Lemma D_9d3e8 : decode_any W_9d3e8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3ec : bv 32 := 0x0005c703.
Lemma F_9d3ec : fetch_word Asan.M.loaded_segments (0x9e070 : word) = Some W_9d3ec.
Proof. vm_refl. Qed.
Lemma D_9d3ec : decode_any W_9d3ec = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3f0 : bv 32 := 0x0015c783.
Lemma F_9d3f0 : fetch_word Asan.M.loaded_segments (0x9e074 : word) = Some W_9d3f0.
Proof. vm_refl. Qed.
Lemma D_9d3f0 : decode_any W_9d3f0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3f4 : bv 32 := 0x0025c803.
Lemma F_9d3f4 : fetch_word Asan.M.loaded_segments (0x9e078 : word) = Some W_9d3f4.
Proof. vm_refl. Qed.
Lemma D_9d3f4 : decode_any W_9d3f4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3f8 : bv 32 := 0x0035c883.
Lemma F_9d3f8 : fetch_word Asan.M.loaded_segments (0x9e07c : word) = Some W_9d3f8.
Proof. vm_refl. Qed.
Lemma D_9d3f8 : decode_any W_9d3f8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d3fc : bv 32 := 0x00458593.
Lemma F_9d3fc : fetch_word Asan.M.loaded_segments (0x9e080 : word) = Some W_9d3fc.
Proof. vm_refl. Qed.
Lemma D_9d3fc : decode_any W_9d3fc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d400 : bv 32 := 0x00468293.
Lemma F_9d400 : fetch_word Asan.M.loaded_segments (0x9e084 : word) = Some W_9d400.
Proof. vm_refl. Qed.
Lemma D_9d400 : decode_any W_9d400 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d404 : bv 32 := 0x00e68023.
Lemma F_9d404 : fetch_word Asan.M.loaded_segments (0x9e088 : word) = Some W_9d404.
Proof. vm_refl. Qed.
Lemma D_9d404 : decode_any W_9d404 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d408 : bv 32 := 0x00f680a3.
Lemma F_9d408 : fetch_word Asan.M.loaded_segments (0x9e08c : word) = Some W_9d408.
Proof. vm_refl. Qed.
Lemma D_9d408 : decode_any W_9d408 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d40c : bv 32 := 0x01068123.
Lemma F_9d40c : fetch_word Asan.M.loaded_segments (0x9e090 : word) = Some W_9d40c.
Proof. vm_refl. Qed.
Lemma D_9d40c : decode_any W_9d40c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d410 : bv 32 := 0x011681a3.
Lemma F_9d410 : fetch_word Asan.M.loaded_segments (0x9e094 : word) = Some W_9d410.
Proof. vm_refl. Qed.
Lemma D_9d410 : decode_any W_9d410 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d414 : bv 32 := 0x00028693.
Lemma F_9d414 : fetch_word Asan.M.loaded_segments (0x9e098 : word) = Some W_9d414.
Proof. vm_refl. Qed.
Lemma D_9d414 : decode_any W_9d414 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d418 : bv 32 := 0x00267713.
Lemma F_9d418 : fetch_word Asan.M.loaded_segments (0x9e09c : word) = Some W_9d418.
Proof. vm_refl. Qed.
Lemma D_9d418 : decode_any W_9d418 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d41c : bv 32 := 0x00071863.
Lemma F_9d41c : fetch_word Asan.M.loaded_segments (0x9e0a0 : word) = Some W_9d41c.
Proof. vm_refl. Qed.
Lemma D_9d41c : decode_any W_9d41c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d420 : bv 32 := 0x00167613.
Lemma F_9d420 : fetch_word Asan.M.loaded_segments (0x9e0a4 : word) = Some W_9d420.
Proof. vm_refl. Qed.
Lemma D_9d420 : decode_any W_9d420 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d424 : bv 32 := 0x02061663.
Lemma F_9d424 : fetch_word Asan.M.loaded_segments (0x9e0a8 : word) = Some W_9d424.
Proof. vm_refl. Qed.
Lemma D_9d424 : decode_any W_9d424 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d428 : bv 32 := 0x00008067.
Lemma F_9d428 : fetch_word Asan.M.loaded_segments (0x9e0ac : word) = Some W_9d428.
Proof. vm_refl. Qed.
Lemma D_9d428 : decode_any W_9d428 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d42c : bv 32 := 0x0005c703.
Lemma F_9d42c : fetch_word Asan.M.loaded_segments (0x9e0b0 : word) = Some W_9d42c.
Proof. vm_refl. Qed.
Lemma D_9d42c : decode_any W_9d42c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d430 : bv 32 := 0x0015c783.
Lemma F_9d430 : fetch_word Asan.M.loaded_segments (0x9e0b4 : word) = Some W_9d430.
Proof. vm_refl. Qed.
Lemma D_9d430 : decode_any W_9d430 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d434 : bv 32 := 0x00258593.
Lemma F_9d434 : fetch_word Asan.M.loaded_segments (0x9e0b8 : word) = Some W_9d434.
Proof. vm_refl. Qed.
Lemma D_9d434 : decode_any W_9d434 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d438 : bv 32 := 0x00268813.
Lemma F_9d438 : fetch_word Asan.M.loaded_segments (0x9e0bc : word) = Some W_9d438.
Proof. vm_refl. Qed.
Lemma D_9d438 : decode_any W_9d438 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d43c : bv 32 := 0x00e68023.
Lemma F_9d43c : fetch_word Asan.M.loaded_segments (0x9e0c0 : word) = Some W_9d43c.
Proof. vm_refl. Qed.
Lemma D_9d43c : decode_any W_9d43c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d440 : bv 32 := 0x00f680a3.
Lemma F_9d440 : fetch_word Asan.M.loaded_segments (0x9e0c4 : word) = Some W_9d440.
Proof. vm_refl. Qed.
Lemma D_9d440 : decode_any W_9d440 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d444 : bv 32 := 0x00080693.
Lemma F_9d444 : fetch_word Asan.M.loaded_segments (0x9e0c8 : word) = Some W_9d444.
Proof. vm_refl. Qed.
Lemma D_9d444 : decode_any W_9d444 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d448 : bv 32 := 0x00167613.
Lemma F_9d448 : fetch_word Asan.M.loaded_segments (0x9e0cc : word) = Some W_9d448.
Proof. vm_refl. Qed.
Lemma D_9d448 : decode_any W_9d448 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d44c : bv 32 := 0xfc060ee3.
Lemma F_9d44c : fetch_word Asan.M.loaded_segments (0x9e0d0 : word) = Some W_9d44c.
Proof. vm_refl. Qed.
Lemma D_9d44c : decode_any W_9d44c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d450 : bv 32 := 0x0005c583.
Lemma F_9d450 : fetch_word Asan.M.loaded_segments (0x9e0d4 : word) = Some W_9d450.
Proof. vm_refl. Qed.
Lemma D_9d450 : decode_any W_9d450 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d454 : bv 32 := 0x00b68023.
Lemma F_9d454 : fetch_word Asan.M.loaded_segments (0x9e0d8 : word) = Some W_9d454.
Proof. vm_refl. Qed.
Lemma D_9d454 : decode_any W_9d454 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d458 : bv 32 := 0x00008067.
Lemma F_9d458 : fetch_word Asan.M.loaded_segments (0x9e0dc : word) = Some W_9d458.
Proof. vm_refl. Qed.
Lemma D_9d458 : decode_any W_9d458 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

