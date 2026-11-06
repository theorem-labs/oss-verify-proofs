(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7ee1c : bv 32 := 0x5450006f.
Lemma F_7ee1c : fetch_word Asan.M.loaded_segments (0x7ee6c : word) = Some W_7ee1c.
Proof. vm_refl. Qed.
Lemma D_7ee1c : decode_any W_7ee1c = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee20 : bv 32 := 0x2000106f.
Lemma F_7ee20 : fetch_word Asan.M.loaded_segments (0x7ee70 : word) = Some W_7ee20.
Proof. vm_refl. Qed.
Lemma D_7ee20 : decode_any W_7ee20 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee24 : bv 32 := 0x81010113.
Lemma F_7ee24 : fetch_word Asan.M.loaded_segments (0x7ee74 : word) = Some W_7ee24.
Proof. vm_refl. Qed.
Lemma D_7ee24 : decode_any W_7ee24 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee28 : bv 32 := 0x7e113423.
Lemma F_7ee28 : fetch_word Asan.M.loaded_segments (0x7ee78 : word) = Some W_7ee28.
Proof. vm_refl. Qed.
Lemma D_7ee28 : decode_any W_7ee28 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee2c : bv 32 := 0x7e813023.
Lemma F_7ee2c : fetch_word Asan.M.loaded_segments (0x7ee7c : word) = Some W_7ee2c.
Proof. vm_refl. Qed.
Lemma D_7ee2c : decode_any W_7ee2c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee30 : bv 32 := 0x7c913c23.
Lemma F_7ee30 : fetch_word Asan.M.loaded_segments (0x7ee80 : word) = Some W_7ee30.
Proof. vm_refl. Qed.
Lemma D_7ee30 : decode_any W_7ee30 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee34 : bv 32 := 0x7d213823.
Lemma F_7ee34 : fetch_word Asan.M.loaded_segments (0x7ee84 : word) = Some W_7ee34.
Proof. vm_refl. Qed.
Lemma D_7ee34 : decode_any W_7ee34 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee38 : bv 32 := 0x7d313423.
Lemma F_7ee38 : fetch_word Asan.M.loaded_segments (0x7ee88 : word) = Some W_7ee38.
Proof. vm_refl. Qed.
Lemma D_7ee38 : decode_any W_7ee38 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee3c : bv 32 := 0x7d413023.
Lemma F_7ee3c : fetch_word Asan.M.loaded_segments (0x7ee8c : word) = Some W_7ee3c.
Proof. vm_refl. Qed.
Lemma D_7ee3c : decode_any W_7ee3c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee40 : bv 32 := 0x7b513c23.
Lemma F_7ee40 : fetch_word Asan.M.loaded_segments (0x7ee90 : word) = Some W_7ee40.
Proof. vm_refl. Qed.
Lemma D_7ee40 : decode_any W_7ee40 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee44 : bv 32 := 0x7b613823.
Lemma F_7ee44 : fetch_word Asan.M.loaded_segments (0x7ee94 : word) = Some W_7ee44.
Proof. vm_refl. Qed.
Lemma D_7ee44 : decode_any W_7ee44 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee48 : bv 32 := 0x7b713423.
Lemma F_7ee48 : fetch_word Asan.M.loaded_segments (0x7ee98 : word) = Some W_7ee48.
Proof. vm_refl. Qed.
Lemma D_7ee48 : decode_any W_7ee48 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee4c : bv 32 := 0x7f010413.
Lemma F_7ee4c : fetch_word Asan.M.loaded_segments (0x7ee9c : word) = Some W_7ee4c.
Proof. vm_refl. Qed.
Lemma D_7ee4c : decode_any W_7ee4c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee50 : bv 32 := 0xf9010113.
Lemma F_7ee50 : fetch_word Asan.M.loaded_segments (0x7eea0 : word) = Some W_7ee50.
Proof. vm_refl. Qed.
Lemma D_7ee50 : decode_any W_7ee50 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee54 : bv 32 := 0x000d5697.
Lemma F_7ee54 : fetch_word Asan.M.loaded_segments (0x7eea4 : word) = Some W_7ee54.
Proof. vm_refl. Qed.
Lemma D_7ee54 : decode_any W_7ee54 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee58 : bv 32 := 0xdfc6b683.
Lemma F_7ee58 : fetch_word Asan.M.loaded_segments (0x7eea8 : word) = Some W_7ee58.
Proof. vm_refl. Qed.
Lemma D_7ee58 : decode_any W_7ee58 = Some (Load SZ8 true 13 13 3580, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee5c : bv 32 := 0x0006c683.
Lemma F_7ee5c : fetch_word Asan.M.loaded_segments (0x7eeac : word) = Some W_7ee5c.
Proof. vm_refl. Qed.
Lemma D_7ee5c : decode_any W_7ee5c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee60 : bv 32 := 0x0e068863.
Lemma F_7ee60 : fetch_word Asan.M.loaded_segments (0x7eeb0 : word) = Some W_7ee60.
Proof. vm_refl. Qed.
Lemma D_7ee60 : decode_any W_7ee60 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee64 : bv 32 := 0x80040a13.
Lemma F_7ee64 : fetch_word Asan.M.loaded_segments (0x7eeb4 : word) = Some W_7ee64.
Proof. vm_refl. Qed.
Lemma D_7ee64 : decode_any W_7ee64 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee68 : bv 32 := 0xfa0a0a13.
Lemma F_7ee68 : fetch_word Asan.M.loaded_segments (0x7eeb8 : word) = Some W_7ee68.
Proof. vm_refl. Qed.
Lemma D_7ee68 : decode_any W_7ee68 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee6c : bv 32 := 0x00c58ab3.
Lemma F_7ee6c : fetch_word Asan.M.loaded_segments (0x7eebc : word) = Some W_7ee6c.
Proof. vm_refl. Qed.
Lemma D_7ee6c : decode_any W_7ee6c = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee70 : bv 32 := 0x00c509b3.
Lemma F_7ee70 : fetch_word Asan.M.loaded_segments (0x7eec0 : word) = Some W_7ee70.
Proof. vm_refl. Qed.
Lemma D_7ee70 : decode_any W_7ee70 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee74 : bv 32 := 0x00b50663.
Lemma F_7ee74 : fetch_word Asan.M.loaded_segments (0x7eec4 : word) = Some W_7ee74.
Proof. vm_refl. Qed.
Lemma D_7ee74 : decode_any W_7ee74 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee78 : bv 32 := 0x0135f463.
Lemma F_7ee78 : fetch_word Asan.M.loaded_segments (0x7eec8 : word) = Some W_7ee78.
Proof. vm_refl. Qed.
Lemma D_7ee78 : decode_any W_7ee78 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee7c : bv 32 := 0x1b556a63.
Lemma F_7ee7c : fetch_word Asan.M.loaded_segments (0x7eecc : word) = Some W_7ee7c.
Proof. vm_refl. Qed.
Lemma D_7ee7c : decode_any W_7ee7c = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee80 : bv 32 := 0xfff5c693.
Lemma F_7ee80 : fetch_word Asan.M.loaded_segments (0x7eed0 : word) = Some W_7ee80.
Proof. vm_refl. Qed.
Lemma D_7ee80 : decode_any W_7ee80 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee84 : bv 32 := 0x26c6e463.
Lemma F_7ee84 : fetch_word Asan.M.loaded_segments (0x7eed4 : word) = Some W_7ee84.
Proof. vm_refl. Qed.
Lemma D_7ee84 : decode_any W_7ee84 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee88 : bv 32 := 0xfbf60b13.
Lemma F_7ee88 : fetch_word Asan.M.loaded_segments (0x7eed8 : word) = Some W_7ee88.
Proof. vm_refl. Qed.
Lemma D_7ee88 : decode_any W_7ee88 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee8c : bv 32 := 0xfbf00693.
Lemma F_7ee8c : fetch_word Asan.M.loaded_segments (0x7eedc : word) = Some W_7ee8c.
Proof. vm_refl. Qed.
Lemma D_7ee8c : decode_any W_7ee8c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee90 : bv 32 := 0x2f66f263.
Lemma F_7ee90 : fetch_word Asan.M.loaded_segments (0x7eee0 : word) = Some W_7ee90.
Proof. vm_refl. Qed.
Lemma D_7ee90 : decode_any W_7ee90 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee94 : bv 32 := 0x000d4697.
Lemma F_7ee94 : fetch_word Asan.M.loaded_segments (0x7eee4 : word) = Some W_7ee94.
Proof. vm_refl. Qed.
Lemma D_7ee94 : decode_any W_7ee94 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee98 : bv 32 := 0x2546b683.
Lemma F_7ee98 : fetch_word Asan.M.loaded_segments (0x7eee8 : word) = Some W_7ee98.
Proof. vm_refl. Qed.
Lemma D_7ee98 : decode_any W_7ee98 = Some (Load SZ8 true 13 13 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ee9c : bv 32 := 0x0006b703.
Lemma F_7ee9c : fetch_word Asan.M.loaded_segments (0x7eeec : word) = Some W_7ee9c.
Proof. vm_refl. Qed.
Lemma D_7ee9c : decode_any W_7ee9c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eea0 : bv 32 := 0xfffa8a93.
Lemma F_7eea0 : fetch_word Asan.M.loaded_segments (0x7eef0 : word) = Some W_7eea0.
Proof. vm_refl. Qed.
Lemma D_7eea0 : decode_any W_7eea0 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eea4 : bv 32 := 0x0035d693.
Lemma F_7eea4 : fetch_word Asan.M.loaded_segments (0x7eef4 : word) = Some W_7eea4.
Proof. vm_refl. Qed.
Lemma D_7eea4 : decode_any W_7eea4 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eea8 : bv 32 := 0x003ad793.
Lemma F_7eea8 : fetch_word Asan.M.loaded_segments (0x7eef8 : word) = Some W_7eea8.
Proof. vm_refl. Qed.
Lemma D_7eea8 : decode_any W_7eea8 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eeac : bv 32 := 0x00d706b3.
Lemma F_7eeac : fetch_word Asan.M.loaded_segments (0x7eefc : word) = Some W_7eeac.
Proof. vm_refl. Qed.
Lemma D_7eeac : decode_any W_7eeac = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eeb0 : bv 32 := 0x00f70733.
Lemma F_7eeb0 : fetch_word Asan.M.loaded_segments (0x7ef00 : word) = Some W_7eeb0.
Proof. vm_refl. Qed.
Lemma D_7eeb0 : decode_any W_7eeb0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eeb4 : bv 32 := 0xff86f793.
Lemma F_7eeb4 : fetch_word Asan.M.loaded_segments (0x7ef04 : word) = Some W_7eeb4.
Proof. vm_refl. Qed.
Lemma D_7eeb4 : decode_any W_7eeb4 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eeb8 : bv 32 := 0xff877813.
Lemma F_7eeb8 : fetch_word Asan.M.loaded_segments (0x7ef08 : word) = Some W_7eeb8.
Proof. vm_refl. Qed.
Lemma D_7eeb8 : decode_any W_7eeb8 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eebc : bv 32 := 0x0007b783.
Lemma F_7eebc : fetch_word Asan.M.loaded_segments (0x7ef0c : word) = Some W_7eebc.
Proof. vm_refl. Qed.
Lemma D_7eebc : decode_any W_7eebc = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eec0 : bv 32 := 0x00083803.
Lemma F_7eec0 : fetch_word Asan.M.loaded_segments (0x7ef10 : word) = Some W_7eec0.
Proof. vm_refl. Qed.
Lemma D_7eec0 : decode_any W_7eec0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eec4 : bv 32 := 0x00f867b3.
Lemma F_7eec4 : fetch_word Asan.M.loaded_segments (0x7ef14 : word) = Some W_7eec4.
Proof. vm_refl. Qed.
Lemma D_7eec4 : decode_any W_7eec4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eec8 : bv 32 := 0x2a079a63.
Lemma F_7eec8 : fetch_word Asan.M.loaded_segments (0x7ef18 : word) = Some W_7eec8.
Proof. vm_refl. Qed.
Lemma D_7eec8 : decode_any W_7eec8 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eecc : bv 32 := 0xfff54693.
Lemma F_7eecc : fetch_word Asan.M.loaded_segments (0x7ef1c : word) = Some W_7eecc.
Proof. vm_refl. Qed.
Lemma D_7eecc : decode_any W_7eecc = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eed0 : bv 32 := 0x0cc6ea63.
Lemma F_7eed0 : fetch_word Asan.M.loaded_segments (0x7ef20 : word) = Some W_7eed0.
Proof. vm_refl. Qed.
Lemma D_7eed0 : decode_any W_7eed0 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eed4 : bv 32 := 0xfbf00693.
Lemma F_7eed4 : fetch_word Asan.M.loaded_segments (0x7ef24 : word) = Some W_7eed4.
Proof. vm_refl. Qed.
Lemma D_7eed4 : decode_any W_7eed4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eed8 : bv 32 := 0x1566f863.
Lemma F_7eed8 : fetch_word Asan.M.loaded_segments (0x7ef28 : word) = Some W_7eed8.
Proof. vm_refl. Qed.
Lemma D_7eed8 : decode_any W_7eed8 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eedc : bv 32 := 0x000d4697.
Lemma F_7eedc : fetch_word Asan.M.loaded_segments (0x7ef2c : word) = Some W_7eedc.
Proof. vm_refl. Qed.
Lemma D_7eedc : decode_any W_7eedc = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eee0 : bv 32 := 0x20c6b683.
Lemma F_7eee0 : fetch_word Asan.M.loaded_segments (0x7ef30 : word) = Some W_7eee0.
Proof. vm_refl. Qed.
Lemma D_7eee0 : decode_any W_7eee0 = Some (Load SZ8 true 13 13 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eee4 : bv 32 := 0x0006b703.
Lemma F_7eee4 : fetch_word Asan.M.loaded_segments (0x7ef34 : word) = Some W_7eee4.
Proof. vm_refl. Qed.
Lemma D_7eee4 : decode_any W_7eee4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eee8 : bv 32 := 0xfff98993.
Lemma F_7eee8 : fetch_word Asan.M.loaded_segments (0x7ef38 : word) = Some W_7eee8.
Proof. vm_refl. Qed.
Lemma D_7eee8 : decode_any W_7eee8 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eeec : bv 32 := 0x00355693.
Lemma F_7eeec : fetch_word Asan.M.loaded_segments (0x7ef3c : word) = Some W_7eeec.
Proof. vm_refl. Qed.
Lemma D_7eeec : decode_any W_7eeec = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eef0 : bv 32 := 0x0039d793.
Lemma F_7eef0 : fetch_word Asan.M.loaded_segments (0x7ef40 : word) = Some W_7eef0.
Proof. vm_refl. Qed.
Lemma D_7eef0 : decode_any W_7eef0 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eef4 : bv 32 := 0x00d706b3.
Lemma F_7eef4 : fetch_word Asan.M.loaded_segments (0x7ef44 : word) = Some W_7eef4.
Proof. vm_refl. Qed.
Lemma D_7eef4 : decode_any W_7eef4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eef8 : bv 32 := 0x00f70733.
Lemma F_7eef8 : fetch_word Asan.M.loaded_segments (0x7ef48 : word) = Some W_7eef8.
Proof. vm_refl. Qed.
Lemma D_7eef8 : decode_any W_7eef8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eefc : bv 32 := 0xff86f793.
Lemma F_7eefc : fetch_word Asan.M.loaded_segments (0x7ef4c : word) = Some W_7eefc.
Proof. vm_refl. Qed.
Lemma D_7eefc : decode_any W_7eefc = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef00 : bv 32 := 0xff877813.
Lemma F_7ef00 : fetch_word Asan.M.loaded_segments (0x7ef50 : word) = Some W_7ef00.
Proof. vm_refl. Qed.
Lemma D_7ef00 : decode_any W_7ef00 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef04 : bv 32 := 0x0007b783.
Lemma F_7ef04 : fetch_word Asan.M.loaded_segments (0x7ef54 : word) = Some W_7ef04.
Proof. vm_refl. Qed.
Lemma D_7ef04 : decode_any W_7ef04 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef08 : bv 32 := 0x00083803.
Lemma F_7ef08 : fetch_word Asan.M.loaded_segments (0x7ef58 : word) = Some W_7ef08.
Proof. vm_refl. Qed.
Lemma D_7ef08 : decode_any W_7ef08 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef0c : bv 32 := 0x00f867b3.
Lemma F_7ef0c : fetch_word Asan.M.loaded_segments (0x7ef5c : word) = Some W_7ef0c.
Proof. vm_refl. Qed.
Lemma D_7ef0c : decode_any W_7ef0c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef10 : bv 32 := 0x30079863.
Lemma F_7ef10 : fetch_word Asan.M.loaded_segments (0x7ef60 : word) = Some W_7ef10.
Proof. vm_refl. Qed.
Lemma D_7ef10 : decode_any W_7ef10 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef14 : bv 32 := 0x000d6697.
Lemma F_7ef14 : fetch_word Asan.M.loaded_segments (0x7ef64 : word) = Some W_7ef14.
Proof. vm_refl. Qed.
Lemma D_7ef14 : decode_any W_7ef14 = Some (Auipc 13 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef18 : bv 32 := 0x1f46b683.
Lemma F_7ef18 : fetch_word Asan.M.loaded_segments (0x7ef68 : word) = Some W_7ef18.
Proof. vm_refl. Qed.
Lemma D_7ef18 : decode_any W_7ef18 = Some (Load SZ8 true 13 13 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef1c : bv 32 := 0x000680e7.
Lemma F_7ef1c : fetch_word Asan.M.loaded_segments (0x7ef6c : word) = Some W_7ef1c.
Proof. vm_refl. Qed.
Lemma D_7ef1c : decode_any W_7ef1c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef20 : bv 32 := 0x07010113.
Lemma F_7ef20 : fetch_word Asan.M.loaded_segments (0x7ef70 : word) = Some W_7ef20.
Proof. vm_refl. Qed.
Lemma D_7ef20 : decode_any W_7ef20 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef24 : bv 32 := 0x7e813083.
Lemma F_7ef24 : fetch_word Asan.M.loaded_segments (0x7ef74 : word) = Some W_7ef24.
Proof. vm_refl. Qed.
Lemma D_7ef24 : decode_any W_7ef24 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef28 : bv 32 := 0x7e013403.
Lemma F_7ef28 : fetch_word Asan.M.loaded_segments (0x7ef78 : word) = Some W_7ef28.
Proof. vm_refl. Qed.
Lemma D_7ef28 : decode_any W_7ef28 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef2c : bv 32 := 0x7d813483.
Lemma F_7ef2c : fetch_word Asan.M.loaded_segments (0x7ef7c : word) = Some W_7ef2c.
Proof. vm_refl. Qed.
Lemma D_7ef2c : decode_any W_7ef2c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef30 : bv 32 := 0x7d013903.
Lemma F_7ef30 : fetch_word Asan.M.loaded_segments (0x7ef80 : word) = Some W_7ef30.
Proof. vm_refl. Qed.
Lemma D_7ef30 : decode_any W_7ef30 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef34 : bv 32 := 0x7c813983.
Lemma F_7ef34 : fetch_word Asan.M.loaded_segments (0x7ef84 : word) = Some W_7ef34.
Proof. vm_refl. Qed.
Lemma D_7ef34 : decode_any W_7ef34 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef38 : bv 32 := 0x7c013a03.
Lemma F_7ef38 : fetch_word Asan.M.loaded_segments (0x7ef88 : word) = Some W_7ef38.
Proof. vm_refl. Qed.
Lemma D_7ef38 : decode_any W_7ef38 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef3c : bv 32 := 0x7b813a83.
Lemma F_7ef3c : fetch_word Asan.M.loaded_segments (0x7ef8c : word) = Some W_7ef3c.
Proof. vm_refl. Qed.
Lemma D_7ef3c : decode_any W_7ef3c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef40 : bv 32 := 0x7b013b03.
Lemma F_7ef40 : fetch_word Asan.M.loaded_segments (0x7ef90 : word) = Some W_7ef40.
Proof. vm_refl. Qed.
Lemma D_7ef40 : decode_any W_7ef40 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef44 : bv 32 := 0x7a813b83.
Lemma F_7ef44 : fetch_word Asan.M.loaded_segments (0x7ef94 : word) = Some W_7ef44.
Proof. vm_refl. Qed.
Lemma D_7ef44 : decode_any W_7ef44 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef48 : bv 32 := 0x7f010113.
Lemma F_7ef48 : fetch_word Asan.M.loaded_segments (0x7ef98 : word) = Some W_7ef48.
Proof. vm_refl. Qed.
Lemma D_7ef48 : decode_any W_7ef48 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef4c : bv 32 := 0x00008067.
Lemma F_7ef4c : fetch_word Asan.M.loaded_segments (0x7ef9c : word) = Some W_7ef4c.
Proof. vm_refl. Qed.
Lemma D_7ef4c : decode_any W_7ef4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

