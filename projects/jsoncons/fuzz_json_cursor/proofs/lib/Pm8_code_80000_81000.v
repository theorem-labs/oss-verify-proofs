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

Definition W_80020 : bv 32 := 0x81010113.
Lemma F_80020 : fetch_word Asan.M.loaded_segments (0x80070 : word) = Some W_80020.
Proof. vm_refl. Qed.
Lemma D_80020 : decode_any W_80020 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80024 : bv 32 := 0x7e113423.
Lemma F_80024 : fetch_word Asan.M.loaded_segments (0x80074 : word) = Some W_80024.
Proof. vm_refl. Qed.
Lemma D_80024 : decode_any W_80024 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80028 : bv 32 := 0x7e813023.
Lemma F_80028 : fetch_word Asan.M.loaded_segments (0x80078 : word) = Some W_80028.
Proof. vm_refl. Qed.
Lemma D_80028 : decode_any W_80028 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8002c : bv 32 := 0x7c913c23.
Lemma F_8002c : fetch_word Asan.M.loaded_segments (0x8007c : word) = Some W_8002c.
Proof. vm_refl. Qed.
Lemma D_8002c : decode_any W_8002c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80030 : bv 32 := 0x7d213823.
Lemma F_80030 : fetch_word Asan.M.loaded_segments (0x80080 : word) = Some W_80030.
Proof. vm_refl. Qed.
Lemma D_80030 : decode_any W_80030 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80034 : bv 32 := 0x7d313423.
Lemma F_80034 : fetch_word Asan.M.loaded_segments (0x80084 : word) = Some W_80034.
Proof. vm_refl. Qed.
Lemma D_80034 : decode_any W_80034 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80038 : bv 32 := 0x7d413023.
Lemma F_80038 : fetch_word Asan.M.loaded_segments (0x80088 : word) = Some W_80038.
Proof. vm_refl. Qed.
Lemma D_80038 : decode_any W_80038 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8003c : bv 32 := 0x7b513c23.
Lemma F_8003c : fetch_word Asan.M.loaded_segments (0x8008c : word) = Some W_8003c.
Proof. vm_refl. Qed.
Lemma D_8003c : decode_any W_8003c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80040 : bv 32 := 0x7b613823.
Lemma F_80040 : fetch_word Asan.M.loaded_segments (0x80090 : word) = Some W_80040.
Proof. vm_refl. Qed.
Lemma D_80040 : decode_any W_80040 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_80044 : bv 32 := 0x7b713423.
Lemma F_80044 : fetch_word Asan.M.loaded_segments (0x80094 : word) = Some W_80044.
Proof. vm_refl. Qed.
Lemma D_80044 : decode_any W_80044 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_80048 : bv 32 := 0x7b813023.
Lemma F_80048 : fetch_word Asan.M.loaded_segments (0x80098 : word) = Some W_80048.
Proof. vm_refl. Qed.
Lemma D_80048 : decode_any W_80048 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_8004c : bv 32 := 0x7f010413.
Lemma F_8004c : fetch_word Asan.M.loaded_segments (0x8009c : word) = Some W_8004c.
Proof. vm_refl. Qed.
Lemma D_8004c : decode_any W_8004c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80050 : bv 32 := 0xf8010113.
Lemma F_80050 : fetch_word Asan.M.loaded_segments (0x800a0 : word) = Some W_80050.
Proof. vm_refl. Qed.
Lemma D_80050 : decode_any W_80050 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_80054 : bv 32 := 0x000d4697.
Lemma F_80054 : fetch_word Asan.M.loaded_segments (0x800a4 : word) = Some W_80054.
Proof. vm_refl. Qed.
Lemma D_80054 : decode_any W_80054 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_80058 : bv 32 := 0xbfc6b683.
Lemma F_80058 : fetch_word Asan.M.loaded_segments (0x800a8 : word) = Some W_80058.
Proof. vm_refl. Qed.
Lemma D_80058 : decode_any W_80058 = Some (Load SZ8 true 13 13 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_8005c : bv 32 := 0x0006c683.
Lemma F_8005c : fetch_word Asan.M.loaded_segments (0x800ac : word) = Some W_8005c.
Proof. vm_refl. Qed.
Lemma D_8005c : decode_any W_8005c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80060 : bv 32 := 0x0e068a63.
Lemma F_80060 : fetch_word Asan.M.loaded_segments (0x800b0 : word) = Some W_80060.
Proof. vm_refl. Qed.
Lemma D_80060 : decode_any W_80060 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_80064 : bv 32 := 0x80040a93.
Lemma F_80064 : fetch_word Asan.M.loaded_segments (0x800b4 : word) = Some W_80064.
Proof. vm_refl. Qed.
Lemma D_80064 : decode_any W_80064 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80068 : bv 32 := 0xf98a8a93.
Lemma F_80068 : fetch_word Asan.M.loaded_segments (0x800b8 : word) = Some W_80068.
Proof. vm_refl. Qed.
Lemma D_80068 : decode_any W_80068 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_8006c : bv 32 := 0x00c589b3.
Lemma F_8006c : fetch_word Asan.M.loaded_segments (0x800bc : word) = Some W_8006c.
Proof. vm_refl. Qed.
Lemma D_8006c : decode_any W_8006c = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80070 : bv 32 := 0x00c50a33.
Lemma F_80070 : fetch_word Asan.M.loaded_segments (0x800c0 : word) = Some W_80070.
Proof. vm_refl. Qed.
Lemma D_80070 : decode_any W_80070 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80074 : bv 32 := 0x00b50663.
Lemma F_80074 : fetch_word Asan.M.loaded_segments (0x800c4 : word) = Some W_80074.
Proof. vm_refl. Qed.
Lemma D_80074 : decode_any W_80074 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80078 : bv 32 := 0x0145f463.
Lemma F_80078 : fetch_word Asan.M.loaded_segments (0x800c8 : word) = Some W_80078.
Proof. vm_refl. Qed.
Lemma D_80078 : decode_any W_80078 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8007c : bv 32 := 0x1b356e63.
Lemma F_8007c : fetch_word Asan.M.loaded_segments (0x800cc : word) = Some W_8007c.
Proof. vm_refl. Qed.
Lemma D_8007c : decode_any W_8007c = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_80080 : bv 32 := 0xfff5c693.
Lemma F_80080 : fetch_word Asan.M.loaded_segments (0x800d0 : word) = Some W_80080.
Proof. vm_refl. Qed.
Lemma D_80080 : decode_any W_80080 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80084 : bv 32 := 0x26c6e863.
Lemma F_80084 : fetch_word Asan.M.loaded_segments (0x800d4 : word) = Some W_80084.
Proof. vm_refl. Qed.
Lemma D_80084 : decode_any W_80084 = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_80088 : bv 32 := 0xfbf60b13.
Lemma F_80088 : fetch_word Asan.M.loaded_segments (0x800d8 : word) = Some W_80088.
Proof. vm_refl. Qed.
Lemma D_80088 : decode_any W_80088 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_8008c : bv 32 := 0xfbf00693.
Lemma F_8008c : fetch_word Asan.M.loaded_segments (0x800dc : word) = Some W_8008c.
Proof. vm_refl. Qed.
Lemma D_8008c : decode_any W_8008c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_80090 : bv 32 := 0x2f66f663.
Lemma F_80090 : fetch_word Asan.M.loaded_segments (0x800e0 : word) = Some W_80090.
Proof. vm_refl. Qed.
Lemma D_80090 : decode_any W_80090 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_80094 : bv 32 := 0x000d3697.
Lemma F_80094 : fetch_word Asan.M.loaded_segments (0x800e4 : word) = Some W_80094.
Proof. vm_refl. Qed.
Lemma D_80094 : decode_any W_80094 = Some (Auipc 13 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_80098 : bv 32 := 0x0546b683.
Lemma F_80098 : fetch_word Asan.M.loaded_segments (0x800e8 : word) = Some W_80098.
Proof. vm_refl. Qed.
Lemma D_80098 : decode_any W_80098 = Some (Load SZ8 true 13 13 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_8009c : bv 32 := 0x0006b703.
Lemma F_8009c : fetch_word Asan.M.loaded_segments (0x800ec : word) = Some W_8009c.
Proof. vm_refl. Qed.
Lemma D_8009c : decode_any W_8009c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a0 : bv 32 := 0xfff98993.
Lemma F_800a0 : fetch_word Asan.M.loaded_segments (0x800f0 : word) = Some W_800a0.
Proof. vm_refl. Qed.
Lemma D_800a0 : decode_any W_800a0 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a4 : bv 32 := 0x0035d693.
Lemma F_800a4 : fetch_word Asan.M.loaded_segments (0x800f4 : word) = Some W_800a4.
Proof. vm_refl. Qed.
Lemma D_800a4 : decode_any W_800a4 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a8 : bv 32 := 0x0039d793.
Lemma F_800a8 : fetch_word Asan.M.loaded_segments (0x800f8 : word) = Some W_800a8.
Proof. vm_refl. Qed.
Lemma D_800a8 : decode_any W_800a8 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ac : bv 32 := 0x00d706b3.
Lemma F_800ac : fetch_word Asan.M.loaded_segments (0x800fc : word) = Some W_800ac.
Proof. vm_refl. Qed.
Lemma D_800ac : decode_any W_800ac = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b0 : bv 32 := 0x00f70733.
Lemma F_800b0 : fetch_word Asan.M.loaded_segments (0x80100 : word) = Some W_800b0.
Proof. vm_refl. Qed.
Lemma D_800b0 : decode_any W_800b0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b4 : bv 32 := 0xff86f793.
Lemma F_800b4 : fetch_word Asan.M.loaded_segments (0x80104 : word) = Some W_800b4.
Proof. vm_refl. Qed.
Lemma D_800b4 : decode_any W_800b4 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b8 : bv 32 := 0xff877813.
Lemma F_800b8 : fetch_word Asan.M.loaded_segments (0x80108 : word) = Some W_800b8.
Proof. vm_refl. Qed.
Lemma D_800b8 : decode_any W_800b8 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_800bc : bv 32 := 0x0007b783.
Lemma F_800bc : fetch_word Asan.M.loaded_segments (0x8010c : word) = Some W_800bc.
Proof. vm_refl. Qed.
Lemma D_800bc : decode_any W_800bc = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c0 : bv 32 := 0x00083803.
Lemma F_800c0 : fetch_word Asan.M.loaded_segments (0x80110 : word) = Some W_800c0.
Proof. vm_refl. Qed.
Lemma D_800c0 : decode_any W_800c0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c4 : bv 32 := 0x00f867b3.
Lemma F_800c4 : fetch_word Asan.M.loaded_segments (0x80114 : word) = Some W_800c4.
Proof. vm_refl. Qed.
Lemma D_800c4 : decode_any W_800c4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c8 : bv 32 := 0x2a079e63.
Lemma F_800c8 : fetch_word Asan.M.loaded_segments (0x80118 : word) = Some W_800c8.
Proof. vm_refl. Qed.
Lemma D_800c8 : decode_any W_800c8 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_800cc : bv 32 := 0xfff54693.
Lemma F_800cc : fetch_word Asan.M.loaded_segments (0x8011c : word) = Some W_800cc.
Proof. vm_refl. Qed.
Lemma D_800cc : decode_any W_800cc = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d0 : bv 32 := 0x0cc6ee63.
Lemma F_800d0 : fetch_word Asan.M.loaded_segments (0x80120 : word) = Some W_800d0.
Proof. vm_refl. Qed.
Lemma D_800d0 : decode_any W_800d0 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d4 : bv 32 := 0xfbf00693.
Lemma F_800d4 : fetch_word Asan.M.loaded_segments (0x80124 : word) = Some W_800d4.
Proof. vm_refl. Qed.
Lemma D_800d4 : decode_any W_800d4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d8 : bv 32 := 0x1566fc63.
Lemma F_800d8 : fetch_word Asan.M.loaded_segments (0x80128 : word) = Some W_800d8.
Proof. vm_refl. Qed.
Lemma D_800d8 : decode_any W_800d8 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_800dc : bv 32 := 0x000d3697.
Lemma F_800dc : fetch_word Asan.M.loaded_segments (0x8012c : word) = Some W_800dc.
Proof. vm_refl. Qed.
Lemma D_800dc : decode_any W_800dc = Some (Auipc 13 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e0 : bv 32 := 0x00c6b683.
Lemma F_800e0 : fetch_word Asan.M.loaded_segments (0x80130 : word) = Some W_800e0.
Proof. vm_refl. Qed.
Lemma D_800e0 : decode_any W_800e0 = Some (Load SZ8 true 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e4 : bv 32 := 0x0006b703.
Lemma F_800e4 : fetch_word Asan.M.loaded_segments (0x80134 : word) = Some W_800e4.
Proof. vm_refl. Qed.
Lemma D_800e4 : decode_any W_800e4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e8 : bv 32 := 0xfffa0a13.
Lemma F_800e8 : fetch_word Asan.M.loaded_segments (0x80138 : word) = Some W_800e8.
Proof. vm_refl. Qed.
Lemma D_800e8 : decode_any W_800e8 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ec : bv 32 := 0x00355693.
Lemma F_800ec : fetch_word Asan.M.loaded_segments (0x8013c : word) = Some W_800ec.
Proof. vm_refl. Qed.
Lemma D_800ec : decode_any W_800ec = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f0 : bv 32 := 0x003a5793.
Lemma F_800f0 : fetch_word Asan.M.loaded_segments (0x80140 : word) = Some W_800f0.
Proof. vm_refl. Qed.
Lemma D_800f0 : decode_any W_800f0 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f4 : bv 32 := 0x00d706b3.
Lemma F_800f4 : fetch_word Asan.M.loaded_segments (0x80144 : word) = Some W_800f4.
Proof. vm_refl. Qed.
Lemma D_800f4 : decode_any W_800f4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f8 : bv 32 := 0x00f70733.
Lemma F_800f8 : fetch_word Asan.M.loaded_segments (0x80148 : word) = Some W_800f8.
Proof. vm_refl. Qed.
Lemma D_800f8 : decode_any W_800f8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800fc : bv 32 := 0xff86f793.
Lemma F_800fc : fetch_word Asan.M.loaded_segments (0x8014c : word) = Some W_800fc.
Proof. vm_refl. Qed.
Lemma D_800fc : decode_any W_800fc = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_80100 : bv 32 := 0xff877813.
Lemma F_80100 : fetch_word Asan.M.loaded_segments (0x80150 : word) = Some W_80100.
Proof. vm_refl. Qed.
Lemma D_80100 : decode_any W_80100 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_80104 : bv 32 := 0x0007b783.
Lemma F_80104 : fetch_word Asan.M.loaded_segments (0x80154 : word) = Some W_80104.
Proof. vm_refl. Qed.
Lemma D_80104 : decode_any W_80104 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80108 : bv 32 := 0x00083803.
Lemma F_80108 : fetch_word Asan.M.loaded_segments (0x80158 : word) = Some W_80108.
Proof. vm_refl. Qed.
Lemma D_80108 : decode_any W_80108 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8010c : bv 32 := 0x00f867b3.
Lemma F_8010c : fetch_word Asan.M.loaded_segments (0x8015c : word) = Some W_8010c.
Proof. vm_refl. Qed.
Lemma D_8010c : decode_any W_8010c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80110 : bv 32 := 0x36079a63.
Lemma F_80110 : fetch_word Asan.M.loaded_segments (0x80160 : word) = Some W_80110.
Proof. vm_refl. Qed.
Lemma D_80110 : decode_any W_80110 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_80114 : bv 32 := 0x000d5697.
Lemma F_80114 : fetch_word Asan.M.loaded_segments (0x80164 : word) = Some W_80114.
Proof. vm_refl. Qed.
Lemma D_80114 : decode_any W_80114 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_80118 : bv 32 := 0xff46b683.
Lemma F_80118 : fetch_word Asan.M.loaded_segments (0x80168 : word) = Some W_80118.
Proof. vm_refl. Qed.
Lemma D_80118 : decode_any W_80118 = Some (Load SZ8 true 13 13 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_8011c : bv 32 := 0x000680e7.
Lemma F_8011c : fetch_word Asan.M.loaded_segments (0x8016c : word) = Some W_8011c.
Proof. vm_refl. Qed.
Lemma D_8011c : decode_any W_8011c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80120 : bv 32 := 0x08010113.
Lemma F_80120 : fetch_word Asan.M.loaded_segments (0x80170 : word) = Some W_80120.
Proof. vm_refl. Qed.
Lemma D_80120 : decode_any W_80120 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_80124 : bv 32 := 0x7e813083.
Lemma F_80124 : fetch_word Asan.M.loaded_segments (0x80174 : word) = Some W_80124.
Proof. vm_refl. Qed.
Lemma D_80124 : decode_any W_80124 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80128 : bv 32 := 0x7e013403.
Lemma F_80128 : fetch_word Asan.M.loaded_segments (0x80178 : word) = Some W_80128.
Proof. vm_refl. Qed.
Lemma D_80128 : decode_any W_80128 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8012c : bv 32 := 0x7d813483.
Lemma F_8012c : fetch_word Asan.M.loaded_segments (0x8017c : word) = Some W_8012c.
Proof. vm_refl. Qed.
Lemma D_8012c : decode_any W_8012c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80130 : bv 32 := 0x7d013903.
Lemma F_80130 : fetch_word Asan.M.loaded_segments (0x80180 : word) = Some W_80130.
Proof. vm_refl. Qed.
Lemma D_80130 : decode_any W_80130 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80134 : bv 32 := 0x7c813983.
Lemma F_80134 : fetch_word Asan.M.loaded_segments (0x80184 : word) = Some W_80134.
Proof. vm_refl. Qed.
Lemma D_80134 : decode_any W_80134 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80138 : bv 32 := 0x7c013a03.
Lemma F_80138 : fetch_word Asan.M.loaded_segments (0x80188 : word) = Some W_80138.
Proof. vm_refl. Qed.
Lemma D_80138 : decode_any W_80138 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8013c : bv 32 := 0x7b813a83.
Lemma F_8013c : fetch_word Asan.M.loaded_segments (0x8018c : word) = Some W_8013c.
Proof. vm_refl. Qed.
Lemma D_8013c : decode_any W_8013c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80140 : bv 32 := 0x7b013b03.
Lemma F_80140 : fetch_word Asan.M.loaded_segments (0x80190 : word) = Some W_80140.
Proof. vm_refl. Qed.
Lemma D_80140 : decode_any W_80140 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_80144 : bv 32 := 0x7a813b83.
Lemma F_80144 : fetch_word Asan.M.loaded_segments (0x80194 : word) = Some W_80144.
Proof. vm_refl. Qed.
Lemma D_80144 : decode_any W_80144 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_80148 : bv 32 := 0x7a013c03.
Lemma F_80148 : fetch_word Asan.M.loaded_segments (0x80198 : word) = Some W_80148.
Proof. vm_refl. Qed.
Lemma D_80148 : decode_any W_80148 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_8014c : bv 32 := 0x7f010113.
Lemma F_8014c : fetch_word Asan.M.loaded_segments (0x8019c : word) = Some W_8014c.
Proof. vm_refl. Qed.
Lemma D_8014c : decode_any W_8014c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80150 : bv 32 := 0x00008067.
Lemma F_80150 : fetch_word Asan.M.loaded_segments (0x801a0 : word) = Some W_80150.
Proof. vm_refl. Qed.
Lemma D_80150 : decode_any W_80150 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80230 : bv 32 := 0x28061463.
Lemma F_80230 : fetch_word Asan.M.loaded_segments (0x80280 : word) = Some W_80230.
Proof. vm_refl. Qed.
Lemma D_80230 : decode_any W_80230 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_80234 : bv 32 := 0xee1ff06f.
Lemma F_80234 : fetch_word Asan.M.loaded_segments (0x80284 : word) = Some W_80234.
Proof. vm_refl. Qed.
Lemma D_80234 : decode_any W_80234 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_8037c : bv 32 := 0x02061e63.
Lemma F_8037c : fetch_word Asan.M.loaded_segments (0x803cc : word) = Some W_8037c.
Proof. vm_refl. Qed.
Lemma D_8037c : decode_any W_8037c = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_80380 : bv 32 := 0xd4dff06f.
Lemma F_80380 : fetch_word Asan.M.loaded_segments (0x803d0 : word) = Some W_80380.
Proof. vm_refl. Qed.
Lemma D_80380 : decode_any W_80380 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

Definition W_80384 : bv 32 := 0x00070783.
Lemma F_80384 : fetch_word Asan.M.loaded_segments (0x803d4 : word) = Some W_80384.
Proof. vm_refl. Qed.
Lemma D_80384 : decode_any W_80384 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80388 : bv 32 := 0x0079f813.
Lemma F_80388 : fetch_word Asan.M.loaded_segments (0x803d8 : word) = Some W_80388.
Proof. vm_refl. Qed.
Lemma D_80388 : decode_any W_80388 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8038c : bv 32 := 0x00f038b3.
Lemma F_8038c : fetch_word Asan.M.loaded_segments (0x803dc : word) = Some W_8038c.
Proof. vm_refl. Qed.
Lemma D_8038c : decode_any W_8038c = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80390 : bv 32 := 0x00f827b3.
Lemma F_80390 : fetch_word Asan.M.loaded_segments (0x803e0 : word) = Some W_80390.
Proof. vm_refl. Qed.
Lemma D_80390 : decode_any W_80390 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80394 : bv 32 := 0x0017c793.
Lemma F_80394 : fetch_word Asan.M.loaded_segments (0x803e4 : word) = Some W_80394.
Proof. vm_refl. Qed.
Lemma D_80394 : decode_any W_80394 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80398 : bv 32 := 0x00f8f7b3.
Lemma F_80398 : fetch_word Asan.M.loaded_segments (0x803e8 : word) = Some W_80398.
Proof. vm_refl. Qed.
Lemma D_80398 : decode_any W_80398 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8039c : bv 32 := 0x00e6fa63.
Lemma F_8039c : fetch_word Asan.M.loaded_segments (0x803ec : word) = Some W_8039c.
Proof. vm_refl. Qed.
Lemma D_8039c : decode_any W_8039c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a0 : bv 32 := 0x0006c803.
Lemma F_803a0 : fetch_word Asan.M.loaded_segments (0x803f0 : word) = Some W_803a0.
Proof. vm_refl. Qed.
Lemma D_803a0 : decode_any W_803a0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a4 : bv 32 := 0x00168693.
Lemma F_803a4 : fetch_word Asan.M.loaded_segments (0x803f4 : word) = Some W_803a4.
Proof. vm_refl. Qed.
Lemma D_803a4 : decode_any W_803a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a8 : bv 32 := 0x00f867b3.
Lemma F_803a8 : fetch_word Asan.M.loaded_segments (0x803f8 : word) = Some W_803a8.
Proof. vm_refl. Qed.
Lemma D_803a8 : decode_any W_803a8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_803ac : bv 32 := 0xfee69ae3.
Lemma F_803ac : fetch_word Asan.M.loaded_segments (0x803fc : word) = Some W_803ac.
Proof. vm_refl. Qed.
Lemma D_803ac : decode_any W_803ac = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b0 : bv 32 := 0x0ff7f693.
Lemma F_803b0 : fetch_word Asan.M.loaded_segments (0x80400 : word) = Some W_803b0.
Proof. vm_refl. Qed.
Lemma D_803b0 : decode_any W_803b0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b4 : bv 32 := 0xd0068ce3.
Lemma F_803b4 : fetch_word Asan.M.loaded_segments (0x80404 : word) = Some W_803b4.
Proof. vm_refl. Qed.
Lemma D_803b4 : decode_any W_803b4 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b8 : bv 32 := 0x00050b93.
Lemma F_803b8 : fetch_word Asan.M.loaded_segments (0x80408 : word) = Some W_803b8.
Proof. vm_refl. Qed.
Lemma D_803b8 : decode_any W_803b8 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803bc : bv 32 := 0x00058513.
Lemma F_803bc : fetch_word Asan.M.loaded_segments (0x8040c : word) = Some W_803bc.
Proof. vm_refl. Qed.
Lemma D_803bc : decode_any W_803bc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c0 : bv 32 := 0x00058c13.
Lemma F_803c0 : fetch_word Asan.M.loaded_segments (0x80410 : word) = Some W_803c0.
Proof. vm_refl. Qed.
Lemma D_803c0 : decode_any W_803c0 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c4 : bv 32 := 0x00060593.
Lemma F_803c4 : fetch_word Asan.M.loaded_segments (0x80414 : word) = Some W_803c4.
Proof. vm_refl. Qed.
Lemma D_803c4 : decode_any W_803c4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c8 : bv 32 := 0x00060493.
Lemma F_803c8 : fetch_word Asan.M.loaded_segments (0x80418 : word) = Some W_803c8.
Proof. vm_refl. Qed.
Lemma D_803c8 : decode_any W_803c8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803cc : bv 32 := 0x284020ef.
Lemma F_803cc : fetch_word Asan.M.loaded_segments (0x8041c : word) = Some W_803cc.
Proof. vm_refl. Qed.
Lemma D_803cc : decode_any W_803cc = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

Definition W_803d0 : bv 32 := 0x000c0593.
Lemma F_803d0 : fetch_word Asan.M.loaded_segments (0x80420 : word) = Some W_803d0.
Proof. vm_refl. Qed.
Lemma D_803d0 : decode_any W_803d0 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803d4 : bv 32 := 0x00048613.
Lemma F_803d4 : fetch_word Asan.M.loaded_segments (0x80424 : word) = Some W_803d4.
Proof. vm_refl. Qed.
Lemma D_803d4 : decode_any W_803d4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803d8 : bv 32 := 0x00050913.
Lemma F_803d8 : fetch_word Asan.M.loaded_segments (0x80428 : word) = Some W_803d8.
Proof. vm_refl. Qed.
Lemma D_803d8 : decode_any W_803d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803dc : bv 32 := 0x000b8513.
Lemma F_803dc : fetch_word Asan.M.loaded_segments (0x8042c : word) = Some W_803dc.
Proof. vm_refl. Qed.
Lemma D_803dc : decode_any W_803dc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803e0 : bv 32 := 0xce0906e3.
Lemma F_803e0 : fetch_word Asan.M.loaded_segments (0x80430 : word) = Some W_803e0.
Proof. vm_refl. Qed.
Lemma D_803e0 : decode_any W_803e0 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

Definition W_80484 : bv 32 := 0x00070783.
Lemma F_80484 : fetch_word Asan.M.loaded_segments (0x804d4 : word) = Some W_80484.
Proof. vm_refl. Qed.
Lemma D_80484 : decode_any W_80484 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80488 : bv 32 := 0x007a7813.
Lemma F_80488 : fetch_word Asan.M.loaded_segments (0x804d8 : word) = Some W_80488.
Proof. vm_refl. Qed.
Lemma D_80488 : decode_any W_80488 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8048c : bv 32 := 0x00f038b3.
Lemma F_8048c : fetch_word Asan.M.loaded_segments (0x804dc : word) = Some W_8048c.
Proof. vm_refl. Qed.
Lemma D_8048c : decode_any W_8048c = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80490 : bv 32 := 0x00f827b3.
Lemma F_80490 : fetch_word Asan.M.loaded_segments (0x804e0 : word) = Some W_80490.
Proof. vm_refl. Qed.
Lemma D_80490 : decode_any W_80490 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80494 : bv 32 := 0x0017c793.
Lemma F_80494 : fetch_word Asan.M.loaded_segments (0x804e4 : word) = Some W_80494.
Proof. vm_refl. Qed.
Lemma D_80494 : decode_any W_80494 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80498 : bv 32 := 0x00f8f7b3.
Lemma F_80498 : fetch_word Asan.M.loaded_segments (0x804e8 : word) = Some W_80498.
Proof. vm_refl. Qed.
Lemma D_80498 : decode_any W_80498 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8049c : bv 32 := 0x00e6fa63.
Lemma F_8049c : fetch_word Asan.M.loaded_segments (0x804ec : word) = Some W_8049c.
Proof. vm_refl. Qed.
Lemma D_8049c : decode_any W_8049c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a0 : bv 32 := 0x0006c803.
Lemma F_804a0 : fetch_word Asan.M.loaded_segments (0x804f0 : word) = Some W_804a0.
Proof. vm_refl. Qed.
Lemma D_804a0 : decode_any W_804a0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a4 : bv 32 := 0x00168693.
Lemma F_804a4 : fetch_word Asan.M.loaded_segments (0x804f4 : word) = Some W_804a4.
Proof. vm_refl. Qed.
Lemma D_804a4 : decode_any W_804a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a8 : bv 32 := 0x00f867b3.
Lemma F_804a8 : fetch_word Asan.M.loaded_segments (0x804f8 : word) = Some W_804a8.
Proof. vm_refl. Qed.
Lemma D_804a8 : decode_any W_804a8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_804ac : bv 32 := 0xfee69ae3.
Lemma F_804ac : fetch_word Asan.M.loaded_segments (0x804fc : word) = Some W_804ac.
Proof. vm_refl. Qed.
Lemma D_804ac : decode_any W_804ac = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b0 : bv 32 := 0x0ff7f693.
Lemma F_804b0 : fetch_word Asan.M.loaded_segments (0x80500 : word) = Some W_804b0.
Proof. vm_refl. Qed.
Lemma D_804b0 : decode_any W_804b0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b4 : bv 32 := 0xc60680e3.
Lemma F_804b4 : fetch_word Asan.M.loaded_segments (0x80504 : word) = Some W_804b4.
Proof. vm_refl. Qed.
Lemma D_804b4 : decode_any W_804b4 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b8 : bv 32 := 0x00050493.
Lemma F_804b8 : fetch_word Asan.M.loaded_segments (0x80508 : word) = Some W_804b8.
Proof. vm_refl. Qed.
Lemma D_804b8 : decode_any W_804b8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804bc : bv 32 := 0x00058b13.
Lemma F_804bc : fetch_word Asan.M.loaded_segments (0x8050c : word) = Some W_804bc.
Proof. vm_refl. Qed.
Lemma D_804bc : decode_any W_804bc = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c0 : bv 32 := 0x00060593.
Lemma F_804c0 : fetch_word Asan.M.loaded_segments (0x80510 : word) = Some W_804c0.
Proof. vm_refl. Qed.
Lemma D_804c0 : decode_any W_804c0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c4 : bv 32 := 0x00060913.
Lemma F_804c4 : fetch_word Asan.M.loaded_segments (0x80514 : word) = Some W_804c4.
Proof. vm_refl. Qed.
Lemma D_804c4 : decode_any W_804c4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c8 : bv 32 := 0x188020ef.
Lemma F_804c8 : fetch_word Asan.M.loaded_segments (0x80518 : word) = Some W_804c8.
Proof. vm_refl. Qed.
Lemma D_804c8 : decode_any W_804c8 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

Definition W_804cc : bv 32 := 0x000b0593.
Lemma F_804cc : fetch_word Asan.M.loaded_segments (0x8051c : word) = Some W_804cc.
Proof. vm_refl. Qed.
Lemma D_804cc : decode_any W_804cc = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d0 : bv 32 := 0x00090613.
Lemma F_804d0 : fetch_word Asan.M.loaded_segments (0x80520 : word) = Some W_804d0.
Proof. vm_refl. Qed.
Lemma D_804d0 : decode_any W_804d0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d4 : bv 32 := 0x00050993.
Lemma F_804d4 : fetch_word Asan.M.loaded_segments (0x80524 : word) = Some W_804d4.
Proof. vm_refl. Qed.
Lemma D_804d4 : decode_any W_804d4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d8 : bv 32 := 0x00048513.
Lemma F_804d8 : fetch_word Asan.M.loaded_segments (0x80528 : word) = Some W_804d8.
Proof. vm_refl. Qed.
Lemma D_804d8 : decode_any W_804d8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804dc : bv 32 := 0xc2098ce3.
Lemma F_804dc : fetch_word Asan.M.loaded_segments (0x8052c : word) = Some W_804dc.
Proof. vm_refl. Qed.
Lemma D_804dc : decode_any W_804dc = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b0 : bv 32 := 0xfe010113.
Lemma F_806b0 : fetch_word Asan.M.loaded_segments (0x80700 : word) = Some W_806b0.
Proof. vm_refl. Qed.
Lemma D_806b0 : decode_any W_806b0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b4 : bv 32 := 0x00113c23.
Lemma F_806b4 : fetch_word Asan.M.loaded_segments (0x80704 : word) = Some W_806b4.
Proof. vm_refl. Qed.
Lemma D_806b4 : decode_any W_806b4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b8 : bv 32 := 0x00813823.
Lemma F_806b8 : fetch_word Asan.M.loaded_segments (0x80708 : word) = Some W_806b8.
Proof. vm_refl. Qed.
Lemma D_806b8 : decode_any W_806b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_806bc : bv 32 := 0x00913423.
Lemma F_806bc : fetch_word Asan.M.loaded_segments (0x8070c : word) = Some W_806bc.
Proof. vm_refl. Qed.
Lemma D_806bc : decode_any W_806bc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c0 : bv 32 := 0x01213023.
Lemma F_806c0 : fetch_word Asan.M.loaded_segments (0x80710 : word) = Some W_806c0.
Proof. vm_refl. Qed.
Lemma D_806c0 : decode_any W_806c0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c4 : bv 32 := 0x00058413.
Lemma F_806c4 : fetch_word Asan.M.loaded_segments (0x80714 : word) = Some W_806c4.
Proof. vm_refl. Qed.
Lemma D_806c4 : decode_any W_806c4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c8 : bv 32 := 0x00050493.
Lemma F_806c8 : fetch_word Asan.M.loaded_segments (0x80718 : word) = Some W_806c8.
Proof. vm_refl. Qed.
Lemma D_806c8 : decode_any W_806c8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806cc : bv 32 := 0x030000ef.
Lemma F_806cc : fetch_word Asan.M.loaded_segments (0x8071c : word) = Some W_806cc.
Proof. vm_refl. Qed.
Lemma D_806cc : decode_any W_806cc = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_806d0 : bv 32 := 0x00050913.
Lemma F_806d0 : fetch_word Asan.M.loaded_segments (0x80720 : word) = Some W_806d0.
Proof. vm_refl. Qed.
Lemma D_806d0 : decode_any W_806d0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806d4 : bv 32 := 0x00940533.
Lemma F_806d4 : fetch_word Asan.M.loaded_segments (0x80724 : word) = Some W_806d4.
Proof. vm_refl. Qed.
Lemma D_806d4 : decode_any W_806d4 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_806d8 : bv 32 := 0x024000ef.
Lemma F_806d8 : fetch_word Asan.M.loaded_segments (0x80728 : word) = Some W_806d8.
Proof. vm_refl. Qed.
Lemma D_806d8 : decode_any W_806d8 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_806dc : bv 32 := 0x00050593.
Lemma F_806dc : fetch_word Asan.M.loaded_segments (0x8072c : word) = Some W_806dc.
Proof. vm_refl. Qed.
Lemma D_806dc : decode_any W_806dc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806e0 : bv 32 := 0x00090513.
Lemma F_806e0 : fetch_word Asan.M.loaded_segments (0x80730 : word) = Some W_806e0.
Proof. vm_refl. Qed.
Lemma D_806e0 : decode_any W_806e0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806e4 : bv 32 := 0x01813083.
Lemma F_806e4 : fetch_word Asan.M.loaded_segments (0x80734 : word) = Some W_806e4.
Proof. vm_refl. Qed.
Lemma D_806e4 : decode_any W_806e4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_806e8 : bv 32 := 0x01013403.
Lemma F_806e8 : fetch_word Asan.M.loaded_segments (0x80738 : word) = Some W_806e8.
Proof. vm_refl. Qed.
Lemma D_806e8 : decode_any W_806e8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_806ec : bv 32 := 0x00813483.
Lemma F_806ec : fetch_word Asan.M.loaded_segments (0x8073c : word) = Some W_806ec.
Proof. vm_refl. Qed.
Lemma D_806ec : decode_any W_806ec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f0 : bv 32 := 0x00013903.
Lemma F_806f0 : fetch_word Asan.M.loaded_segments (0x80740 : word) = Some W_806f0.
Proof. vm_refl. Qed.
Lemma D_806f0 : decode_any W_806f0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f4 : bv 32 := 0x02010113.
Lemma F_806f4 : fetch_word Asan.M.loaded_segments (0x80744 : word) = Some W_806f4.
Proof. vm_refl. Qed.
Lemma D_806f4 : decode_any W_806f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f8 : bv 32 := 0x3151b06f.
Lemma F_806f8 : fetch_word Asan.M.loaded_segments (0x80748 : word) = Some W_806f8.
Proof. vm_refl. Qed.
Lemma D_806f8 : decode_any W_806f8 = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

Definition W_806fc : bv 32 := 0x000d3597.
Lemma F_806fc : fetch_word Asan.M.loaded_segments (0x8074c : word) = Some W_806fc.
Proof. vm_refl. Qed.
Lemma D_806fc : decode_any W_806fc = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_80700 : bv 32 := 0x9ec5b583.
Lemma F_80700 : fetch_word Asan.M.loaded_segments (0x80750 : word) = Some W_80700.
Proof. vm_refl. Qed.
Lemma D_80700 : decode_any W_80700 = Some (Load SZ8 true 11 11 2540, 4%Z).
Proof. vm_refl. Qed.

Definition W_80704 : bv 32 := 0x0005b583.
Lemma F_80704 : fetch_word Asan.M.loaded_segments (0x80754 : word) = Some W_80704.
Proof. vm_refl. Qed.
Lemma D_80704 : decode_any W_80704 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80708 : bv 32 := 0xfff58613.
Lemma F_80708 : fetch_word Asan.M.loaded_segments (0x80758 : word) = Some W_80708.
Proof. vm_refl. Qed.
Lemma D_80708 : decode_any W_80708 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8070c : bv 32 := 0x00c5b6b3.
Lemma F_8070c : fetch_word Asan.M.loaded_segments (0x8075c : word) = Some W_8070c.
Proof. vm_refl. Qed.
Lemma D_8070c : decode_any W_8070c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80710 : bv 32 := 0xfff68693.
Lemma F_80710 : fetch_word Asan.M.loaded_segments (0x80760 : word) = Some W_80710.
Proof. vm_refl. Qed.
Lemma D_80710 : decode_any W_80710 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80714 : bv 32 := 0x00c6f6b3.
Lemma F_80714 : fetch_word Asan.M.loaded_segments (0x80764 : word) = Some W_80714.
Proof. vm_refl. Qed.
Lemma D_80714 : decode_any W_80714 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80718 : bv 32 := 0x04a6f263.
Lemma F_80718 : fetch_word Asan.M.loaded_segments (0x80768 : word) = Some W_80718.
Proof. vm_refl. Qed.
Lemma D_80718 : decode_any W_80718 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_8071c : bv 32 := 0x000d3697.
Lemma F_8071c : fetch_word Asan.M.loaded_segments (0x8076c : word) = Some W_8071c.
Proof. vm_refl. Qed.
Lemma D_8071c : decode_any W_8071c = Some (Auipc 13 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_80720 : bv 32 := 0x9d46b683.
Lemma F_80720 : fetch_word Asan.M.loaded_segments (0x80770 : word) = Some W_80720.
Proof. vm_refl. Qed.
Lemma D_80720 : decode_any W_80720 = Some (Load SZ8 true 13 13 2516, 4%Z).
Proof. vm_refl. Qed.

Definition W_80724 : bv 32 := 0x000d3717.
Lemma F_80724 : fetch_word Asan.M.loaded_segments (0x80774 : word) = Some W_80724.
Proof. vm_refl. Qed.
Lemma D_80724 : decode_any W_80724 = Some (Auipc 14 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_80728 : bv 32 := 0x9d473703.
Lemma F_80728 : fetch_word Asan.M.loaded_segments (0x80778 : word) = Some W_80728.
Proof. vm_refl. Qed.
Lemma D_80728 : decode_any W_80728 = Some (Load SZ8 true 14 14 2516, 4%Z).
Proof. vm_refl. Qed.

Definition W_8072c : bv 32 := 0x0006b803.
Lemma F_8072c : fetch_word Asan.M.loaded_segments (0x8077c : word) = Some W_8072c.
Proof. vm_refl. Qed.
Lemma D_8072c : decode_any W_8072c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80730 : bv 32 := 0x00073683.
Lemma F_80730 : fetch_word Asan.M.loaded_segments (0x80780 : word) = Some W_80730.
Proof. vm_refl. Qed.
Lemma D_80730 : decode_any W_80730 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80734 : bv 32 := 0xfff80793.
Lemma F_80734 : fetch_word Asan.M.loaded_segments (0x80784 : word) = Some W_80734.
Proof. vm_refl. Qed.
Lemma D_80734 : decode_any W_80734 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80738 : bv 32 := 0x00a7f463.
Lemma F_80738 : fetch_word Asan.M.loaded_segments (0x80788 : word) = Some W_80738.
Proof. vm_refl. Qed.
Lemma D_80738 : decode_any W_80738 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80740 : bv 32 := 0x000d3717.
Lemma F_80740 : fetch_word Asan.M.loaded_segments (0x80790 : word) = Some W_80740.
Proof. vm_refl. Qed.
Lemma D_80740 : decode_any W_80740 = Some (Auipc 14 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_80744 : bv 32 := 0x9c073703.
Lemma F_80744 : fetch_word Asan.M.loaded_segments (0x80794 : word) = Some W_80744.
Proof. vm_refl. Qed.
Lemma D_80744 : decode_any W_80744 = Some (Load SZ8 true 14 14 2496, 4%Z).
Proof. vm_refl. Qed.

Definition W_80748 : bv 32 := 0x00073283.
Lemma F_80748 : fetch_word Asan.M.loaded_segments (0x80798 : word) = Some W_80748.
Proof. vm_refl. Qed.
Lemma D_80748 : decode_any W_80748 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8074c : bv 32 := 0x0032d713.
Lemma F_8074c : fetch_word Asan.M.loaded_segments (0x8079c : word) = Some W_8074c.
Proof. vm_refl. Qed.
Lemma D_8074c : decode_any W_8074c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80750 : bv 32 := 0x00b708b3.
Lemma F_80750 : fetch_word Asan.M.loaded_segments (0x807a0 : word) = Some W_80750.
Proof. vm_refl. Qed.
Lemma D_80750 : decode_any W_80750 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80754 : bv 32 := 0x00a2ea63.
Lemma F_80754 : fetch_word Asan.M.loaded_segments (0x807a4 : word) = Some W_80754.
Proof. vm_refl. Qed.
Lemma D_80754 : decode_any W_80754 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80758 : bv 32 := 0x00a8f863.
Lemma F_80758 : fetch_word Asan.M.loaded_segments (0x807a8 : word) = Some W_80758.
Proof. vm_refl. Qed.
Lemma D_80758 : decode_any W_80758 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8075c : bv 32 := 0x00355513.
Lemma F_8075c : fetch_word Asan.M.loaded_segments (0x807ac : word) = Some W_8075c.
Proof. vm_refl. Qed.
Lemma D_8075c : decode_any W_8075c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80760 : bv 32 := 0x00a58533.
Lemma F_80760 : fetch_word Asan.M.loaded_segments (0x807b0 : word) = Some W_80760.
Proof. vm_refl. Qed.
Lemma D_80760 : decode_any W_80760 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80764 : bv 32 := 0x00008067.
Lemma F_80764 : fetch_word Asan.M.loaded_segments (0x807b4 : word) = Some W_80764.
Proof. vm_refl. Qed.
Lemma D_80764 : decode_any W_80764 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a4 : bv 32 := 0x0100006f.
Lemma F_809a4 : fetch_word Asan.M.loaded_segments (0x809f4 : word) = Some W_809a4.
Proof. vm_refl. Qed.
Lemma D_809a4 : decode_any W_809a4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a8 : bv 32 := 0x1dc0006f.
Lemma F_809a8 : fetch_word Asan.M.loaded_segments (0x809f8 : word) = Some W_809a8.
Proof. vm_refl. Qed.
Lemma D_809a8 : decode_any W_809a8 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b0 : bv 32 := 0x7400006f.
Lemma F_809b0 : fetch_word Asan.M.loaded_segments (0x80a00 : word) = Some W_809b0.
Proof. vm_refl. Qed.
Lemma D_809b0 : decode_any W_809b0 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b4 : bv 32 := 0x81010113.
Lemma F_809b4 : fetch_word Asan.M.loaded_segments (0x80a04 : word) = Some W_809b4.
Proof. vm_refl. Qed.
Lemma D_809b4 : decode_any W_809b4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b8 : bv 32 := 0x7e113423.
Lemma F_809b8 : fetch_word Asan.M.loaded_segments (0x80a08 : word) = Some W_809b8.
Proof. vm_refl. Qed.
Lemma D_809b8 : decode_any W_809b8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_809bc : bv 32 := 0x7e813023.
Lemma F_809bc : fetch_word Asan.M.loaded_segments (0x80a0c : word) = Some W_809bc.
Proof. vm_refl. Qed.
Lemma D_809bc : decode_any W_809bc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c0 : bv 32 := 0x7c913c23.
Lemma F_809c0 : fetch_word Asan.M.loaded_segments (0x80a10 : word) = Some W_809c0.
Proof. vm_refl. Qed.
Lemma D_809c0 : decode_any W_809c0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c4 : bv 32 := 0x7d213823.
Lemma F_809c4 : fetch_word Asan.M.loaded_segments (0x80a14 : word) = Some W_809c4.
Proof. vm_refl. Qed.
Lemma D_809c4 : decode_any W_809c4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c8 : bv 32 := 0x7d313423.
Lemma F_809c8 : fetch_word Asan.M.loaded_segments (0x80a18 : word) = Some W_809c8.
Proof. vm_refl. Qed.
Lemma D_809c8 : decode_any W_809c8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_809cc : bv 32 := 0x7d413023.
Lemma F_809cc : fetch_word Asan.M.loaded_segments (0x80a1c : word) = Some W_809cc.
Proof. vm_refl. Qed.
Lemma D_809cc : decode_any W_809cc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d0 : bv 32 := 0x7b513c23.
Lemma F_809d0 : fetch_word Asan.M.loaded_segments (0x80a20 : word) = Some W_809d0.
Proof. vm_refl. Qed.
Lemma D_809d0 : decode_any W_809d0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d4 : bv 32 := 0x7f010413.
Lemma F_809d4 : fetch_word Asan.M.loaded_segments (0x80a24 : word) = Some W_809d4.
Proof. vm_refl. Qed.
Lemma D_809d4 : decode_any W_809d4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d8 : bv 32 := 0xfa010113.
Lemma F_809d8 : fetch_word Asan.M.loaded_segments (0x80a28 : word) = Some W_809d8.
Proof. vm_refl. Qed.
Lemma D_809d8 : decode_any W_809d8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_809dc : bv 32 := 0x00008913.
Lemma F_809dc : fetch_word Asan.M.loaded_segments (0x80a2c : word) = Some W_809dc.
Proof. vm_refl. Qed.
Lemma D_809dc : decode_any W_809dc = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e0 : bv 32 := 0x00050493.
Lemma F_809e0 : fetch_word Asan.M.loaded_segments (0x80a30 : word) = Some W_809e0.
Proof. vm_refl. Qed.
Lemma D_809e0 : decode_any W_809e0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e4 : bv 32 := 0x10c0c0ef.
Lemma F_809e4 : fetch_word Asan.M.loaded_segments (0x80a34 : word) = Some W_809e4.
Proof. vm_refl. Qed.
Lemma D_809e4 : decode_any W_809e4 = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e8 : bv 32 := 0x02f4d593.
Lemma F_809e8 : fetch_word Asan.M.loaded_segments (0x80a38 : word) = Some W_809e8.
Proof. vm_refl. Qed.
Lemma D_809e8 : decode_any W_809e8 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_809ec : bv 32 := 0x0a059063.
Lemma F_809ec : fetch_word Asan.M.loaded_segments (0x80a3c : word) = Some W_809ec.
Proof. vm_refl. Qed.
Lemma D_809ec : decode_any W_809ec = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f0 : bv 32 := 0x0204d593.
Lemma F_809f0 : fetch_word Asan.M.loaded_segments (0x80a40 : word) = Some W_809f0.
Proof. vm_refl. Qed.
Lemma D_809f0 : decode_any W_809f0 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f4 : bv 32 := 0x00359613.
Lemma F_809f4 : fetch_word Asan.M.loaded_segments (0x80a44 : word) = Some W_809f4.
Proof. vm_refl. Qed.
Lemma D_809f4 : decode_any W_809f4 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f8 : bv 32 := 0x00c50633.
Lemma F_809f8 : fetch_word Asan.M.loaded_segments (0x80a48 : word) = Some W_809f8.
Proof. vm_refl. Qed.
Lemma D_809f8 : decode_any W_809f8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_809fc : bv 32 := 0x00863683.
Lemma F_809fc : fetch_word Asan.M.loaded_segments (0x80a4c : word) = Some W_809fc.
Proof. vm_refl. Qed.
Lemma D_809fc : decode_any W_809fc = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a00 : bv 32 := 0x0230000f.
Lemma F_80a00 : fetch_word Asan.M.loaded_segments (0x80a50 : word) = Some W_80a00.
Proof. vm_refl. Qed.
Lemma D_80a00 : decode_any W_80a00 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a04 : bv 32 := 0x08068463.
Lemma F_80a04 : fetch_word Asan.M.loaded_segments (0x80a54 : word) = Some W_80a04.
Proof. vm_refl. Qed.
Lemma D_80a04 : decode_any W_80a04 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a8c : bv 32 := 0x80040a13.
Lemma F_80a8c : fetch_word Asan.M.loaded_segments (0x80adc : word) = Some W_80a8c.
Proof. vm_refl. Qed.
Lemma D_80a8c : decode_any W_80a8c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a90 : bv 32 := 0xfb0a0a13.
Lemma F_80a90 : fetch_word Asan.M.loaded_segments (0x80ae0 : word) = Some W_80a90.
Proof. vm_refl. Qed.
Lemma D_80a90 : decode_any W_80a90 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a94 : bv 32 := 0x80040513.
Lemma F_80a94 : fetch_word Asan.M.loaded_segments (0x80ae4 : word) = Some W_80a94.
Proof. vm_refl. Qed.
Lemma D_80a94 : decode_any W_80a94 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a98 : bv 32 := 0xfc050513.
Lemma F_80a98 : fetch_word Asan.M.loaded_segments (0x80ae8 : word) = Some W_80a98.
Proof. vm_refl. Qed.
Lemma D_80a98 : decode_any W_80a98 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a9c : bv 32 := 0x7ffa0a93.
Lemma F_80a9c : fetch_word Asan.M.loaded_segments (0x80aec : word) = Some W_80a9c.
Proof. vm_refl. Qed.
Lemma D_80a9c : decode_any W_80a9c = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa0 : bv 32 := 0x000ab4a3.
Lemma F_80aa0 : fetch_word Asan.M.loaded_segments (0x80af0 : word) = Some W_80aa0.
Proof. vm_refl. Qed.
Lemma D_80aa0 : decode_any W_80aa0 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa4 : bv 32 := 0x00aa3023.
Lemma F_80aa4 : fetch_word Asan.M.loaded_segments (0x80af4 : word) = Some W_80aa4.
Proof. vm_refl. Qed.
Lemma D_80aa4 : decode_any W_80aa4 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa8 : bv 32 := 0x000a3423.
Lemma F_80aa8 : fetch_word Asan.M.loaded_segments (0x80af8 : word) = Some W_80aa8.
Proof. vm_refl. Qed.
Lemma D_80aa8 : decode_any W_80aa8 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aac : bv 32 := 0x550080ef.
Lemma F_80aac : fetch_word Asan.M.loaded_segments (0x80afc : word) = Some W_80aac.
Proof. vm_refl. Qed.
Lemma D_80aac : decode_any W_80aac = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab0 : bv 32 := 0x00200593.
Lemma F_80ab0 : fetch_word Asan.M.loaded_segments (0x80b00 : word) = Some W_80ab0.
Proof. vm_refl. Qed.
Lemma D_80ab0 : decode_any W_80ab0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab4 : bv 32 := 0x02a5ea63.
Lemma F_80ab4 : fetch_word Asan.M.loaded_segments (0x80b04 : word) = Some W_80ab4.
Proof. vm_refl. Qed.
Lemma D_80ab4 : decode_any W_80ab4 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae8 : bv 32 := 0x7f1200ef.
Lemma F_80ae8 : fetch_word Asan.M.loaded_segments (0x80b38 : word) = Some W_80ae8.
Proof. vm_refl. Qed.
Lemma D_80ae8 : decode_any W_80ae8 = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aec : bv 32 := 0x000d2597.
Lemma F_80aec : fetch_word Asan.M.loaded_segments (0x80b3c : word) = Some W_80aec.
Proof. vm_refl. Qed.
Lemma D_80aec : decode_any W_80aec = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af0 : bv 32 := 0x5ec5b583.
Lemma F_80af0 : fetch_word Asan.M.loaded_segments (0x80b40 : word) = Some W_80af0.
Proof. vm_refl. Qed.
Lemma D_80af0 : decode_any W_80af0 = Some (Load SZ8 true 11 11 1516, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af4 : bv 32 := 0x0225c983.
Lemma F_80af4 : fetch_word Asan.M.loaded_segments (0x80b44 : word) = Some W_80af4.
Proof. vm_refl. Qed.
Lemma D_80af4 : decode_any W_80af4 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af8 : bv 32 := 0x00050913.
Lemma F_80af8 : fetch_word Asan.M.loaded_segments (0x80b48 : word) = Some W_80af8.
Proof. vm_refl. Qed.
Lemma D_80af8 : decode_any W_80af8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80afc : bv 32 := 0x500080ef.
Lemma F_80afc : fetch_word Asan.M.loaded_segments (0x80b4c : word) = Some W_80afc.
Proof. vm_refl. Qed.
Lemma D_80afc : decode_any W_80afc = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b00 : bv 32 := 0x00050793.
Lemma F_80b00 : fetch_word Asan.M.loaded_segments (0x80b50 : word) = Some W_80b00.
Proof. vm_refl. Qed.
Lemma D_80b00 : decode_any W_80b00 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b04 : bv 32 := 0x00153513.
Lemma F_80b04 : fetch_word Asan.M.loaded_segments (0x80b54 : word) = Some W_80b04.
Proof. vm_refl. Qed.
Lemma D_80b04 : decode_any W_80b04 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b08 : bv 32 := 0xfff50513.
Lemma F_80b08 : fetch_word Asan.M.loaded_segments (0x80b58 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b0c : bv 32 := 0x008575b3.
Lemma F_80b0c : fetch_word Asan.M.loaded_segments (0x80b5c : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b10 : bv 32 := 0x00100513.
Lemma F_80b10 : fetch_word Asan.M.loaded_segments (0x80b60 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b14 : bv 32 := 0x00bab4a3.
Lemma F_80b14 : fetch_word Asan.M.loaded_segments (0x80b64 : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b18 : bv 32 := 0x00f56a63.
Lemma F_80b18 : fetch_word Asan.M.loaded_segments (0x80b68 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b2c : bv 32 := 0x80040513.
Lemma F_80b2c : fetch_word Asan.M.loaded_segments (0x80b7c : word) = Some W_80b2c.
Proof. vm_refl. Qed.
Lemma D_80b2c : decode_any W_80b2c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b30 : bv 32 := 0xfb050513.
Lemma F_80b30 : fetch_word Asan.M.loaded_segments (0x80b80 : word) = Some W_80b30.
Proof. vm_refl. Qed.
Lemma D_80b30 : decode_any W_80b30 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b34 : bv 32 := 0x00090593.
Lemma F_80b34 : fetch_word Asan.M.loaded_segments (0x80b84 : word) = Some W_80b34.
Proof. vm_refl. Qed.
Lemma D_80b34 : decode_any W_80b34 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b38 : bv 32 := 0x00040613.
Lemma F_80b38 : fetch_word Asan.M.loaded_segments (0x80b88 : word) = Some W_80b38.
Proof. vm_refl. Qed.
Lemma D_80b38 : decode_any W_80b38 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b3c : bv 32 := 0x00000693.
Lemma F_80b3c : fetch_word Asan.M.loaded_segments (0x80b8c : word) = Some W_80b3c.
Proof. vm_refl. Qed.
Lemma D_80b3c : decode_any W_80b3c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b40 : bv 32 := 0x00098713.
Lemma F_80b40 : fetch_word Asan.M.loaded_segments (0x80b90 : word) = Some W_80b40.
Proof. vm_refl. Qed.
Lemma D_80b40 : decode_any W_80b40 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b44 : bv 32 := 0x4c8080ef.
Lemma F_80b44 : fetch_word Asan.M.loaded_segments (0x80b94 : word) = Some W_80b44.
Proof. vm_refl. Qed.
Lemma D_80b44 : decode_any W_80b44 = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b48 : bv 32 := 0x80040593.
Lemma F_80b48 : fetch_word Asan.M.loaded_segments (0x80b98 : word) = Some W_80b48.
Proof. vm_refl. Qed.
Lemma D_80b48 : decode_any W_80b48 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b4c : bv 32 := 0xfb058593.
Lemma F_80b4c : fetch_word Asan.M.loaded_segments (0x80b9c : word) = Some W_80b4c.
Proof. vm_refl. Qed.
Lemma D_80b4c : decode_any W_80b4c = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b50 : bv 32 := 0x00100613.
Lemma F_80b50 : fetch_word Asan.M.loaded_segments (0x80ba0 : word) = Some W_80b50.
Proof. vm_refl. Qed.
Lemma D_80b50 : decode_any W_80b50 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b54 : bv 32 := 0x00048513.
Lemma F_80b54 : fetch_word Asan.M.loaded_segments (0x80ba4 : word) = Some W_80b54.
Proof. vm_refl. Qed.
Lemma D_80b54 : decode_any W_80b54 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b58 : bv 32 := 0xd78d80ef.
Lemma F_80b58 : fetch_word Asan.M.loaded_segments (0x80ba8 : word) = Some W_80b58.
Proof. vm_refl. Qed.
Lemma D_80b58 : decode_any W_80b58 = Some (Jal 1 1934712, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b5c : bv 32 := 0x06010113.
Lemma F_80b5c : fetch_word Asan.M.loaded_segments (0x80bac : word) = Some W_80b5c.
Proof. vm_refl. Qed.
Lemma D_80b5c : decode_any W_80b5c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b60 : bv 32 := 0x7e813083.
Lemma F_80b60 : fetch_word Asan.M.loaded_segments (0x80bb0 : word) = Some W_80b60.
Proof. vm_refl. Qed.
Lemma D_80b60 : decode_any W_80b60 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b64 : bv 32 := 0x7e013403.
Lemma F_80b64 : fetch_word Asan.M.loaded_segments (0x80bb4 : word) = Some W_80b64.
Proof. vm_refl. Qed.
Lemma D_80b64 : decode_any W_80b64 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b68 : bv 32 := 0x7d813483.
Lemma F_80b68 : fetch_word Asan.M.loaded_segments (0x80bb8 : word) = Some W_80b68.
Proof. vm_refl. Qed.
Lemma D_80b68 : decode_any W_80b68 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b6c : bv 32 := 0x7d013903.
Lemma F_80b6c : fetch_word Asan.M.loaded_segments (0x80bbc : word) = Some W_80b6c.
Proof. vm_refl. Qed.
Lemma D_80b6c : decode_any W_80b6c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b70 : bv 32 := 0x7c813983.
Lemma F_80b70 : fetch_word Asan.M.loaded_segments (0x80bc0 : word) = Some W_80b70.
Proof. vm_refl. Qed.
Lemma D_80b70 : decode_any W_80b70 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b74 : bv 32 := 0x7c013a03.
Lemma F_80b74 : fetch_word Asan.M.loaded_segments (0x80bc4 : word) = Some W_80b74.
Proof. vm_refl. Qed.
Lemma D_80b74 : decode_any W_80b74 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b78 : bv 32 := 0x7b813a83.
Lemma F_80b78 : fetch_word Asan.M.loaded_segments (0x80bc8 : word) = Some W_80b78.
Proof. vm_refl. Qed.
Lemma D_80b78 : decode_any W_80b78 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b7c : bv 32 := 0x7f010113.
Lemma F_80b7c : fetch_word Asan.M.loaded_segments (0x80bcc : word) = Some W_80b7c.
Proof. vm_refl. Qed.
Lemma D_80b7c : decode_any W_80b7c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b80 : bv 32 := 0x00008067.
Lemma F_80b80 : fetch_word Asan.M.loaded_segments (0x80bd0 : word) = Some W_80b80.
Proof. vm_refl. Qed.
Lemma D_80b80 : decode_any W_80b80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b84 : bv 32 := 0x81010113.
Lemma F_80b84 : fetch_word Asan.M.loaded_segments (0x80bd4 : word) = Some W_80b84.
Proof. vm_refl. Qed.
Lemma D_80b84 : decode_any W_80b84 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b88 : bv 32 := 0x7e113423.
Lemma F_80b88 : fetch_word Asan.M.loaded_segments (0x80bd8 : word) = Some W_80b88.
Proof. vm_refl. Qed.
Lemma D_80b88 : decode_any W_80b88 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b8c : bv 32 := 0x7e813023.
Lemma F_80b8c : fetch_word Asan.M.loaded_segments (0x80bdc : word) = Some W_80b8c.
Proof. vm_refl. Qed.
Lemma D_80b8c : decode_any W_80b8c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b90 : bv 32 := 0x7c913c23.
Lemma F_80b90 : fetch_word Asan.M.loaded_segments (0x80be0 : word) = Some W_80b90.
Proof. vm_refl. Qed.
Lemma D_80b90 : decode_any W_80b90 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b94 : bv 32 := 0x7d213823.
Lemma F_80b94 : fetch_word Asan.M.loaded_segments (0x80be4 : word) = Some W_80b94.
Proof. vm_refl. Qed.
Lemma D_80b94 : decode_any W_80b94 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b98 : bv 32 := 0x7d313423.
Lemma F_80b98 : fetch_word Asan.M.loaded_segments (0x80be8 : word) = Some W_80b98.
Proof. vm_refl. Qed.
Lemma D_80b98 : decode_any W_80b98 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b9c : bv 32 := 0x7d413023.
Lemma F_80b9c : fetch_word Asan.M.loaded_segments (0x80bec : word) = Some W_80b9c.
Proof. vm_refl. Qed.
Lemma D_80b9c : decode_any W_80b9c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba0 : bv 32 := 0x7b513c23.
Lemma F_80ba0 : fetch_word Asan.M.loaded_segments (0x80bf0 : word) = Some W_80ba0.
Proof. vm_refl. Qed.
Lemma D_80ba0 : decode_any W_80ba0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba4 : bv 32 := 0x7f010413.
Lemma F_80ba4 : fetch_word Asan.M.loaded_segments (0x80bf4 : word) = Some W_80ba4.
Proof. vm_refl. Qed.
Lemma D_80ba4 : decode_any W_80ba4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba8 : bv 32 := 0xfa010113.
Lemma F_80ba8 : fetch_word Asan.M.loaded_segments (0x80bf8 : word) = Some W_80ba8.
Proof. vm_refl. Qed.
Lemma D_80ba8 : decode_any W_80ba8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bac : bv 32 := 0x00008913.
Lemma F_80bac : fetch_word Asan.M.loaded_segments (0x80bfc : word) = Some W_80bac.
Proof. vm_refl. Qed.
Lemma D_80bac : decode_any W_80bac = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb0 : bv 32 := 0x00050493.
Lemma F_80bb0 : fetch_word Asan.M.loaded_segments (0x80c00 : word) = Some W_80bb0.
Proof. vm_refl. Qed.
Lemma D_80bb0 : decode_any W_80bb0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb4 : bv 32 := 0x6c0070ef.
Lemma F_80bb4 : fetch_word Asan.M.loaded_segments (0x80c04 : word) = Some W_80bb4.
Proof. vm_refl. Qed.
Lemma D_80bb4 : decode_any W_80bb4 = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb8 : bv 32 := 0x06050063.
Lemma F_80bb8 : fetch_word Asan.M.loaded_segments (0x80c08 : word) = Some W_80bb8.
Proof. vm_refl. Qed.
Lemma D_80bb8 : decode_any W_80bb8 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bbc : bv 32 := 0x80040a13.
Lemma F_80bbc : fetch_word Asan.M.loaded_segments (0x80c0c : word) = Some W_80bbc.
Proof. vm_refl. Qed.
Lemma D_80bbc : decode_any W_80bbc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc0 : bv 32 := 0xfb0a0a13.
Lemma F_80bc0 : fetch_word Asan.M.loaded_segments (0x80c10 : word) = Some W_80bc0.
Proof. vm_refl. Qed.
Lemma D_80bc0 : decode_any W_80bc0 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc4 : bv 32 := 0x80040513.
Lemma F_80bc4 : fetch_word Asan.M.loaded_segments (0x80c14 : word) = Some W_80bc4.
Proof. vm_refl. Qed.
Lemma D_80bc4 : decode_any W_80bc4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc8 : bv 32 := 0xfc050513.
Lemma F_80bc8 : fetch_word Asan.M.loaded_segments (0x80c18 : word) = Some W_80bc8.
Proof. vm_refl. Qed.
Lemma D_80bc8 : decode_any W_80bc8 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bcc : bv 32 := 0x7ffa0a93.
Lemma F_80bcc : fetch_word Asan.M.loaded_segments (0x80c1c : word) = Some W_80bcc.
Proof. vm_refl. Qed.
Lemma D_80bcc : decode_any W_80bcc = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd0 : bv 32 := 0x000ab4a3.
Lemma F_80bd0 : fetch_word Asan.M.loaded_segments (0x80c20 : word) = Some W_80bd0.
Proof. vm_refl. Qed.
Lemma D_80bd0 : decode_any W_80bd0 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd4 : bv 32 := 0x00aa3023.
Lemma F_80bd4 : fetch_word Asan.M.loaded_segments (0x80c24 : word) = Some W_80bd4.
Proof. vm_refl. Qed.
Lemma D_80bd4 : decode_any W_80bd4 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd8 : bv 32 := 0x000a3423.
Lemma F_80bd8 : fetch_word Asan.M.loaded_segments (0x80c28 : word) = Some W_80bd8.
Proof. vm_refl. Qed.
Lemma D_80bd8 : decode_any W_80bd8 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bdc : bv 32 := 0x420080ef.
Lemma F_80bdc : fetch_word Asan.M.loaded_segments (0x80c2c : word) = Some W_80bdc.
Proof. vm_refl. Qed.
Lemma D_80bdc : decode_any W_80bdc = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be0 : bv 32 := 0x00200593.
Lemma F_80be0 : fetch_word Asan.M.loaded_segments (0x80c30 : word) = Some W_80be0.
Proof. vm_refl. Qed.
Lemma D_80be0 : decode_any W_80be0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be4 : bv 32 := 0x06a5e263.
Lemma F_80be4 : fetch_word Asan.M.loaded_segments (0x80c34 : word) = Some W_80be4.
Proof. vm_refl. Qed.
Lemma D_80be4 : decode_any W_80be4 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c48 : bv 32 := 0x691200ef.
Lemma F_80c48 : fetch_word Asan.M.loaded_segments (0x80c98 : word) = Some W_80c48.
Proof. vm_refl. Qed.
Lemma D_80c48 : decode_any W_80c48 = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c4c : bv 32 := 0x000d2597.
Lemma F_80c4c : fetch_word Asan.M.loaded_segments (0x80c9c : word) = Some W_80c4c.
Proof. vm_refl. Qed.
Lemma D_80c4c : decode_any W_80c4c = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c50 : bv 32 := 0x48c5b583.
Lemma F_80c50 : fetch_word Asan.M.loaded_segments (0x80ca0 : word) = Some W_80c50.
Proof. vm_refl. Qed.
Lemma D_80c50 : decode_any W_80c50 = Some (Load SZ8 true 11 11 1164, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c54 : bv 32 := 0x0225c983.
Lemma F_80c54 : fetch_word Asan.M.loaded_segments (0x80ca4 : word) = Some W_80c54.
Proof. vm_refl. Qed.
Lemma D_80c54 : decode_any W_80c54 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c58 : bv 32 := 0x00050913.
Lemma F_80c58 : fetch_word Asan.M.loaded_segments (0x80ca8 : word) = Some W_80c58.
Proof. vm_refl. Qed.
Lemma D_80c58 : decode_any W_80c58 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c5c : bv 32 := 0x3a0080ef.
Lemma F_80c5c : fetch_word Asan.M.loaded_segments (0x80cac : word) = Some W_80c5c.
Proof. vm_refl. Qed.
Lemma D_80c5c : decode_any W_80c5c = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c60 : bv 32 := 0x00050793.
Lemma F_80c60 : fetch_word Asan.M.loaded_segments (0x80cb0 : word) = Some W_80c60.
Proof. vm_refl. Qed.
Lemma D_80c60 : decode_any W_80c60 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c64 : bv 32 := 0x00153513.
Lemma F_80c64 : fetch_word Asan.M.loaded_segments (0x80cb4 : word) = Some W_80c64.
Proof. vm_refl. Qed.
Lemma D_80c64 : decode_any W_80c64 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c68 : bv 32 := 0xfff50513.
Lemma F_80c68 : fetch_word Asan.M.loaded_segments (0x80cb8 : word) = Some W_80c68.
Proof. vm_refl. Qed.
Lemma D_80c68 : decode_any W_80c68 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c6c : bv 32 := 0x008575b3.
Lemma F_80c6c : fetch_word Asan.M.loaded_segments (0x80cbc : word) = Some W_80c6c.
Proof. vm_refl. Qed.
Lemma D_80c6c : decode_any W_80c6c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c70 : bv 32 := 0x00100513.
Lemma F_80c70 : fetch_word Asan.M.loaded_segments (0x80cc0 : word) = Some W_80c70.
Proof. vm_refl. Qed.
Lemma D_80c70 : decode_any W_80c70 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c74 : bv 32 := 0x00bab4a3.
Lemma F_80c74 : fetch_word Asan.M.loaded_segments (0x80cc4 : word) = Some W_80c74.
Proof. vm_refl. Qed.
Lemma D_80c74 : decode_any W_80c74 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c78 : bv 32 := 0x00f56a63.
Lemma F_80c78 : fetch_word Asan.M.loaded_segments (0x80cc8 : word) = Some W_80c78.
Proof. vm_refl. Qed.
Lemma D_80c78 : decode_any W_80c78 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c8c : bv 32 := 0x80040513.
Lemma F_80c8c : fetch_word Asan.M.loaded_segments (0x80cdc : word) = Some W_80c8c.
Proof. vm_refl. Qed.
Lemma D_80c8c : decode_any W_80c8c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c90 : bv 32 := 0xfb050513.
Lemma F_80c90 : fetch_word Asan.M.loaded_segments (0x80ce0 : word) = Some W_80c90.
Proof. vm_refl. Qed.
Lemma D_80c90 : decode_any W_80c90 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c94 : bv 32 := 0x00090593.
Lemma F_80c94 : fetch_word Asan.M.loaded_segments (0x80ce4 : word) = Some W_80c94.
Proof. vm_refl. Qed.
Lemma D_80c94 : decode_any W_80c94 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c98 : bv 32 := 0x00040613.
Lemma F_80c98 : fetch_word Asan.M.loaded_segments (0x80ce8 : word) = Some W_80c98.
Proof. vm_refl. Qed.
Lemma D_80c98 : decode_any W_80c98 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c9c : bv 32 := 0x00000693.
Lemma F_80c9c : fetch_word Asan.M.loaded_segments (0x80cec : word) = Some W_80c9c.
Proof. vm_refl. Qed.
Lemma D_80c9c : decode_any W_80c9c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ca0 : bv 32 := 0x00098713.
Lemma F_80ca0 : fetch_word Asan.M.loaded_segments (0x80cf0 : word) = Some W_80ca0.
Proof. vm_refl. Qed.
Lemma D_80ca0 : decode_any W_80ca0 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ca4 : bv 32 := 0x368080ef.
Lemma F_80ca4 : fetch_word Asan.M.loaded_segments (0x80cf4 : word) = Some W_80ca4.
Proof. vm_refl. Qed.
Lemma D_80ca4 : decode_any W_80ca4 = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ca8 : bv 32 := 0x80040593.
Lemma F_80ca8 : fetch_word Asan.M.loaded_segments (0x80cf8 : word) = Some W_80ca8.
Proof. vm_refl. Qed.
Lemma D_80ca8 : decode_any W_80ca8 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cac : bv 32 := 0xfb058593.
Lemma F_80cac : fetch_word Asan.M.loaded_segments (0x80cfc : word) = Some W_80cac.
Proof. vm_refl. Qed.
Lemma D_80cac : decode_any W_80cac = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cb0 : bv 32 := 0x00048513.
Lemma F_80cb0 : fetch_word Asan.M.loaded_segments (0x80d00 : word) = Some W_80cb0.
Proof. vm_refl. Qed.
Lemma D_80cb0 : decode_any W_80cb0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cb4 : bv 32 := 0xefcd80ef.
Lemma F_80cb4 : fetch_word Asan.M.loaded_segments (0x80d04 : word) = Some W_80cb4.
Proof. vm_refl. Qed.
Lemma D_80cb4 : decode_any W_80cb4 = Some (Jal 1 1935100, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cb8 : bv 32 := 0x06010113.
Lemma F_80cb8 : fetch_word Asan.M.loaded_segments (0x80d08 : word) = Some W_80cb8.
Proof. vm_refl. Qed.
Lemma D_80cb8 : decode_any W_80cb8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cbc : bv 32 := 0x7e813083.
Lemma F_80cbc : fetch_word Asan.M.loaded_segments (0x80d0c : word) = Some W_80cbc.
Proof. vm_refl. Qed.
Lemma D_80cbc : decode_any W_80cbc = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cc0 : bv 32 := 0x7e013403.
Lemma F_80cc0 : fetch_word Asan.M.loaded_segments (0x80d10 : word) = Some W_80cc0.
Proof. vm_refl. Qed.
Lemma D_80cc0 : decode_any W_80cc0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cc4 : bv 32 := 0x7d813483.
Lemma F_80cc4 : fetch_word Asan.M.loaded_segments (0x80d14 : word) = Some W_80cc4.
Proof. vm_refl. Qed.
Lemma D_80cc4 : decode_any W_80cc4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cc8 : bv 32 := 0x7d013903.
Lemma F_80cc8 : fetch_word Asan.M.loaded_segments (0x80d18 : word) = Some W_80cc8.
Proof. vm_refl. Qed.
Lemma D_80cc8 : decode_any W_80cc8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ccc : bv 32 := 0x7c813983.
Lemma F_80ccc : fetch_word Asan.M.loaded_segments (0x80d1c : word) = Some W_80ccc.
Proof. vm_refl. Qed.
Lemma D_80ccc : decode_any W_80ccc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cd0 : bv 32 := 0x7c013a03.
Lemma F_80cd0 : fetch_word Asan.M.loaded_segments (0x80d20 : word) = Some W_80cd0.
Proof. vm_refl. Qed.
Lemma D_80cd0 : decode_any W_80cd0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cd4 : bv 32 := 0x7b813a83.
Lemma F_80cd4 : fetch_word Asan.M.loaded_segments (0x80d24 : word) = Some W_80cd4.
Proof. vm_refl. Qed.
Lemma D_80cd4 : decode_any W_80cd4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cd8 : bv 32 := 0x7f010113.
Lemma F_80cd8 : fetch_word Asan.M.loaded_segments (0x80d28 : word) = Some W_80cd8.
Proof. vm_refl. Qed.
Lemma D_80cd8 : decode_any W_80cd8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cdc : bv 32 := 0x00008067.
Lemma F_80cdc : fetch_word Asan.M.loaded_segments (0x80d2c : word) = Some W_80cdc.
Proof. vm_refl. Qed.
Lemma D_80cdc : decode_any W_80cdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

