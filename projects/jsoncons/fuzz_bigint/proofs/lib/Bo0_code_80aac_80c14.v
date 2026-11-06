(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_80aac : bv 32 := 0x00008513.
Lemma F_80aac : fetch_word AsanUbsan.M.loaded_segments (0x80aac : word) = Some W_80aac.
Proof. vm_refl. Qed.
Lemma D_80aac : decode_any W_80aac = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab0 : bv 32 := 0x00008067.
Lemma F_80ab0 : fetch_word AsanUbsan.M.loaded_segments (0x80ab0 : word) = Some W_80ab0.
Proof. vm_refl. Qed.
Lemma D_80ab0 : decode_any W_80ab0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab4 : bv 32 := 0xfc010113.
Lemma F_80ab4 : fetch_word AsanUbsan.M.loaded_segments (0x80ab4 : word) = Some W_80ab4.
Proof. vm_refl. Qed.
Lemma D_80ab4 : decode_any W_80ab4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab8 : bv 32 := 0x02113c23.
Lemma F_80ab8 : fetch_word AsanUbsan.M.loaded_segments (0x80ab8 : word) = Some W_80ab8.
Proof. vm_refl. Qed.
Lemma D_80ab8 : decode_any W_80ab8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80abc : bv 32 := 0x02813823.
Lemma F_80abc : fetch_word AsanUbsan.M.loaded_segments (0x80abc : word) = Some W_80abc.
Proof. vm_refl. Qed.
Lemma D_80abc : decode_any W_80abc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac0 : bv 32 := 0x02913423.
Lemma F_80ac0 : fetch_word AsanUbsan.M.loaded_segments (0x80ac0 : word) = Some W_80ac0.
Proof. vm_refl. Qed.
Lemma D_80ac0 : decode_any W_80ac0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac4 : bv 32 := 0x03213023.
Lemma F_80ac4 : fetch_word AsanUbsan.M.loaded_segments (0x80ac4 : word) = Some W_80ac4.
Proof. vm_refl. Qed.
Lemma D_80ac4 : decode_any W_80ac4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac8 : bv 32 := 0x01313c23.
Lemma F_80ac8 : fetch_word AsanUbsan.M.loaded_segments (0x80ac8 : word) = Some W_80ac8.
Proof. vm_refl. Qed.
Lemma D_80ac8 : decode_any W_80ac8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80acc : bv 32 := 0x01413823.
Lemma F_80acc : fetch_word AsanUbsan.M.loaded_segments (0x80acc : word) = Some W_80acc.
Proof. vm_refl. Qed.
Lemma D_80acc : decode_any W_80acc = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad0 : bv 32 := 0x01513423.
Lemma F_80ad0 : fetch_word AsanUbsan.M.loaded_segments (0x80ad0 : word) = Some W_80ad0.
Proof. vm_refl. Qed.
Lemma D_80ad0 : decode_any W_80ad0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad4 : bv 32 := 0x01613023.
Lemma F_80ad4 : fetch_word AsanUbsan.M.loaded_segments (0x80ad4 : word) = Some W_80ad4.
Proof. vm_refl. Qed.
Lemma D_80ad4 : decode_any W_80ad4 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad8 : bv 32 := 0x00068493.
Lemma F_80ad8 : fetch_word AsanUbsan.M.loaded_segments (0x80ad8 : word) = Some W_80ad8.
Proof. vm_refl. Qed.
Lemma D_80ad8 : decode_any W_80ad8 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80adc : bv 32 := 0x02079413.
Lemma F_80adc : fetch_word AsanUbsan.M.loaded_segments (0x80adc : word) = Some W_80adc.
Proof. vm_refl. Qed.
Lemma D_80adc : decode_any W_80adc = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae0 : bv 32 := 0x00100693.
Lemma F_80ae0 : fetch_word AsanUbsan.M.loaded_segments (0x80ae0 : word) = Some W_80ae0.
Proof. vm_refl. Qed.
Lemma D_80ae0 : decode_any W_80ae0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae4 : bv 32 := 0x02045413.
Lemma F_80ae4 : fetch_word AsanUbsan.M.loaded_segments (0x80ae4 : word) = Some W_80ae4.
Proof. vm_refl. Qed.
Lemma D_80ae4 : decode_any W_80ae4 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae8 : bv 32 := 0x0ef6f863.
Lemma F_80ae8 : fetch_word AsanUbsan.M.loaded_segments (0x80ae8 : word) = Some W_80ae8.
Proof. vm_refl. Qed.
Lemma D_80ae8 : decode_any W_80ae8 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aec : bv 32 := 0x00056697.
Lemma F_80aec : fetch_word AsanUbsan.M.loaded_segments (0x80aec : word) = Some W_80aec.
Proof. vm_refl. Qed.
Lemma D_80aec : decode_any W_80aec = Some (Auipc 13 86, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af0 : bv 32 := 0x9bc6b903.
Lemma F_80af0 : fetch_word AsanUbsan.M.loaded_segments (0x80af0 : word) = Some W_80af0.
Proof. vm_refl. Qed.
Lemma D_80af0 : decode_any W_80af0 = Some (Load SZ8 true 18 13 2492, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af4 : bv 32 := 0x00093683.
Lemma F_80af4 : fetch_word AsanUbsan.M.loaded_segments (0x80af4 : word) = Some W_80af4.
Proof. vm_refl. Qed.
Lemma D_80af4 : decode_any W_80af4 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af8 : bv 32 := 0x00068e63.
Lemma F_80af8 : fetch_word AsanUbsan.M.loaded_segments (0x80af8 : word) = Some W_80af8.
Proof. vm_refl. Qed.
Lemma D_80af8 : decode_any W_80af8 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80afc : bv 32 := 0x00100793.
Lemma F_80afc : fetch_word AsanUbsan.M.loaded_segments (0x80afc : word) = Some W_80afc.
Proof. vm_refl. Qed.
Lemma D_80afc : decode_any W_80afc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b00 : bv 32 := 0x00c4d813.
Lemma F_80b00 : fetch_word AsanUbsan.M.loaded_segments (0x80b00 : word) = Some W_80b00.
Proof. vm_refl. Qed.
Lemma D_80b00 : decode_any W_80b00 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b04 : bv 32 := 0x00f52423.
Lemma F_80b04 : fetch_word AsanUbsan.M.loaded_segments (0x80b04 : word) = Some W_80b04.
Proof. vm_refl. Qed.
Lemma D_80b04 : decode_any W_80b04 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b08 : bv 32 := 0x00b53823.
Lemma F_80b08 : fetch_word AsanUbsan.M.loaded_segments (0x80b08 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b0c : bv 32 := 0x04081463.
Lemma F_80b0c : fetch_word AsanUbsan.M.loaded_segments (0x80b0c : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b10 : bv 32 := 0x0a00006f.
Lemma F_80b10 : fetch_word AsanUbsan.M.loaded_segments (0x80b10 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (Jal 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b14 : bv 32 := 0x00058a13.
Lemma F_80b14 : fetch_word AsanUbsan.M.loaded_segments (0x80b14 : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b18 : bv 32 := 0x00050993.
Lemma F_80b18 : fetch_word AsanUbsan.M.loaded_segments (0x80b18 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b1c : bv 32 := 0x00060a93.
Lemma F_80b1c : fetch_word AsanUbsan.M.loaded_segments (0x80b1c : word) = Some W_80b1c.
Proof. vm_refl. Qed.
Lemma D_80b1c : decode_any W_80b1c = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b20 : bv 32 := 0x00070b13.
Lemma F_80b20 : fetch_word AsanUbsan.M.loaded_segments (0x80b20 : word) = Some W_80b20.
Proof. vm_refl. Qed.
Lemma D_80b20 : decode_any W_80b20 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b24 : bv 32 := 0x9e8f20ef.
Lemma F_80b24 : fetch_word AsanUbsan.M.loaded_segments (0x80b24 : word) = Some W_80b24.
Proof. vm_refl. Qed.
Lemma D_80b24 : decode_any W_80b24 = Some (Jal 1 2040296, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b28 : bv 32 := 0x000b0713.
Lemma F_80b28 : fetch_word AsanUbsan.M.loaded_segments (0x80b28 : word) = Some W_80b28.
Proof. vm_refl. Qed.
Lemma D_80b28 : decode_any W_80b28 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b2c : bv 32 := 0x000a8613.
Lemma F_80b2c : fetch_word AsanUbsan.M.loaded_segments (0x80b2c : word) = Some W_80b2c.
Proof. vm_refl. Qed.
Lemma D_80b2c : decode_any W_80b2c = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b30 : bv 32 := 0x000a0593.
Lemma F_80b30 : fetch_word AsanUbsan.M.loaded_segments (0x80b30 : word) = Some W_80b30.
Proof. vm_refl. Qed.
Lemma D_80b30 : decode_any W_80b30 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b34 : bv 32 := 0x00050693.
Lemma F_80b34 : fetch_word AsanUbsan.M.loaded_segments (0x80b34 : word) = Some W_80b34.
Proof. vm_refl. Qed.
Lemma D_80b34 : decode_any W_80b34 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b38 : bv 32 := 0x00098513.
Lemma F_80b38 : fetch_word AsanUbsan.M.loaded_segments (0x80b38 : word) = Some W_80b38.
Proof. vm_refl. Qed.
Lemma D_80b38 : decode_any W_80b38 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b3c : bv 32 := 0x00d93023.
Lemma F_80b3c : fetch_word AsanUbsan.M.loaded_segments (0x80b3c : word) = Some W_80b3c.
Proof. vm_refl. Qed.
Lemma D_80b3c : decode_any W_80b3c = Some (Store SZ8 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b40 : bv 32 := 0x00100793.
Lemma F_80b40 : fetch_word AsanUbsan.M.loaded_segments (0x80b40 : word) = Some W_80b40.
Proof. vm_refl. Qed.
Lemma D_80b40 : decode_any W_80b40 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b44 : bv 32 := 0x00c4d813.
Lemma F_80b44 : fetch_word AsanUbsan.M.loaded_segments (0x80b44 : word) = Some W_80b44.
Proof. vm_refl. Qed.
Lemma D_80b44 : decode_any W_80b44 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b48 : bv 32 := 0x00f9a423.
Lemma F_80b48 : fetch_word AsanUbsan.M.loaded_segments (0x80b48 : word) = Some W_80b48.
Proof. vm_refl. Qed.
Lemma D_80b48 : decode_any W_80b48 = Some (Store SZ4 19 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b4c : bv 32 := 0x0149b823.
Lemma F_80b4c : fetch_word AsanUbsan.M.loaded_segments (0x80b4c : word) = Some W_80b4c.
Proof. vm_refl. Qed.
Lemma D_80b4c : decode_any W_80b4c = Some (Store SZ8 19 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b50 : bv 32 := 0x06080063.
Lemma F_80b50 : fetch_word AsanUbsan.M.loaded_segments (0x80b50 : word) = Some W_80b50.
Proof. vm_refl. Qed.
Lemma D_80b50 : decode_any W_80b50 = Some (Branch BC_EQ 16 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b54 : bv 32 := 0x0a977263.
Lemma F_80b54 : fetch_word AsanUbsan.M.loaded_segments (0x80b54 : word) = Some W_80b54.
Proof. vm_refl. Qed.
Lemma D_80b54 : decode_any W_80b54 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b58 : bv 32 := 0x04c77c63.
Lemma F_80b58 : fetch_word AsanUbsan.M.loaded_segments (0x80b58 : word) = Some W_80b58.
Proof. vm_refl. Qed.
Lemma D_80b58 : decode_any W_80b58 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b5c : bv 32 := 0xff048493.
Lemma F_80b5c : fetch_word AsanUbsan.M.loaded_segments (0x80b5c : word) = Some W_80b5c.
Proof. vm_refl. Qed.
Lemma D_80b5c : decode_any W_80b5c = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b60 : bv 32 := 0x04967863.
Lemma F_80b60 : fetch_word AsanUbsan.M.loaded_segments (0x80b60 : word) = Some W_80b60.
Proof. vm_refl. Qed.
Lemma D_80b60 : decode_any W_80b60 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b64 : bv 32 := 0x00767713.
Lemma F_80b64 : fetch_word AsanUbsan.M.loaded_segments (0x80b64 : word) = Some W_80b64.
Proof. vm_refl. Qed.
Lemma D_80b64 : decode_any W_80b64 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b68 : bv 32 := 0x04071463.
Lemma F_80b68 : fetch_word AsanUbsan.M.loaded_segments (0x80b68 : word) = Some W_80b68.
Proof. vm_refl. Qed.
Lemma D_80b68 : decode_any W_80b68 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b6c : bv 32 := 0x01050713.
Lemma F_80b6c : fetch_word AsanUbsan.M.loaded_segments (0x80b6c : word) = Some W_80b6c.
Proof. vm_refl. Qed.
Lemma D_80b6c : decode_any W_80b6c = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b70 : bv 32 := 0x00100793.
Lemma F_80b70 : fetch_word AsanUbsan.M.loaded_segments (0x80b70 : word) = Some W_80b70.
Proof. vm_refl. Qed.
Lemma D_80b70 : decode_any W_80b70 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b74 : bv 32 := 0x0287fe63.
Lemma F_80b74 : fetch_word AsanUbsan.M.loaded_segments (0x80b74 : word) = Some W_80b74.
Proof. vm_refl. Qed.
Lemma D_80b74 : decode_any W_80b74 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b78 : bv 32 := 0xff863803.
Lemma F_80b78 : fetch_word AsanUbsan.M.loaded_segments (0x80b78 : word) = Some W_80b78.
Proof. vm_refl. Qed.
Lemma D_80b78 : decode_any W_80b78 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b7c : bv 32 := 0x02d86a63.
Lemma F_80b7c : fetch_word AsanUbsan.M.loaded_segments (0x80b7c : word) = Some W_80b7c.
Proof. vm_refl. Qed.
Lemma D_80b7c : decode_any W_80b7c = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b80 : bv 32 := 0x00b80c63.
Lemma F_80b80 : fetch_word AsanUbsan.M.loaded_segments (0x80b80 : word) = Some W_80b80.
Proof. vm_refl. Qed.
Lemma D_80b80 : decode_any W_80b80 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b84 : bv 32 := 0x00379893.
Lemma F_80b84 : fetch_word AsanUbsan.M.loaded_segments (0x80b84 : word) = Some W_80b84.
Proof. vm_refl. Qed.
Lemma D_80b84 : decode_any W_80b84 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b88 : bv 32 := 0x00178793.
Lemma F_80b88 : fetch_word AsanUbsan.M.loaded_segments (0x80b88 : word) = Some W_80b88.
Proof. vm_refl. Qed.
Lemma D_80b88 : decode_any W_80b88 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b8c : bv 32 := 0x011708b3.
Lemma F_80b8c : fetch_word AsanUbsan.M.loaded_segments (0x80b8c : word) = Some W_80b8c.
Proof. vm_refl. Qed.
Lemma D_80b8c : decode_any W_80b8c = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b90 : bv 32 := 0x00f52423.
Lemma F_80b90 : fetch_word AsanUbsan.M.loaded_segments (0x80b90 : word) = Some W_80b90.
Proof. vm_refl. Qed.
Lemma D_80b90 : decode_any W_80b90 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b94 : bv 32 := 0x0108b023.
Lemma F_80b94 : fetch_word AsanUbsan.M.loaded_segments (0x80b94 : word) = Some W_80b94.
Proof. vm_refl. Qed.
Lemma D_80b94 : decode_any W_80b94 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b98 : bv 32 := 0xff063803.
Lemma F_80b98 : fetch_word AsanUbsan.M.loaded_segments (0x80b98 : word) = Some W_80b98.
Proof. vm_refl. Qed.
Lemma D_80b98 : decode_any W_80b98 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b9c : bv 32 := 0x01067a63.
Lemma F_80b9c : fetch_word AsanUbsan.M.loaded_segments (0x80b9c : word) = Some W_80b9c.
Proof. vm_refl. Qed.
Lemma D_80b9c : decode_any W_80b9c = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba0 : bv 32 := 0x00987863.
Lemma F_80ba0 : fetch_word AsanUbsan.M.loaded_segments (0x80ba0 : word) = Some W_80ba0.
Proof. vm_refl. Qed.
Lemma D_80ba0 : decode_any W_80ba0 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba4 : bv 32 := 0x00787893.
Lemma F_80ba4 : fetch_word AsanUbsan.M.loaded_segments (0x80ba4 : word) = Some W_80ba4.
Proof. vm_refl. Qed.
Lemma D_80ba4 : decode_any W_80ba4 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba8 : bv 32 := 0x00080613.
Lemma F_80ba8 : fetch_word AsanUbsan.M.loaded_segments (0x80ba8 : word) = Some W_80ba8.
Proof. vm_refl. Qed.
Lemma D_80ba8 : decode_any W_80ba8 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bac : bv 32 := 0xfc0884e3.
Lemma F_80bac : fetch_word AsanUbsan.M.loaded_segments (0x80bac : word) = Some W_80bac.
Proof. vm_refl. Qed.
Lemma D_80bac : decode_any W_80bac = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb0 : bv 32 := 0x03813083.
Lemma F_80bb0 : fetch_word AsanUbsan.M.loaded_segments (0x80bb0 : word) = Some W_80bb0.
Proof. vm_refl. Qed.
Lemma D_80bb0 : decode_any W_80bb0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb4 : bv 32 := 0x03013403.
Lemma F_80bb4 : fetch_word AsanUbsan.M.loaded_segments (0x80bb4 : word) = Some W_80bb4.
Proof. vm_refl. Qed.
Lemma D_80bb4 : decode_any W_80bb4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb8 : bv 32 := 0x02813483.
Lemma F_80bb8 : fetch_word AsanUbsan.M.loaded_segments (0x80bb8 : word) = Some W_80bb8.
Proof. vm_refl. Qed.
Lemma D_80bb8 : decode_any W_80bb8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bbc : bv 32 := 0x02013903.
Lemma F_80bbc : fetch_word AsanUbsan.M.loaded_segments (0x80bbc : word) = Some W_80bbc.
Proof. vm_refl. Qed.
Lemma D_80bbc : decode_any W_80bbc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc0 : bv 32 := 0x01813983.
Lemma F_80bc0 : fetch_word AsanUbsan.M.loaded_segments (0x80bc0 : word) = Some W_80bc0.
Proof. vm_refl. Qed.
Lemma D_80bc0 : decode_any W_80bc0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc4 : bv 32 := 0x01013a03.
Lemma F_80bc4 : fetch_word AsanUbsan.M.loaded_segments (0x80bc4 : word) = Some W_80bc4.
Proof. vm_refl. Qed.
Lemma D_80bc4 : decode_any W_80bc4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc8 : bv 32 := 0x00813a83.
Lemma F_80bc8 : fetch_word AsanUbsan.M.loaded_segments (0x80bc8 : word) = Some W_80bc8.
Proof. vm_refl. Qed.
Lemma D_80bc8 : decode_any W_80bc8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bcc : bv 32 := 0x00013b03.
Lemma F_80bcc : fetch_word AsanUbsan.M.loaded_segments (0x80bcc : word) = Some W_80bcc.
Proof. vm_refl. Qed.
Lemma D_80bcc : decode_any W_80bcc = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd0 : bv 32 := 0x04010113.
Lemma F_80bd0 : fetch_word AsanUbsan.M.loaded_segments (0x80bd0 : word) = Some W_80bd0.
Proof. vm_refl. Qed.
Lemma D_80bd0 : decode_any W_80bd0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd4 : bv 32 := 0x00008067.
Lemma F_80bd4 : fetch_word AsanUbsan.M.loaded_segments (0x80bd4 : word) = Some W_80bd4.
Proof. vm_refl. Qed.
Lemma D_80bd4 : decode_any W_80bd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd8 : bv 32 := 0xfff9e517.
Lemma F_80bd8 : fetch_word AsanUbsan.M.loaded_segments (0x80bd8 : word) = Some W_80bd8.
Proof. vm_refl. Qed.
Lemma D_80bd8 : decode_any W_80bd8 = Some (Auipc 10 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bdc : bv 32 := 0xfff9b617.
Lemma F_80bdc : fetch_word AsanUbsan.M.loaded_segments (0x80bdc : word) = Some W_80bdc.
Proof. vm_refl. Qed.
Lemma D_80bdc : decode_any W_80bdc = Some (Auipc 12 1048475, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be0 : bv 32 := 0x06400593.
Lemma F_80be0 : fetch_word AsanUbsan.M.loaded_segments (0x80be0 : word) = Some W_80be0.
Proof. vm_refl. Qed.
Lemma D_80be0 : decode_any W_80be0 = Some (OpImm ALU_ADD 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be4 : bv 32 := 0xea450513.
Lemma F_80be4 : fetch_word AsanUbsan.M.loaded_segments (0x80be4 : word) = Some W_80be4.
Proof. vm_refl. Qed.
Lemma D_80be4 : decode_any W_80be4 = Some (OpImm ALU_ADD 10 10 3748, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be8 : bv 32 := 0x31060613.
Lemma F_80be8 : fetch_word AsanUbsan.M.loaded_segments (0x80be8 : word) = Some W_80be8.
Proof. vm_refl. Qed.
Lemma D_80be8 : decode_any W_80be8 = Some (OpImm ALU_ADD 12 12 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bec : bv 32 := 0x00200713.
Lemma F_80bec : fetch_word AsanUbsan.M.loaded_segments (0x80bec : word) = Some W_80bec.
Proof. vm_refl. Qed.
Lemma D_80bec : decode_any W_80bec = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bf0 : bv 32 := 0x00040693.
Lemma F_80bf0 : fetch_word AsanUbsan.M.loaded_segments (0x80bf0 : word) = Some W_80bf0.
Proof. vm_refl. Qed.
Lemma D_80bf0 : decode_any W_80bf0 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bf4 : bv 32 := 0xef4f80ef.
Lemma F_80bf4 : fetch_word AsanUbsan.M.loaded_segments (0x80bf4 : word) = Some W_80bf4.
Proof. vm_refl. Qed.
Lemma D_80bf4 : decode_any W_80bf4 = Some (Jal 1 2066164, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bf8 : bv 32 := 0xfff9e517.
Lemma F_80bf8 : fetch_word AsanUbsan.M.loaded_segments (0x80bf8 : word) = Some W_80bf8.
Proof. vm_refl. Qed.
Lemma D_80bf8 : decode_any W_80bf8 = Some (Auipc 10 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bfc : bv 32 := 0xfff93597.
Lemma F_80bfc : fetch_word AsanUbsan.M.loaded_segments (0x80bfc : word) = Some W_80bfc.
Proof. vm_refl. Qed.
Lemma D_80bfc : decode_any W_80bfc = Some (Auipc 11 1048467, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c00 : bv 32 := 0xe8450513.
Lemma F_80c00 : fetch_word AsanUbsan.M.loaded_segments (0x80c00 : word) = Some W_80c00.
Proof. vm_refl. Qed.
Lemma D_80c00 : decode_any W_80c00 = Some (OpImm ALU_ADD 10 10 3716, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c04 : bv 32 := 0x46558613.
Lemma F_80c04 : fetch_word AsanUbsan.M.loaded_segments (0x80c04 : word) = Some W_80c04.
Proof. vm_refl. Qed.
Lemma D_80c04 : decode_any W_80c04 = Some (OpImm ALU_ADD 12 11 1125, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c08 : bv 32 := 0x04e00593.
Lemma F_80c08 : fetch_word AsanUbsan.M.loaded_segments (0x80c08 : word) = Some W_80c08.
Proof. vm_refl. Qed.
Lemma D_80c08 : decode_any W_80c08 = Some (OpImm ALU_ADD 11 0 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c0c : bv 32 := 0x00048693.
Lemma F_80c0c : fetch_word AsanUbsan.M.loaded_segments (0x80c0c : word) = Some W_80c0c.
Proof. vm_refl. Qed.
Lemma D_80c0c : decode_any W_80c0c = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c10 : bv 32 := 0xed8f80ef.
Lemma F_80c10 : fetch_word AsanUbsan.M.loaded_segments (0x80c10 : word) = Some W_80c10.
Proof. vm_refl. Qed.
Lemma D_80c10 : decode_any W_80c10 = Some (Jal 1 2066136, 4%Z).
Proof. vm_refl. Qed.
