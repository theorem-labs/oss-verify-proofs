(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_80ac0 : bv 32 := 0x5450006f.
Lemma F_80ac0 : fetch_word AsanUbsan.M.loaded_segments (0x80b08 : word) = Some W_80ac0.
Proof. vm_refl. Qed.
Lemma D_80ac0 : decode_any W_80ac0 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ac4 : bv 32 := 0x2000106f.
Lemma F_80ac4 : fetch_word AsanUbsan.M.loaded_segments (0x80b0c : word) = Some W_80ac4.
Proof. vm_refl. Qed.
Lemma D_80ac4 : decode_any W_80ac4 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ac8 : bv 32 := 0x81010113.
Lemma F_80ac8 : fetch_word AsanUbsan.M.loaded_segments (0x80b10 : word) = Some W_80ac8.
Proof. vm_refl. Qed.
Lemma D_80ac8 : decode_any W_80ac8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80acc : bv 32 := 0x7e113423.
Lemma F_80acc : fetch_word AsanUbsan.M.loaded_segments (0x80b14 : word) = Some W_80acc.
Proof. vm_refl. Qed.
Lemma D_80acc : decode_any W_80acc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ad0 : bv 32 := 0x7e813023.
Lemma F_80ad0 : fetch_word AsanUbsan.M.loaded_segments (0x80b18 : word) = Some W_80ad0.
Proof. vm_refl. Qed.
Lemma D_80ad0 : decode_any W_80ad0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ad4 : bv 32 := 0x7c913c23.
Lemma F_80ad4 : fetch_word AsanUbsan.M.loaded_segments (0x80b1c : word) = Some W_80ad4.
Proof. vm_refl. Qed.
Lemma D_80ad4 : decode_any W_80ad4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ad8 : bv 32 := 0x7d213823.
Lemma F_80ad8 : fetch_word AsanUbsan.M.loaded_segments (0x80b20 : word) = Some W_80ad8.
Proof. vm_refl. Qed.
Lemma D_80ad8 : decode_any W_80ad8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80adc : bv 32 := 0x7d313423.
Lemma F_80adc : fetch_word AsanUbsan.M.loaded_segments (0x80b24 : word) = Some W_80adc.
Proof. vm_refl. Qed.
Lemma D_80adc : decode_any W_80adc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ae0 : bv 32 := 0x7d413023.
Lemma F_80ae0 : fetch_word AsanUbsan.M.loaded_segments (0x80b28 : word) = Some W_80ae0.
Proof. vm_refl. Qed.
Lemma D_80ae0 : decode_any W_80ae0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ae4 : bv 32 := 0x7b513c23.
Lemma F_80ae4 : fetch_word AsanUbsan.M.loaded_segments (0x80b2c : word) = Some W_80ae4.
Proof. vm_refl. Qed.
Lemma D_80ae4 : decode_any W_80ae4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ae8 : bv 32 := 0x7b613823.
Lemma F_80ae8 : fetch_word AsanUbsan.M.loaded_segments (0x80b30 : word) = Some W_80ae8.
Proof. vm_refl. Qed.
Lemma D_80ae8 : decode_any W_80ae8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80aec : bv 32 := 0x7b713423.
Lemma F_80aec : fetch_word AsanUbsan.M.loaded_segments (0x80b34 : word) = Some W_80aec.
Proof. vm_refl. Qed.
Lemma D_80aec : decode_any W_80aec = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80af0 : bv 32 := 0x7f010413.
Lemma F_80af0 : fetch_word AsanUbsan.M.loaded_segments (0x80b38 : word) = Some W_80af0.
Proof. vm_refl. Qed.
Lemma D_80af0 : decode_any W_80af0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80af4 : bv 32 := 0xf9010113.
Lemma F_80af4 : fetch_word AsanUbsan.M.loaded_segments (0x80b3c : word) = Some W_80af4.
Proof. vm_refl. Qed.
Lemma D_80af4 : decode_any W_80af4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80af8 : bv 32 := 0x000e4697.
Lemma F_80af8 : fetch_word AsanUbsan.M.loaded_segments (0x80b40 : word) = Some W_80af8.
Proof. vm_refl. Qed.
Lemma D_80af8 : decode_any W_80af8 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80afc : bv 32 := 0x5406b683.
Lemma F_80afc : fetch_word AsanUbsan.M.loaded_segments (0x80b44 : word) = Some W_80afc.
Proof. vm_refl. Qed.
Lemma D_80afc : decode_any W_80afc = Some (Load SZ8 true 13 13 1344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b00 : bv 32 := 0x0006c683.
Lemma F_80b00 : fetch_word AsanUbsan.M.loaded_segments (0x80b48 : word) = Some W_80b00.
Proof. vm_refl. Qed.
Lemma D_80b00 : decode_any W_80b00 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b04 : bv 32 := 0x0e068863.
Lemma F_80b04 : fetch_word AsanUbsan.M.loaded_segments (0x80b4c : word) = Some W_80b04.
Proof. vm_refl. Qed.
Lemma D_80b04 : decode_any W_80b04 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b08 : bv 32 := 0x80040a13.
Lemma F_80b08 : fetch_word AsanUbsan.M.loaded_segments (0x80b50 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b0c : bv 32 := 0xfa0a0a13.
Lemma F_80b0c : fetch_word AsanUbsan.M.loaded_segments (0x80b54 : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b10 : bv 32 := 0x00c58ab3.
Lemma F_80b10 : fetch_word AsanUbsan.M.loaded_segments (0x80b58 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b14 : bv 32 := 0x00c509b3.
Lemma F_80b14 : fetch_word AsanUbsan.M.loaded_segments (0x80b5c : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b18 : bv 32 := 0x00b50663.
Lemma F_80b18 : fetch_word AsanUbsan.M.loaded_segments (0x80b60 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b1c : bv 32 := 0x0135f463.
Lemma F_80b1c : fetch_word AsanUbsan.M.loaded_segments (0x80b64 : word) = Some W_80b1c.
Proof. vm_refl. Qed.
Lemma D_80b1c : decode_any W_80b1c = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b20 : bv 32 := 0x1b556a63.
Lemma F_80b20 : fetch_word AsanUbsan.M.loaded_segments (0x80b68 : word) = Some W_80b20.
Proof. vm_refl. Qed.
Lemma D_80b20 : decode_any W_80b20 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b24 : bv 32 := 0xfff5c693.
Lemma F_80b24 : fetch_word AsanUbsan.M.loaded_segments (0x80b6c : word) = Some W_80b24.
Proof. vm_refl. Qed.
Lemma D_80b24 : decode_any W_80b24 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b28 : bv 32 := 0x26c6e463.
Lemma F_80b28 : fetch_word AsanUbsan.M.loaded_segments (0x80b70 : word) = Some W_80b28.
Proof. vm_refl. Qed.
Lemma D_80b28 : decode_any W_80b28 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b2c : bv 32 := 0xfbf60b13.
Lemma F_80b2c : fetch_word AsanUbsan.M.loaded_segments (0x80b74 : word) = Some W_80b2c.
Proof. vm_refl. Qed.
Lemma D_80b2c : decode_any W_80b2c = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b30 : bv 32 := 0xfbf00693.
Lemma F_80b30 : fetch_word AsanUbsan.M.loaded_segments (0x80b78 : word) = Some W_80b30.
Proof. vm_refl. Qed.
Lemma D_80b30 : decode_any W_80b30 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b34 : bv 32 := 0x2f66f263.
Lemma F_80b34 : fetch_word AsanUbsan.M.loaded_segments (0x80b7c : word) = Some W_80b34.
Proof. vm_refl. Qed.
Lemma D_80b34 : decode_any W_80b34 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b38 : bv 32 := 0x000e4697.
Lemma F_80b38 : fetch_word AsanUbsan.M.loaded_segments (0x80b80 : word) = Some W_80b38.
Proof. vm_refl. Qed.
Lemma D_80b38 : decode_any W_80b38 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b3c : bv 32 := 0x9986b683.
Lemma F_80b3c : fetch_word AsanUbsan.M.loaded_segments (0x80b84 : word) = Some W_80b3c.
Proof. vm_refl. Qed.
Lemma D_80b3c : decode_any W_80b3c = Some (Load SZ8 true 13 13 2456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b40 : bv 32 := 0x0006b703.
Lemma F_80b40 : fetch_word AsanUbsan.M.loaded_segments (0x80b88 : word) = Some W_80b40.
Proof. vm_refl. Qed.
Lemma D_80b40 : decode_any W_80b40 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b44 : bv 32 := 0xfffa8a93.
Lemma F_80b44 : fetch_word AsanUbsan.M.loaded_segments (0x80b8c : word) = Some W_80b44.
Proof. vm_refl. Qed.
Lemma D_80b44 : decode_any W_80b44 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b48 : bv 32 := 0x0035d693.
Lemma F_80b48 : fetch_word AsanUbsan.M.loaded_segments (0x80b90 : word) = Some W_80b48.
Proof. vm_refl. Qed.
Lemma D_80b48 : decode_any W_80b48 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b4c : bv 32 := 0x003ad793.
Lemma F_80b4c : fetch_word AsanUbsan.M.loaded_segments (0x80b94 : word) = Some W_80b4c.
Proof. vm_refl. Qed.
Lemma D_80b4c : decode_any W_80b4c = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b50 : bv 32 := 0x00d706b3.
Lemma F_80b50 : fetch_word AsanUbsan.M.loaded_segments (0x80b98 : word) = Some W_80b50.
Proof. vm_refl. Qed.
Lemma D_80b50 : decode_any W_80b50 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b54 : bv 32 := 0x00f70733.
Lemma F_80b54 : fetch_word AsanUbsan.M.loaded_segments (0x80b9c : word) = Some W_80b54.
Proof. vm_refl. Qed.
Lemma D_80b54 : decode_any W_80b54 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b58 : bv 32 := 0xff86f793.
Lemma F_80b58 : fetch_word AsanUbsan.M.loaded_segments (0x80ba0 : word) = Some W_80b58.
Proof. vm_refl. Qed.
Lemma D_80b58 : decode_any W_80b58 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b5c : bv 32 := 0xff877813.
Lemma F_80b5c : fetch_word AsanUbsan.M.loaded_segments (0x80ba4 : word) = Some W_80b5c.
Proof. vm_refl. Qed.
Lemma D_80b5c : decode_any W_80b5c = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b60 : bv 32 := 0x0007b783.
Lemma F_80b60 : fetch_word AsanUbsan.M.loaded_segments (0x80ba8 : word) = Some W_80b60.
Proof. vm_refl. Qed.
Lemma D_80b60 : decode_any W_80b60 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b64 : bv 32 := 0x00083803.
Lemma F_80b64 : fetch_word AsanUbsan.M.loaded_segments (0x80bac : word) = Some W_80b64.
Proof. vm_refl. Qed.
Lemma D_80b64 : decode_any W_80b64 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b68 : bv 32 := 0x00f867b3.
Lemma F_80b68 : fetch_word AsanUbsan.M.loaded_segments (0x80bb0 : word) = Some W_80b68.
Proof. vm_refl. Qed.
Lemma D_80b68 : decode_any W_80b68 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b6c : bv 32 := 0x2a079a63.
Lemma F_80b6c : fetch_word AsanUbsan.M.loaded_segments (0x80bb4 : word) = Some W_80b6c.
Proof. vm_refl. Qed.
Lemma D_80b6c : decode_any W_80b6c = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b70 : bv 32 := 0xfff54693.
Lemma F_80b70 : fetch_word AsanUbsan.M.loaded_segments (0x80bb8 : word) = Some W_80b70.
Proof. vm_refl. Qed.
Lemma D_80b70 : decode_any W_80b70 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b74 : bv 32 := 0x0cc6ea63.
Lemma F_80b74 : fetch_word AsanUbsan.M.loaded_segments (0x80bbc : word) = Some W_80b74.
Proof. vm_refl. Qed.
Lemma D_80b74 : decode_any W_80b74 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b78 : bv 32 := 0xfbf00693.
Lemma F_80b78 : fetch_word AsanUbsan.M.loaded_segments (0x80bc0 : word) = Some W_80b78.
Proof. vm_refl. Qed.
Lemma D_80b78 : decode_any W_80b78 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b7c : bv 32 := 0x1566f863.
Lemma F_80b7c : fetch_word AsanUbsan.M.loaded_segments (0x80bc4 : word) = Some W_80b7c.
Proof. vm_refl. Qed.
Lemma D_80b7c : decode_any W_80b7c = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b80 : bv 32 := 0x000e4697.
Lemma F_80b80 : fetch_word AsanUbsan.M.loaded_segments (0x80bc8 : word) = Some W_80b80.
Proof. vm_refl. Qed.
Lemma D_80b80 : decode_any W_80b80 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b84 : bv 32 := 0x9506b683.
Lemma F_80b84 : fetch_word AsanUbsan.M.loaded_segments (0x80bcc : word) = Some W_80b84.
Proof. vm_refl. Qed.
Lemma D_80b84 : decode_any W_80b84 = Some (Load SZ8 true 13 13 2384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b88 : bv 32 := 0x0006b703.
Lemma F_80b88 : fetch_word AsanUbsan.M.loaded_segments (0x80bd0 : word) = Some W_80b88.
Proof. vm_refl. Qed.
Lemma D_80b88 : decode_any W_80b88 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b8c : bv 32 := 0xfff98993.
Lemma F_80b8c : fetch_word AsanUbsan.M.loaded_segments (0x80bd4 : word) = Some W_80b8c.
Proof. vm_refl. Qed.
Lemma D_80b8c : decode_any W_80b8c = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b90 : bv 32 := 0x00355693.
Lemma F_80b90 : fetch_word AsanUbsan.M.loaded_segments (0x80bd8 : word) = Some W_80b90.
Proof. vm_refl. Qed.
Lemma D_80b90 : decode_any W_80b90 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b94 : bv 32 := 0x0039d793.
Lemma F_80b94 : fetch_word AsanUbsan.M.loaded_segments (0x80bdc : word) = Some W_80b94.
Proof. vm_refl. Qed.
Lemma D_80b94 : decode_any W_80b94 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b98 : bv 32 := 0x00d706b3.
Lemma F_80b98 : fetch_word AsanUbsan.M.loaded_segments (0x80be0 : word) = Some W_80b98.
Proof. vm_refl. Qed.
Lemma D_80b98 : decode_any W_80b98 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b9c : bv 32 := 0x00f70733.
Lemma F_80b9c : fetch_word AsanUbsan.M.loaded_segments (0x80be4 : word) = Some W_80b9c.
Proof. vm_refl. Qed.
Lemma D_80b9c : decode_any W_80b9c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ba0 : bv 32 := 0xff86f793.
Lemma F_80ba0 : fetch_word AsanUbsan.M.loaded_segments (0x80be8 : word) = Some W_80ba0.
Proof. vm_refl. Qed.
Lemma D_80ba0 : decode_any W_80ba0 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ba4 : bv 32 := 0xff877813.
Lemma F_80ba4 : fetch_word AsanUbsan.M.loaded_segments (0x80bec : word) = Some W_80ba4.
Proof. vm_refl. Qed.
Lemma D_80ba4 : decode_any W_80ba4 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ba8 : bv 32 := 0x0007b783.
Lemma F_80ba8 : fetch_word AsanUbsan.M.loaded_segments (0x80bf0 : word) = Some W_80ba8.
Proof. vm_refl. Qed.
Lemma D_80ba8 : decode_any W_80ba8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bac : bv 32 := 0x00083803.
Lemma F_80bac : fetch_word AsanUbsan.M.loaded_segments (0x80bf4 : word) = Some W_80bac.
Proof. vm_refl. Qed.
Lemma D_80bac : decode_any W_80bac = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bb0 : bv 32 := 0x00f867b3.
Lemma F_80bb0 : fetch_word AsanUbsan.M.loaded_segments (0x80bf8 : word) = Some W_80bb0.
Proof. vm_refl. Qed.
Lemma D_80bb0 : decode_any W_80bb0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bb4 : bv 32 := 0x30079863.
Lemma F_80bb4 : fetch_word AsanUbsan.M.loaded_segments (0x80bfc : word) = Some W_80bb4.
Proof. vm_refl. Qed.
Lemma D_80bb4 : decode_any W_80bb4 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bb8 : bv 32 := 0x000e6697.
Lemma F_80bb8 : fetch_word AsanUbsan.M.loaded_segments (0x80c00 : word) = Some W_80bb8.
Proof. vm_refl. Qed.
Lemma D_80bb8 : decode_any W_80bb8 = Some (Auipc 13 230, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bbc : bv 32 := 0x9486b683.
Lemma F_80bbc : fetch_word AsanUbsan.M.loaded_segments (0x80c04 : word) = Some W_80bbc.
Proof. vm_refl. Qed.
Lemma D_80bbc : decode_any W_80bbc = Some (Load SZ8 true 13 13 2376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bc0 : bv 32 := 0x000680e7.
Lemma F_80bc0 : fetch_word AsanUbsan.M.loaded_segments (0x80c08 : word) = Some W_80bc0.
Proof. vm_refl. Qed.
Lemma D_80bc0 : decode_any W_80bc0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bc4 : bv 32 := 0x07010113.
Lemma F_80bc4 : fetch_word AsanUbsan.M.loaded_segments (0x80c0c : word) = Some W_80bc4.
Proof. vm_refl. Qed.
Lemma D_80bc4 : decode_any W_80bc4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bc8 : bv 32 := 0x7e813083.
Lemma F_80bc8 : fetch_word AsanUbsan.M.loaded_segments (0x80c10 : word) = Some W_80bc8.
Proof. vm_refl. Qed.
Lemma D_80bc8 : decode_any W_80bc8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bcc : bv 32 := 0x7e013403.
Lemma F_80bcc : fetch_word AsanUbsan.M.loaded_segments (0x80c14 : word) = Some W_80bcc.
Proof. vm_refl. Qed.
Lemma D_80bcc : decode_any W_80bcc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bd0 : bv 32 := 0x7d813483.
Lemma F_80bd0 : fetch_word AsanUbsan.M.loaded_segments (0x80c18 : word) = Some W_80bd0.
Proof. vm_refl. Qed.
Lemma D_80bd0 : decode_any W_80bd0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bd4 : bv 32 := 0x7d013903.
Lemma F_80bd4 : fetch_word AsanUbsan.M.loaded_segments (0x80c1c : word) = Some W_80bd4.
Proof. vm_refl. Qed.
Lemma D_80bd4 : decode_any W_80bd4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bd8 : bv 32 := 0x7c813983.
Lemma F_80bd8 : fetch_word AsanUbsan.M.loaded_segments (0x80c20 : word) = Some W_80bd8.
Proof. vm_refl. Qed.
Lemma D_80bd8 : decode_any W_80bd8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bdc : bv 32 := 0x7c013a03.
Lemma F_80bdc : fetch_word AsanUbsan.M.loaded_segments (0x80c24 : word) = Some W_80bdc.
Proof. vm_refl. Qed.
Lemma D_80bdc : decode_any W_80bdc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be0 : bv 32 := 0x7b813a83.
Lemma F_80be0 : fetch_word AsanUbsan.M.loaded_segments (0x80c28 : word) = Some W_80be0.
Proof. vm_refl. Qed.
Lemma D_80be0 : decode_any W_80be0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be4 : bv 32 := 0x7b013b03.
Lemma F_80be4 : fetch_word AsanUbsan.M.loaded_segments (0x80c2c : word) = Some W_80be4.
Proof. vm_refl. Qed.
Lemma D_80be4 : decode_any W_80be4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be8 : bv 32 := 0x7a813b83.
Lemma F_80be8 : fetch_word AsanUbsan.M.loaded_segments (0x80c30 : word) = Some W_80be8.
Proof. vm_refl. Qed.
Lemma D_80be8 : decode_any W_80be8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bec : bv 32 := 0x7f010113.
Lemma F_80bec : fetch_word AsanUbsan.M.loaded_segments (0x80c34 : word) = Some W_80bec.
Proof. vm_refl. Qed.
Lemma D_80bec : decode_any W_80bec = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bf0 : bv 32 := 0x00008067.
Lemma F_80bf0 : fetch_word AsanUbsan.M.loaded_segments (0x80c38 : word) = Some W_80bf0.
Proof. vm_refl. Qed.
Lemma D_80bf0 : decode_any W_80bf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ccc : bv 32 := 0x22061663.
Lemma F_80ccc : fetch_word AsanUbsan.M.loaded_segments (0x80d14 : word) = Some W_80ccc.
Proof. vm_refl. Qed.
Lemma D_80ccc : decode_any W_80ccc = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd0 : bv 32 := 0xee9ff06f.
Lemma F_80cd0 : fetch_word AsanUbsan.M.loaded_segments (0x80d18 : word) = Some W_80cd0.
Proof. vm_refl. Qed.
Lemma D_80cd0 : decode_any W_80cd0 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e18 : bv 32 := 0x02061e63.
Lemma F_80e18 : fetch_word AsanUbsan.M.loaded_segments (0x80e60 : word) = Some W_80e18.
Proof. vm_refl. Qed.
Lemma D_80e18 : decode_any W_80e18 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e1c : bv 32 := 0xd55ff06f.
Lemma F_80e1c : fetch_word AsanUbsan.M.loaded_segments (0x80e64 : word) = Some W_80e1c.
Proof. vm_refl. Qed.
Lemma D_80e1c : decode_any W_80e1c = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e20 : bv 32 := 0x00070783.
Lemma F_80e20 : fetch_word AsanUbsan.M.loaded_segments (0x80e68 : word) = Some W_80e20.
Proof. vm_refl. Qed.
Lemma D_80e20 : decode_any W_80e20 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e24 : bv 32 := 0x007af813.
Lemma F_80e24 : fetch_word AsanUbsan.M.loaded_segments (0x80e6c : word) = Some W_80e24.
Proof. vm_refl. Qed.
Lemma D_80e24 : decode_any W_80e24 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e28 : bv 32 := 0x00f038b3.
Lemma F_80e28 : fetch_word AsanUbsan.M.loaded_segments (0x80e70 : word) = Some W_80e28.
Proof. vm_refl. Qed.
Lemma D_80e28 : decode_any W_80e28 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e2c : bv 32 := 0x00f827b3.
Lemma F_80e2c : fetch_word AsanUbsan.M.loaded_segments (0x80e74 : word) = Some W_80e2c.
Proof. vm_refl. Qed.
Lemma D_80e2c : decode_any W_80e2c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e30 : bv 32 := 0x0017c793.
Lemma F_80e30 : fetch_word AsanUbsan.M.loaded_segments (0x80e78 : word) = Some W_80e30.
Proof. vm_refl. Qed.
Lemma D_80e30 : decode_any W_80e30 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e34 : bv 32 := 0x00f8f7b3.
Lemma F_80e34 : fetch_word AsanUbsan.M.loaded_segments (0x80e7c : word) = Some W_80e34.
Proof. vm_refl. Qed.
Lemma D_80e34 : decode_any W_80e34 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e38 : bv 32 := 0x00e6fa63.
Lemma F_80e38 : fetch_word AsanUbsan.M.loaded_segments (0x80e80 : word) = Some W_80e38.
Proof. vm_refl. Qed.
Lemma D_80e38 : decode_any W_80e38 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e3c : bv 32 := 0x0006c803.
Lemma F_80e3c : fetch_word AsanUbsan.M.loaded_segments (0x80e84 : word) = Some W_80e3c.
Proof. vm_refl. Qed.
Lemma D_80e3c : decode_any W_80e3c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e40 : bv 32 := 0x00168693.
Lemma F_80e40 : fetch_word AsanUbsan.M.loaded_segments (0x80e88 : word) = Some W_80e40.
Proof. vm_refl. Qed.
Lemma D_80e40 : decode_any W_80e40 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e44 : bv 32 := 0x00f867b3.
Lemma F_80e44 : fetch_word AsanUbsan.M.loaded_segments (0x80e8c : word) = Some W_80e44.
Proof. vm_refl. Qed.
Lemma D_80e44 : decode_any W_80e44 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e48 : bv 32 := 0xfee69ae3.
Lemma F_80e48 : fetch_word AsanUbsan.M.loaded_segments (0x80e90 : word) = Some W_80e48.
Proof. vm_refl. Qed.
Lemma D_80e48 : decode_any W_80e48 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e4c : bv 32 := 0x0ff7f693.
Lemma F_80e4c : fetch_word AsanUbsan.M.loaded_segments (0x80e94 : word) = Some W_80e4c.
Proof. vm_refl. Qed.
Lemma D_80e4c : decode_any W_80e4c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e50 : bv 32 := 0xd20680e3.
Lemma F_80e50 : fetch_word AsanUbsan.M.loaded_segments (0x80e98 : word) = Some W_80e50.
Proof. vm_refl. Qed.
Lemma D_80e50 : decode_any W_80e50 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e54 : bv 32 := 0x00050a93.
Lemma F_80e54 : fetch_word AsanUbsan.M.loaded_segments (0x80e9c : word) = Some W_80e54.
Proof. vm_refl. Qed.
Lemma D_80e54 : decode_any W_80e54 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e58 : bv 32 := 0x00058513.
Lemma F_80e58 : fetch_word AsanUbsan.M.loaded_segments (0x80ea0 : word) = Some W_80e58.
Proof. vm_refl. Qed.
Lemma D_80e58 : decode_any W_80e58 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e5c : bv 32 := 0x00058b93.
Lemma F_80e5c : fetch_word AsanUbsan.M.loaded_segments (0x80ea4 : word) = Some W_80e5c.
Proof. vm_refl. Qed.
Lemma D_80e5c : decode_any W_80e5c = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e60 : bv 32 := 0x00060593.
Lemma F_80e60 : fetch_word AsanUbsan.M.loaded_segments (0x80ea8 : word) = Some W_80e60.
Proof. vm_refl. Qed.
Lemma D_80e60 : decode_any W_80e60 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e64 : bv 32 := 0x00060493.
Lemma F_80e64 : fetch_word AsanUbsan.M.loaded_segments (0x80eac : word) = Some W_80e64.
Proof. vm_refl. Qed.
Lemma D_80e64 : decode_any W_80e64 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e68 : bv 32 := 0x48c030ef.
Lemma F_80e68 : fetch_word AsanUbsan.M.loaded_segments (0x80eb0 : word) = Some W_80e68.
Proof. vm_refl. Qed.
Lemma D_80e68 : decode_any W_80e68 = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e6c : bv 32 := 0x000b8593.
Lemma F_80e6c : fetch_word AsanUbsan.M.loaded_segments (0x80eb4 : word) = Some W_80e6c.
Proof. vm_refl. Qed.
Lemma D_80e6c : decode_any W_80e6c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e70 : bv 32 := 0x00048613.
Lemma F_80e70 : fetch_word AsanUbsan.M.loaded_segments (0x80eb8 : word) = Some W_80e70.
Proof. vm_refl. Qed.
Lemma D_80e70 : decode_any W_80e70 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e74 : bv 32 := 0x00050913.
Lemma F_80e74 : fetch_word AsanUbsan.M.loaded_segments (0x80ebc : word) = Some W_80e74.
Proof. vm_refl. Qed.
Lemma D_80e74 : decode_any W_80e74 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e78 : bv 32 := 0x000a8513.
Lemma F_80e78 : fetch_word AsanUbsan.M.loaded_segments (0x80ec0 : word) = Some W_80e78.
Proof. vm_refl. Qed.
Lemma D_80e78 : decode_any W_80e78 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e7c : bv 32 := 0xce090ae3.
Lemma F_80e7c : fetch_word AsanUbsan.M.loaded_segments (0x80ec4 : word) = Some W_80e7c.
Proof. vm_refl. Qed.
Lemma D_80e7c : decode_any W_80e7c = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ec4 : bv 32 := 0x00070783.
Lemma F_80ec4 : fetch_word AsanUbsan.M.loaded_segments (0x80f0c : word) = Some W_80ec4.
Proof. vm_refl. Qed.
Lemma D_80ec4 : decode_any W_80ec4 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ec8 : bv 32 := 0x0079f813.
Lemma F_80ec8 : fetch_word AsanUbsan.M.loaded_segments (0x80f10 : word) = Some W_80ec8.
Proof. vm_refl. Qed.
Lemma D_80ec8 : decode_any W_80ec8 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ecc : bv 32 := 0x00f038b3.
Lemma F_80ecc : fetch_word AsanUbsan.M.loaded_segments (0x80f14 : word) = Some W_80ecc.
Proof. vm_refl. Qed.
Lemma D_80ecc : decode_any W_80ecc = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ed0 : bv 32 := 0x00f827b3.
Lemma F_80ed0 : fetch_word AsanUbsan.M.loaded_segments (0x80f18 : word) = Some W_80ed0.
Proof. vm_refl. Qed.
Lemma D_80ed0 : decode_any W_80ed0 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ed4 : bv 32 := 0x0017c793.
Lemma F_80ed4 : fetch_word AsanUbsan.M.loaded_segments (0x80f1c : word) = Some W_80ed4.
Proof. vm_refl. Qed.
Lemma D_80ed4 : decode_any W_80ed4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ed8 : bv 32 := 0x00f8f7b3.
Lemma F_80ed8 : fetch_word AsanUbsan.M.loaded_segments (0x80f20 : word) = Some W_80ed8.
Proof. vm_refl. Qed.
Lemma D_80ed8 : decode_any W_80ed8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80edc : bv 32 := 0x00e6fa63.
Lemma F_80edc : fetch_word AsanUbsan.M.loaded_segments (0x80f24 : word) = Some W_80edc.
Proof. vm_refl. Qed.
Lemma D_80edc : decode_any W_80edc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ee0 : bv 32 := 0x0006c803.
Lemma F_80ee0 : fetch_word AsanUbsan.M.loaded_segments (0x80f28 : word) = Some W_80ee0.
Proof. vm_refl. Qed.
Lemma D_80ee0 : decode_any W_80ee0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ee4 : bv 32 := 0x00168693.
Lemma F_80ee4 : fetch_word AsanUbsan.M.loaded_segments (0x80f2c : word) = Some W_80ee4.
Proof. vm_refl. Qed.
Lemma D_80ee4 : decode_any W_80ee4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ee8 : bv 32 := 0x00f867b3.
Lemma F_80ee8 : fetch_word AsanUbsan.M.loaded_segments (0x80f30 : word) = Some W_80ee8.
Proof. vm_refl. Qed.
Lemma D_80ee8 : decode_any W_80ee8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80eec : bv 32 := 0xfee69ae3.
Lemma F_80eec : fetch_word AsanUbsan.M.loaded_segments (0x80f34 : word) = Some W_80eec.
Proof. vm_refl. Qed.
Lemma D_80eec : decode_any W_80eec = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ef0 : bv 32 := 0x0ff7f693.
Lemma F_80ef0 : fetch_word AsanUbsan.M.loaded_segments (0x80f38 : word) = Some W_80ef0.
Proof. vm_refl. Qed.
Lemma D_80ef0 : decode_any W_80ef0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ef4 : bv 32 := 0xcc0682e3.
Lemma F_80ef4 : fetch_word AsanUbsan.M.loaded_segments (0x80f3c : word) = Some W_80ef4.
Proof. vm_refl. Qed.
Lemma D_80ef4 : decode_any W_80ef4 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ef8 : bv 32 := 0x00050493.
Lemma F_80ef8 : fetch_word AsanUbsan.M.loaded_segments (0x80f40 : word) = Some W_80ef8.
Proof. vm_refl. Qed.
Lemma D_80ef8 : decode_any W_80ef8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80efc : bv 32 := 0x00058a93.
Lemma F_80efc : fetch_word AsanUbsan.M.loaded_segments (0x80f44 : word) = Some W_80efc.
Proof. vm_refl. Qed.
Lemma D_80efc : decode_any W_80efc = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f00 : bv 32 := 0x00060593.
Lemma F_80f00 : fetch_word AsanUbsan.M.loaded_segments (0x80f48 : word) = Some W_80f00.
Proof. vm_refl. Qed.
Lemma D_80f00 : decode_any W_80f00 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f04 : bv 32 := 0x00060913.
Lemma F_80f04 : fetch_word AsanUbsan.M.loaded_segments (0x80f4c : word) = Some W_80f04.
Proof. vm_refl. Qed.
Lemma D_80f04 : decode_any W_80f04 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f08 : bv 32 := 0x3ec030ef.
Lemma F_80f08 : fetch_word AsanUbsan.M.loaded_segments (0x80f50 : word) = Some W_80f08.
Proof. vm_refl. Qed.
Lemma D_80f08 : decode_any W_80f08 = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f0c : bv 32 := 0x000a8593.
Lemma F_80f0c : fetch_word AsanUbsan.M.loaded_segments (0x80f54 : word) = Some W_80f0c.
Proof. vm_refl. Qed.
Lemma D_80f0c : decode_any W_80f0c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f10 : bv 32 := 0x00090613.
Lemma F_80f10 : fetch_word AsanUbsan.M.loaded_segments (0x80f58 : word) = Some W_80f10.
Proof. vm_refl. Qed.
Lemma D_80f10 : decode_any W_80f10 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f14 : bv 32 := 0x00050993.
Lemma F_80f14 : fetch_word AsanUbsan.M.loaded_segments (0x80f5c : word) = Some W_80f14.
Proof. vm_refl. Qed.
Lemma D_80f14 : decode_any W_80f14 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f18 : bv 32 := 0x00048513.
Lemma F_80f18 : fetch_word AsanUbsan.M.loaded_segments (0x80f60 : word) = Some W_80f18.
Proof. vm_refl. Qed.
Lemma D_80f18 : decode_any W_80f18 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f1c : bv 32 := 0xc8098ee3.
Lemma F_80f1c : fetch_word AsanUbsan.M.loaded_segments (0x80f64 : word) = Some W_80f1c.
Proof. vm_refl. Qed.
Lemma D_80f1c : decode_any W_80f1c = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f64 : bv 32 := 0x81010113.
Lemma F_80f64 : fetch_word AsanUbsan.M.loaded_segments (0x80fac : word) = Some W_80f64.
Proof. vm_refl. Qed.
Lemma D_80f64 : decode_any W_80f64 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f68 : bv 32 := 0x7e113423.
Lemma F_80f68 : fetch_word AsanUbsan.M.loaded_segments (0x80fb0 : word) = Some W_80f68.
Proof. vm_refl. Qed.
Lemma D_80f68 : decode_any W_80f68 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f6c : bv 32 := 0x7e813023.
Lemma F_80f6c : fetch_word AsanUbsan.M.loaded_segments (0x80fb4 : word) = Some W_80f6c.
Proof. vm_refl. Qed.
Lemma D_80f6c : decode_any W_80f6c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f70 : bv 32 := 0x7c913c23.
Lemma F_80f70 : fetch_word AsanUbsan.M.loaded_segments (0x80fb8 : word) = Some W_80f70.
Proof. vm_refl. Qed.
Lemma D_80f70 : decode_any W_80f70 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f74 : bv 32 := 0x7d213823.
Lemma F_80f74 : fetch_word AsanUbsan.M.loaded_segments (0x80fbc : word) = Some W_80f74.
Proof. vm_refl. Qed.
Lemma D_80f74 : decode_any W_80f74 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f78 : bv 32 := 0x7d313423.
Lemma F_80f78 : fetch_word AsanUbsan.M.loaded_segments (0x80fc0 : word) = Some W_80f78.
Proof. vm_refl. Qed.
Lemma D_80f78 : decode_any W_80f78 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f7c : bv 32 := 0x7d413023.
Lemma F_80f7c : fetch_word AsanUbsan.M.loaded_segments (0x80fc4 : word) = Some W_80f7c.
Proof. vm_refl. Qed.
Lemma D_80f7c : decode_any W_80f7c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f80 : bv 32 := 0x7b513c23.
Lemma F_80f80 : fetch_word AsanUbsan.M.loaded_segments (0x80fc8 : word) = Some W_80f80.
Proof. vm_refl. Qed.
Lemma D_80f80 : decode_any W_80f80 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f84 : bv 32 := 0x7f010413.
Lemma F_80f84 : fetch_word AsanUbsan.M.loaded_segments (0x80fcc : word) = Some W_80f84.
Proof. vm_refl. Qed.
Lemma D_80f84 : decode_any W_80f84 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f88 : bv 32 := 0xfa010113.
Lemma F_80f88 : fetch_word AsanUbsan.M.loaded_segments (0x80fd0 : word) = Some W_80f88.
Proof. vm_refl. Qed.
Lemma D_80f88 : decode_any W_80f88 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f8c : bv 32 := 0x000e4697.
Lemma F_80f8c : fetch_word AsanUbsan.M.loaded_segments (0x80fd4 : word) = Some W_80f8c.
Proof. vm_refl. Qed.
Lemma D_80f8c : decode_any W_80f8c = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f90 : bv 32 := 0x0ac6b683.
Lemma F_80f90 : fetch_word AsanUbsan.M.loaded_segments (0x80fd8 : word) = Some W_80f90.
Proof. vm_refl. Qed.
Lemma D_80f90 : decode_any W_80f90 = Some (Load SZ8 true 13 13 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f94 : bv 32 := 0x0006c683.
Lemma F_80f94 : fetch_word AsanUbsan.M.loaded_segments (0x80fdc : word) = Some W_80f94.
Proof. vm_refl. Qed.
Lemma D_80f94 : decode_any W_80f94 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f98 : bv 32 := 0x08068863.
Lemma F_80f98 : fetch_word AsanUbsan.M.loaded_segments (0x80fe0 : word) = Some W_80f98.
Proof. vm_refl. Qed.
Lemma D_80f98 : decode_any W_80f98 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f9c : bv 32 := 0xfff54693.
Lemma F_80f9c : fetch_word AsanUbsan.M.loaded_segments (0x80fe4 : word) = Some W_80f9c.
Proof. vm_refl. Qed.
Lemma D_80f9c : decode_any W_80f9c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fa0 : bv 32 := 0x80040a13.
Lemma F_80fa0 : fetch_word AsanUbsan.M.loaded_segments (0x80fe8 : word) = Some W_80fa0.
Proof. vm_refl. Qed.
Lemma D_80fa0 : decode_any W_80fa0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fa4 : bv 32 := 0xfb0a0a13.
Lemma F_80fa4 : fetch_word AsanUbsan.M.loaded_segments (0x80fec : word) = Some W_80fa4.
Proof. vm_refl. Qed.
Lemma D_80fa4 : decode_any W_80fa4 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fa8 : bv 32 := 0x0cc6e663.
Lemma F_80fa8 : fetch_word AsanUbsan.M.loaded_segments (0x80ff0 : word) = Some W_80fa8.
Proof. vm_refl. Qed.
Lemma D_80fa8 : decode_any W_80fa8 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fac : bv 32 := 0xfbf60693.
Lemma F_80fac : fetch_word AsanUbsan.M.loaded_segments (0x80ff4 : word) = Some W_80fac.
Proof. vm_refl. Qed.
Lemma D_80fac : decode_any W_80fac = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fb0 : bv 32 := 0xfbf00713.
Lemma F_80fb0 : fetch_word AsanUbsan.M.loaded_segments (0x80ff8 : word) = Some W_80fb0.
Proof. vm_refl. Qed.
Lemma D_80fb0 : decode_any W_80fb0 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fb4 : bv 32 := 0x14d77463.
Lemma F_80fb4 : fetch_word AsanUbsan.M.loaded_segments (0x80ffc : word) = Some W_80fb4.
Proof. vm_refl. Qed.
Lemma D_80fb4 : decode_any W_80fb4 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fb8 : bv 32 := 0x000e3697.
Lemma F_80fb8 : fetch_word AsanUbsan.M.loaded_segments (0x81000 : word) = Some W_80fb8.
Proof. vm_refl. Qed.
Lemma D_80fb8 : decode_any W_80fb8 = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fbc : bv 32 := 0x5186b683.
Lemma F_80fbc : fetch_word AsanUbsan.M.loaded_segments (0x81004 : word) = Some W_80fbc.
Proof. vm_refl. Qed.
Lemma D_80fbc : decode_any W_80fbc = Some (Load SZ8 true 13 13 1304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fc0 : bv 32 := 0x00c507b3.
Lemma F_80fc0 : fetch_word AsanUbsan.M.loaded_segments (0x81008 : word) = Some W_80fc0.
Proof. vm_refl. Qed.
Lemma D_80fc0 : decode_any W_80fc0 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fc4 : bv 32 := 0x0006b703.
Lemma F_80fc4 : fetch_word AsanUbsan.M.loaded_segments (0x8100c : word) = Some W_80fc4.
Proof. vm_refl. Qed.
Lemma D_80fc4 : decode_any W_80fc4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fc8 : bv 32 := 0x00355693.
Lemma F_80fc8 : fetch_word AsanUbsan.M.loaded_segments (0x81010 : word) = Some W_80fc8.
Proof. vm_refl. Qed.
Lemma D_80fc8 : decode_any W_80fc8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fcc : bv 32 := 0xfff78793.
Lemma F_80fcc : fetch_word AsanUbsan.M.loaded_segments (0x81014 : word) = Some W_80fcc.
Proof. vm_refl. Qed.
Lemma D_80fcc : decode_any W_80fcc = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fd0 : bv 32 := 0x0037d813.
Lemma F_80fd0 : fetch_word AsanUbsan.M.loaded_segments (0x81018 : word) = Some W_80fd0.
Proof. vm_refl. Qed.
Lemma D_80fd0 : decode_any W_80fd0 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fd4 : bv 32 := 0x00d706b3.
Lemma F_80fd4 : fetch_word AsanUbsan.M.loaded_segments (0x8101c : word) = Some W_80fd4.
Proof. vm_refl. Qed.
Lemma D_80fd4 : decode_any W_80fd4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fd8 : bv 32 := 0x01070733.
Lemma F_80fd8 : fetch_word AsanUbsan.M.loaded_segments (0x81020 : word) = Some W_80fd8.
Proof. vm_refl. Qed.
Lemma D_80fd8 : decode_any W_80fd8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fdc : bv 32 := 0xff86f813.
Lemma F_80fdc : fetch_word AsanUbsan.M.loaded_segments (0x81024 : word) = Some W_80fdc.
Proof. vm_refl. Qed.
Lemma D_80fdc : decode_any W_80fdc = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fe0 : bv 32 := 0xff877893.
Lemma F_80fe0 : fetch_word AsanUbsan.M.loaded_segments (0x81028 : word) = Some W_80fe0.
Proof. vm_refl. Qed.
Lemma D_80fe0 : decode_any W_80fe0 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fe4 : bv 32 := 0x00083803.
Lemma F_80fe4 : fetch_word AsanUbsan.M.loaded_segments (0x8102c : word) = Some W_80fe4.
Proof. vm_refl. Qed.
Lemma D_80fe4 : decode_any W_80fe4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fe8 : bv 32 := 0x0008b883.
Lemma F_80fe8 : fetch_word AsanUbsan.M.loaded_segments (0x81030 : word) = Some W_80fe8.
Proof. vm_refl. Qed.
Lemma D_80fe8 : decode_any W_80fe8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fec : bv 32 := 0x0108e833.
Lemma F_80fec : fetch_word AsanUbsan.M.loaded_segments (0x81034 : word) = Some W_80fec.
Proof. vm_refl. Qed.
Lemma D_80fec : decode_any W_80fec = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ff0 : bv 32 := 0x10081a63.
Lemma F_80ff0 : fetch_word AsanUbsan.M.loaded_segments (0x81038 : word) = Some W_80ff0.
Proof. vm_refl. Qed.
Lemma D_80ff0 : decode_any W_80ff0 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ff4 : bv 32 := 0x000e5697.
Lemma F_80ff4 : fetch_word AsanUbsan.M.loaded_segments (0x8103c : word) = Some W_80ff4.
Proof. vm_refl. Qed.
Lemma D_80ff4 : decode_any W_80ff4 = Some (Auipc 13 229, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ff8 : bv 32 := 0x5146b683.
Lemma F_80ff8 : fetch_word AsanUbsan.M.loaded_segments (0x81040 : word) = Some W_80ff8.
Proof. vm_refl. Qed.
Lemma D_80ff8 : decode_any W_80ff8 = Some (Load SZ8 true 13 13 1300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ffc : bv 32 := 0x000680e7.
Lemma F_80ffc : fetch_word AsanUbsan.M.loaded_segments (0x81044 : word) = Some W_80ffc.
Proof. vm_refl. Qed.
Lemma D_80ffc : decode_any W_80ffc = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

