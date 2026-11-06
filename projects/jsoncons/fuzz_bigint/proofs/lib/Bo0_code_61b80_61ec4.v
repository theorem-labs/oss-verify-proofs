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

Definition W_61b80 : bv 32 := 0xfc010113.
Lemma F_61b80 : fetch_word AsanUbsan.M.loaded_segments (0x61b80 : word) = Some W_61b80.
Proof. vm_refl. Qed.
Lemma D_61b80 : decode_any W_61b80 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b84 : bv 32 := 0x02113c23.
Lemma F_61b84 : fetch_word AsanUbsan.M.loaded_segments (0x61b84 : word) = Some W_61b84.
Proof. vm_refl. Qed.
Lemma D_61b84 : decode_any W_61b84 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b88 : bv 32 := 0x02813823.
Lemma F_61b88 : fetch_word AsanUbsan.M.loaded_segments (0x61b88 : word) = Some W_61b88.
Proof. vm_refl. Qed.
Lemma D_61b88 : decode_any W_61b88 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b8c : bv 32 := 0x02913423.
Lemma F_61b8c : fetch_word AsanUbsan.M.loaded_segments (0x61b8c : word) = Some W_61b8c.
Proof. vm_refl. Qed.
Lemma D_61b8c : decode_any W_61b8c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b90 : bv 32 := 0x03213023.
Lemma F_61b90 : fetch_word AsanUbsan.M.loaded_segments (0x61b90 : word) = Some W_61b90.
Proof. vm_refl. Qed.
Lemma D_61b90 : decode_any W_61b90 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b94 : bv 32 := 0x01313c23.
Lemma F_61b94 : fetch_word AsanUbsan.M.loaded_segments (0x61b94 : word) = Some W_61b94.
Proof. vm_refl. Qed.
Lemma D_61b94 : decode_any W_61b94 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b98 : bv 32 := 0x01413823.
Lemma F_61b98 : fetch_word AsanUbsan.M.loaded_segments (0x61b98 : word) = Some W_61b98.
Proof. vm_refl. Qed.
Lemma D_61b98 : decode_any W_61b98 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b9c : bv 32 := 0x01513423.
Lemma F_61b9c : fetch_word AsanUbsan.M.loaded_segments (0x61b9c : word) = Some W_61b9c.
Proof. vm_refl. Qed.
Lemma D_61b9c : decode_any W_61b9c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ba0 : bv 32 := 0x14058c63.
Lemma F_61ba0 : fetch_word AsanUbsan.M.loaded_segments (0x61ba0 : word) = Some W_61ba0.
Proof. vm_refl. Qed.
Lemma D_61ba0 : decode_any W_61ba0 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ba4 : bv 32 := 0x00058493.
Lemma F_61ba4 : fetch_word AsanUbsan.M.loaded_segments (0x61ba4 : word) = Some W_61ba4.
Proof. vm_refl. Qed.
Lemma D_61ba4 : decode_any W_61ba4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ba8 : bv 32 := 0x00050413.
Lemma F_61ba8 : fetch_word AsanUbsan.M.loaded_segments (0x61ba8 : word) = Some W_61ba8.
Proof. vm_refl. Qed.
Lemma D_61ba8 : decode_any W_61ba8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bac : bv 32 := 0x00075517.
Lemma F_61bac : fetch_word AsanUbsan.M.loaded_segments (0x61bac : word) = Some W_61bac.
Proof. vm_refl. Qed.
Lemma D_61bac : decode_any W_61bac = Some (Auipc 10 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bb0 : bv 32 := 0x91c53a83.
Lemma F_61bb0 : fetch_word AsanUbsan.M.loaded_segments (0x61bb0 : word) = Some W_61bb0.
Proof. vm_refl. Qed.
Lemma D_61bb0 : decode_any W_61bb0 = Some (Load SZ8 true 21 10 2332, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bb4 : bv 32 := 0x000ab583.
Lemma F_61bb4 : fetch_word AsanUbsan.M.loaded_segments (0x61bb4 : word) = Some W_61bb4.
Proof. vm_refl. Qed.
Lemma D_61bb4 : decode_any W_61bb4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bb8 : bv 32 := 0xfff58513.
Lemma F_61bb8 : fetch_word AsanUbsan.M.loaded_segments (0x61bb8 : word) = Some W_61bb8.
Proof. vm_refl. Qed.
Lemma D_61bb8 : decode_any W_61bb8 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bbc : bv 32 := 0x00a5b633.
Lemma F_61bbc : fetch_word AsanUbsan.M.loaded_segments (0x61bbc : word) = Some W_61bbc.
Proof. vm_refl. Qed.
Lemma D_61bbc : decode_any W_61bbc = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bc0 : bv 32 := 0xfff60613.
Lemma F_61bc0 : fetch_word AsanUbsan.M.loaded_segments (0x61bc0 : word) = Some W_61bc0.
Proof. vm_refl. Qed.
Lemma D_61bc0 : decode_any W_61bc0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bc4 : bv 32 := 0x00a67633.
Lemma F_61bc4 : fetch_word AsanUbsan.M.loaded_segments (0x61bc4 : word) = Some W_61bc4.
Proof. vm_refl. Qed.
Lemma D_61bc4 : decode_any W_61bc4 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bc8 : bv 32 := 0x04867263.
Lemma F_61bc8 : fetch_word AsanUbsan.M.loaded_segments (0x61bc8 : word) = Some W_61bc8.
Proof. vm_refl. Qed.
Lemma D_61bc8 : decode_any W_61bc8 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bcc : bv 32 := 0x00075697.
Lemma F_61bcc : fetch_word AsanUbsan.M.loaded_segments (0x61bcc : word) = Some W_61bcc.
Proof. vm_refl. Qed.
Lemma D_61bcc : decode_any W_61bcc = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bd0 : bv 32 := 0x9046b683.
Lemma F_61bd0 : fetch_word AsanUbsan.M.loaded_segments (0x61bd0 : word) = Some W_61bd0.
Proof. vm_refl. Qed.
Lemma D_61bd0 : decode_any W_61bd0 = Some (Load SZ8 true 13 13 2308, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bd4 : bv 32 := 0x00075717.
Lemma F_61bd4 : fetch_word AsanUbsan.M.loaded_segments (0x61bd4 : word) = Some W_61bd4.
Proof. vm_refl. Qed.
Lemma D_61bd4 : decode_any W_61bd4 = Some (Auipc 14 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bd8 : bv 32 := 0x90473703.
Lemma F_61bd8 : fetch_word AsanUbsan.M.loaded_segments (0x61bd8 : word) = Some W_61bd8.
Proof. vm_refl. Qed.
Lemma D_61bd8 : decode_any W_61bd8 = Some (Load SZ8 true 14 14 2308, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bdc : bv 32 := 0x0006b803.
Lemma F_61bdc : fetch_word AsanUbsan.M.loaded_segments (0x61bdc : word) = Some W_61bdc.
Proof. vm_refl. Qed.
Lemma D_61bdc : decode_any W_61bdc = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61be0 : bv 32 := 0x00073683.
Lemma F_61be0 : fetch_word AsanUbsan.M.loaded_segments (0x61be0 : word) = Some W_61be0.
Proof. vm_refl. Qed.
Lemma D_61be0 : decode_any W_61be0 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61be4 : bv 32 := 0xfff80793.
Lemma F_61be4 : fetch_word AsanUbsan.M.loaded_segments (0x61be4 : word) = Some W_61be4.
Proof. vm_refl. Qed.
Lemma D_61be4 : decode_any W_61be4 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61be8 : bv 32 := 0x0087f463.
Lemma F_61be8 : fetch_word AsanUbsan.M.loaded_segments (0x61be8 : word) = Some W_61be8.
Proof. vm_refl. Qed.
Lemma D_61be8 : decode_any W_61be8 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bec : bv 32 := 0x0286f063.
Lemma F_61bec : fetch_word AsanUbsan.M.loaded_segments (0x61bec : word) = Some W_61bec.
Proof. vm_refl. Qed.
Lemma D_61bec : decode_any W_61bec = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bf0 : bv 32 := 0x00075717.
Lemma F_61bf0 : fetch_word AsanUbsan.M.loaded_segments (0x61bf0 : word) = Some W_61bf0.
Proof. vm_refl. Qed.
Lemma D_61bf0 : decode_any W_61bf0 = Some (Auipc 14 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bf4 : bv 32 := 0x8f073703.
Lemma F_61bf4 : fetch_word AsanUbsan.M.loaded_segments (0x61bf4 : word) = Some W_61bf4.
Proof. vm_refl. Qed.
Lemma D_61bf4 : decode_any W_61bf4 = Some (Load SZ8 true 14 14 2288, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bf8 : bv 32 := 0x00073283.
Lemma F_61bf8 : fetch_word AsanUbsan.M.loaded_segments (0x61bf8 : word) = Some W_61bf8.
Proof. vm_refl. Qed.
Lemma D_61bf8 : decode_any W_61bf8 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bfc : bv 32 := 0x0032d713.
Lemma F_61bfc : fetch_word AsanUbsan.M.loaded_segments (0x61bfc : word) = Some W_61bfc.
Proof. vm_refl. Qed.
Lemma D_61bfc : decode_any W_61bfc = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c00 : bv 32 := 0x00b708b3.
Lemma F_61c00 : fetch_word AsanUbsan.M.loaded_segments (0x61c00 : word) = Some W_61c00.
Proof. vm_refl. Qed.
Lemma D_61c00 : decode_any W_61c00 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c04 : bv 32 := 0x1282e063.
Lemma F_61c04 : fetch_word AsanUbsan.M.loaded_segments (0x61c04 : word) = Some W_61c04.
Proof. vm_refl. Qed.
Lemma D_61c04 : decode_any W_61c04 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c08 : bv 32 := 0x1088fe63.
Lemma F_61c08 : fetch_word AsanUbsan.M.loaded_segments (0x61c08 : word) = Some W_61c08.
Proof. vm_refl. Qed.
Lemma D_61c08 : decode_any W_61c08 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c0c : bv 32 := 0x00848933.
Lemma F_61c0c : fetch_word AsanUbsan.M.loaded_segments (0x61c0c : word) = Some W_61c0c.
Proof. vm_refl. Qed.
Lemma D_61c0c : decode_any W_61c0c = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c10 : bv 32 := 0x05267263.
Lemma F_61c10 : fetch_word AsanUbsan.M.loaded_segments (0x61c10 : word) = Some W_61c10.
Proof. vm_refl. Qed.
Lemma D_61c10 : decode_any W_61c10 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c14 : bv 32 := 0x00075617.
Lemma F_61c14 : fetch_word AsanUbsan.M.loaded_segments (0x61c14 : word) = Some W_61c14.
Proof. vm_refl. Qed.
Lemma D_61c14 : decode_any W_61c14 = Some (Auipc 12 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c18 : bv 32 := 0x8bc63603.
Lemma F_61c18 : fetch_word AsanUbsan.M.loaded_segments (0x61c18 : word) = Some W_61c18.
Proof. vm_refl. Qed.
Lemma D_61c18 : decode_any W_61c18 = Some (Load SZ8 true 12 12 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c1c : bv 32 := 0x00075697.
Lemma F_61c1c : fetch_word AsanUbsan.M.loaded_segments (0x61c1c : word) = Some W_61c1c.
Proof. vm_refl. Qed.
Lemma D_61c1c : decode_any W_61c1c = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c20 : bv 32 := 0x8bc6b683.
Lemma F_61c20 : fetch_word AsanUbsan.M.loaded_segments (0x61c20 : word) = Some W_61c20.
Proof. vm_refl. Qed.
Lemma D_61c20 : decode_any W_61c20 = Some (Load SZ8 true 13 13 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c24 : bv 32 := 0x00063783.
Lemma F_61c24 : fetch_word AsanUbsan.M.loaded_segments (0x61c24 : word) = Some W_61c24.
Proof. vm_refl. Qed.
Lemma D_61c24 : decode_any W_61c24 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c28 : bv 32 := 0x0006b603.
Lemma F_61c28 : fetch_word AsanUbsan.M.loaded_segments (0x61c28 : word) = Some W_61c28.
Proof. vm_refl. Qed.
Lemma D_61c28 : decode_any W_61c28 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c2c : bv 32 := 0xfff78713.
Lemma F_61c2c : fetch_word AsanUbsan.M.loaded_segments (0x61c2c : word) = Some W_61c2c.
Proof. vm_refl. Qed.
Lemma D_61c2c : decode_any W_61c2c = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c30 : bv 32 := 0x01277463.
Lemma F_61c30 : fetch_word AsanUbsan.M.loaded_segments (0x61c30 : word) = Some W_61c30.
Proof. vm_refl. Qed.
Lemma D_61c30 : decode_any W_61c30 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c34 : bv 32 := 0x03267063.
Lemma F_61c34 : fetch_word AsanUbsan.M.loaded_segments (0x61c34 : word) = Some W_61c34.
Proof. vm_refl. Qed.
Lemma D_61c34 : decode_any W_61c34 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c38 : bv 32 := 0x00075697.
Lemma F_61c38 : fetch_word AsanUbsan.M.loaded_segments (0x61c38 : word) = Some W_61c38.
Proof. vm_refl. Qed.
Lemma D_61c38 : decode_any W_61c38 = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c3c : bv 32 := 0x8a86b683.
Lemma F_61c3c : fetch_word AsanUbsan.M.loaded_segments (0x61c3c : word) = Some W_61c3c.
Proof. vm_refl. Qed.
Lemma D_61c3c : decode_any W_61c3c = Some (Load SZ8 true 13 13 2216, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c40 : bv 32 := 0x0006b883.
Lemma F_61c40 : fetch_word AsanUbsan.M.loaded_segments (0x61c40 : word) = Some W_61c40.
Proof. vm_refl. Qed.
Lemma D_61c40 : decode_any W_61c40 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c44 : bv 32 := 0x0038d693.
Lemma F_61c44 : fetch_word AsanUbsan.M.loaded_segments (0x61c44 : word) = Some W_61c44.
Proof. vm_refl. Qed.
Lemma D_61c44 : decode_any W_61c44 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c48 : bv 32 := 0x00b68833.
Lemma F_61c48 : fetch_word AsanUbsan.M.loaded_segments (0x61c48 : word) = Some W_61c48.
Proof. vm_refl. Qed.
Lemma D_61c48 : decode_any W_61c48 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c4c : bv 32 := 0x1328e463.
Lemma F_61c4c : fetch_word AsanUbsan.M.loaded_segments (0x61c4c : word) = Some W_61c4c.
Proof. vm_refl. Qed.
Lemma D_61c4c : decode_any W_61c4c = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c50 : bv 32 := 0x13287263.
Lemma F_61c50 : fetch_word AsanUbsan.M.loaded_segments (0x61c50 : word) = Some W_61c50.
Proof. vm_refl. Qed.
Lemma D_61c50 : decode_any W_61c50 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c54 : bv 32 := 0x23247863.
Lemma F_61c54 : fetch_word AsanUbsan.M.loaded_segments (0x61c54 : word) = Some W_61c54.
Proof. vm_refl. Qed.
Lemma D_61c54 : decode_any W_61c54 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c58 : bv 32 := 0x00740513.
Lemma F_61c58 : fetch_word AsanUbsan.M.loaded_segments (0x61c58 : word) = Some W_61c58.
Proof. vm_refl. Qed.
Lemma D_61c58 : decode_any W_61c58 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c5c : bv 32 := 0xff857513.
Lemma F_61c5c : fetch_word AsanUbsan.M.loaded_segments (0x61c5c : word) = Some W_61c5c.
Proof. vm_refl. Qed.
Lemma D_61c5c : decode_any W_61c5c = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c60 : bv 32 := 0xff897a13.
Lemma F_61c60 : fetch_word AsanUbsan.M.loaded_segments (0x61c60 : word) = Some W_61c60.
Proof. vm_refl. Qed.
Lemma D_61c60 : decode_any W_61c60 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c64 : bv 32 := 0xa91ff0ef.
Lemma F_61c64 : fetch_word AsanUbsan.M.loaded_segments (0x61c64 : word) = Some W_61c64.
Proof. vm_refl. Qed.
Lemma D_61c64 : decode_any W_61c64 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c68 : bv 32 := 0x00050993.
Lemma F_61c68 : fetch_word AsanUbsan.M.loaded_segments (0x61c68 : word) = Some W_61c68.
Proof. vm_refl. Qed.
Lemma D_61c68 : decode_any W_61c68 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c6c : bv 32 := 0x000a0513.
Lemma F_61c6c : fetch_word AsanUbsan.M.loaded_segments (0x61c6c : word) = Some W_61c6c.
Proof. vm_refl. Qed.
Lemma D_61c6c : decode_any W_61c6c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c70 : bv 32 := 0xa85ff0ef.
Lemma F_61c70 : fetch_word AsanUbsan.M.loaded_segments (0x61c70 : word) = Some W_61c70.
Proof. vm_refl. Qed.
Lemma D_61c70 : decode_any W_61c70 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c74 : bv 32 := 0x000ab583.
Lemma F_61c74 : fetch_word AsanUbsan.M.loaded_segments (0x61c74 : word) = Some W_61c74.
Proof. vm_refl. Qed.
Lemma D_61c74 : decode_any W_61c74 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c78 : bv 32 := 0x00345613.
Lemma F_61c78 : fetch_word AsanUbsan.M.loaded_segments (0x61c78 : word) = Some W_61c78.
Proof. vm_refl. Qed.
Lemma D_61c78 : decode_any W_61c78 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c7c : bv 32 := 0x00c58633.
Lemma F_61c7c : fetch_word AsanUbsan.M.loaded_segments (0x61c7c : word) = Some W_61c7c.
Proof. vm_refl. Qed.
Lemma D_61c7c : decode_any W_61c7c = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c80 : bv 32 := 0x00060603.
Lemma F_61c80 : fetch_word AsanUbsan.M.loaded_segments (0x61c80 : word) = Some W_61c80.
Proof. vm_refl. Qed.
Lemma D_61c80 : decode_any W_61c80 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c84 : bv 32 := 0x00060663.
Lemma F_61c84 : fetch_word AsanUbsan.M.loaded_segments (0x61c84 : word) = Some W_61c84.
Proof. vm_refl. Qed.
Lemma D_61c84 : decode_any W_61c84 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c88 : bv 32 := 0x00747693.
Lemma F_61c88 : fetch_word AsanUbsan.M.loaded_segments (0x61c88 : word) = Some W_61c88.
Proof. vm_refl. Qed.
Lemma D_61c88 : decode_any W_61c88 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c8c : bv 32 := 0x02c6d063.
Lemma F_61c8c : fetch_word AsanUbsan.M.loaded_segments (0x61c8c : word) = Some W_61c8c.
Proof. vm_refl. Qed.
Lemma D_61c8c : decode_any W_61c8c = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c90 : bv 32 := 0xfff90913.
Lemma F_61c90 : fetch_word AsanUbsan.M.loaded_segments (0x61c90 : word) = Some W_61c90.
Proof. vm_refl. Qed.
Lemma D_61c90 : decode_any W_61c90 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c94 : bv 32 := 0x00395613.
Lemma F_61c94 : fetch_word AsanUbsan.M.loaded_segments (0x61c94 : word) = Some W_61c94.
Proof. vm_refl. Qed.
Lemma D_61c94 : decode_any W_61c94 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c98 : bv 32 := 0x00c585b3.
Lemma F_61c98 : fetch_word AsanUbsan.M.loaded_segments (0x61c98 : word) = Some W_61c98.
Proof. vm_refl. Qed.
Lemma D_61c98 : decode_any W_61c98 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c9c : bv 32 := 0x00058583.
Lemma F_61c9c : fetch_word AsanUbsan.M.loaded_segments (0x61c9c : word) = Some W_61c9c.
Proof. vm_refl. Qed.
Lemma D_61c9c : decode_any W_61c9c = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ca0 : bv 32 := 0x04058263.
Lemma F_61ca0 : fetch_word AsanUbsan.M.loaded_segments (0x61ca0 : word) = Some W_61ca0.
Proof. vm_refl. Qed.
Lemma D_61ca0 : decode_any W_61ca0 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ca4 : bv 32 := 0x00797613.
Lemma F_61ca4 : fetch_word AsanUbsan.M.loaded_segments (0x61ca4 : word) = Some W_61ca4.
Proof. vm_refl. Qed.
Lemma D_61ca4 : decode_any W_61ca4 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ca8 : bv 32 := 0x02b64e63.
Lemma F_61ca8 : fetch_word AsanUbsan.M.loaded_segments (0x61ca8 : word) = Some W_61ca8.
Proof. vm_refl. Qed.
Lemma D_61ca8 : decode_any W_61ca8 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cac : bv 32 := 0x000ab503.
Lemma F_61cac : fetch_word AsanUbsan.M.loaded_segments (0x61cac : word) = Some W_61cac.
Proof. vm_refl. Qed.
Lemma D_61cac : decode_any W_61cac = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cb0 : bv 32 := 0x00040593.
Lemma F_61cb0 : fetch_word AsanUbsan.M.loaded_segments (0x61cb0 : word) = Some W_61cb0.
Proof. vm_refl. Qed.
Lemma D_61cb0 : decode_any W_61cb0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cb4 : bv 32 := 0x0140006f.
Lemma F_61cb4 : fetch_word AsanUbsan.M.loaded_segments (0x61cb4 : word) = Some W_61cb4.
Proof. vm_refl. Qed.
Lemma D_61cb4 : decode_any W_61cb4 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cb8 : bv 32 := 0x00140413.
Lemma F_61cb8 : fetch_word AsanUbsan.M.loaded_segments (0x61cb8 : word) = Some W_61cb8.
Proof. vm_refl. Qed.
Lemma D_61cb8 : decode_any W_61cb8 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cbc : bv 32 := 0xfff48493.
Lemma F_61cbc : fetch_word AsanUbsan.M.loaded_segments (0x61cbc : word) = Some W_61cbc.
Proof. vm_refl. Qed.
Lemma D_61cbc : decode_any W_61cbc = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cc0 : bv 32 := 0x00158593.
Lemma F_61cc0 : fetch_word AsanUbsan.M.loaded_segments (0x61cc0 : word) = Some W_61cc0.
Proof. vm_refl. Qed.
Lemma D_61cc0 : decode_any W_61cc0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cc4 : bv 32 := 0x1e048063.
Lemma F_61cc4 : fetch_word AsanUbsan.M.loaded_segments (0x61cc4 : word) = Some W_61cc4.
Proof. vm_refl. Qed.
Lemma D_61cc4 : decode_any W_61cc4 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cc8 : bv 32 := 0x00345613.
Lemma F_61cc8 : fetch_word AsanUbsan.M.loaded_segments (0x61cc8 : word) = Some W_61cc8.
Proof. vm_refl. Qed.
Lemma D_61cc8 : decode_any W_61cc8 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ccc : bv 32 := 0x00c50633.
Lemma F_61ccc : fetch_word AsanUbsan.M.loaded_segments (0x61ccc : word) = Some W_61ccc.
Proof. vm_refl. Qed.
Lemma D_61ccc : decode_any W_61ccc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cd0 : bv 32 := 0x00060603.
Lemma F_61cd0 : fetch_word AsanUbsan.M.loaded_segments (0x61cd0 : word) = Some W_61cd0.
Proof. vm_refl. Qed.
Lemma D_61cd0 : decode_any W_61cd0 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cd4 : bv 32 := 0xfe0602e3.
Lemma F_61cd4 : fetch_word AsanUbsan.M.loaded_segments (0x61cd4 : word) = Some W_61cd4.
Proof. vm_refl. Qed.
Lemma D_61cd4 : decode_any W_61cd4 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cd8 : bv 32 := 0x0075f693.
Lemma F_61cd8 : fetch_word AsanUbsan.M.loaded_segments (0x61cd8 : word) = Some W_61cd8.
Proof. vm_refl. Qed.
Lemma D_61cd8 : decode_any W_61cd8 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cdc : bv 32 := 0xfcc6cee3.
Lemma F_61cdc : fetch_word AsanUbsan.M.loaded_segments (0x61cdc : word) = Some W_61cdc.
Proof. vm_refl. Qed.
Lemma D_61cdc : decode_any W_61cdc = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ce0 : bv 32 := 0x01c0006f.
Lemma F_61ce0 : fetch_word AsanUbsan.M.loaded_segments (0x61ce0 : word) = Some W_61ce0.
Proof. vm_refl. Qed.
Lemma D_61ce0 : decode_any W_61ce0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ce4 : bv 32 := 0x00a9fa63.
Lemma F_61ce4 : fetch_word AsanUbsan.M.loaded_segments (0x61ce4 : word) = Some W_61ce4.
Proof. vm_refl. Qed.
Lemma D_61ce4 : decode_any W_61ce4 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ce8 : bv 32 := 0x413505b3.
Lemma F_61ce8 : fetch_word AsanUbsan.M.loaded_segments (0x61ce8 : word) = Some W_61ce8.
Proof. vm_refl. Qed.
Lemma D_61ce8 : decode_any W_61ce8 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cec : bv 32 := 0x00098513.
Lemma F_61cec : fetch_word AsanUbsan.M.loaded_segments (0x61cec : word) = Some W_61cec.
Proof. vm_refl. Qed.
Lemma D_61cec : decode_any W_61cec = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cf0 : bv 32 := 0x6210f0ef.
Lemma F_61cf0 : fetch_word AsanUbsan.M.loaded_segments (0x61cf0 : word) = Some W_61cf0.
Proof. vm_refl. Qed.
Lemma D_61cf0 : decode_any W_61cf0 = Some (Jal 1 65056, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cf4 : bv 32 := 0xfa050ce3.
Lemma F_61cf4 : fetch_word AsanUbsan.M.loaded_segments (0x61cf4 : word) = Some W_61cf4.
Proof. vm_refl. Qed.
Lemma D_61cf4 : decode_any W_61cf4 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cf8 : bv 32 := 0x00000413.
Lemma F_61cf8 : fetch_word AsanUbsan.M.loaded_segments (0x61cf8 : word) = Some W_61cf8.
Proof. vm_refl. Qed.
Lemma D_61cf8 : decode_any W_61cf8 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61cfc : bv 32 := 0x00040513.
Lemma F_61cfc : fetch_word AsanUbsan.M.loaded_segments (0x61cfc : word) = Some W_61cfc.
Proof. vm_refl. Qed.
Lemma D_61cfc : decode_any W_61cfc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d00 : bv 32 := 0x03813083.
Lemma F_61d00 : fetch_word AsanUbsan.M.loaded_segments (0x61d00 : word) = Some W_61d00.
Proof. vm_refl. Qed.
Lemma D_61d00 : decode_any W_61d00 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d04 : bv 32 := 0x03013403.
Lemma F_61d04 : fetch_word AsanUbsan.M.loaded_segments (0x61d04 : word) = Some W_61d04.
Proof. vm_refl. Qed.
Lemma D_61d04 : decode_any W_61d04 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d08 : bv 32 := 0x02813483.
Lemma F_61d08 : fetch_word AsanUbsan.M.loaded_segments (0x61d08 : word) = Some W_61d08.
Proof. vm_refl. Qed.
Lemma D_61d08 : decode_any W_61d08 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d0c : bv 32 := 0x02013903.
Lemma F_61d0c : fetch_word AsanUbsan.M.loaded_segments (0x61d0c : word) = Some W_61d0c.
Proof. vm_refl. Qed.
Lemma D_61d0c : decode_any W_61d0c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d10 : bv 32 := 0x01813983.
Lemma F_61d10 : fetch_word AsanUbsan.M.loaded_segments (0x61d10 : word) = Some W_61d10.
Proof. vm_refl. Qed.
Lemma D_61d10 : decode_any W_61d10 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d14 : bv 32 := 0x01013a03.
Lemma F_61d14 : fetch_word AsanUbsan.M.loaded_segments (0x61d14 : word) = Some W_61d14.
Proof. vm_refl. Qed.
Lemma D_61d14 : decode_any W_61d14 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d18 : bv 32 := 0x00813a83.
Lemma F_61d18 : fetch_word AsanUbsan.M.loaded_segments (0x61d18 : word) = Some W_61d18.
Proof. vm_refl. Qed.
Lemma D_61d18 : decode_any W_61d18 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d1c : bv 32 := 0x04010113.
Lemma F_61d1c : fetch_word AsanUbsan.M.loaded_segments (0x61d1c : word) = Some W_61d1c.
Proof. vm_refl. Qed.
Lemma D_61d1c : decode_any W_61d1c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d20 : bv 32 := 0x00008067.
Lemma F_61d20 : fetch_word AsanUbsan.M.loaded_segments (0x61d20 : word) = Some W_61d20.
Proof. vm_refl. Qed.
Lemma D_61d20 : decode_any W_61d20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d24 : bv 32 := 0x00074297.
Lemma F_61d24 : fetch_word AsanUbsan.M.loaded_segments (0x61d24 : word) = Some W_61d24.
Proof. vm_refl. Qed.
Lemma D_61d24 : decode_any W_61d24 = Some (Auipc 5 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d28 : bv 32 := 0x79c2b283.
Lemma F_61d28 : fetch_word AsanUbsan.M.loaded_segments (0x61d28 : word) = Some W_61d28.
Proof. vm_refl. Qed.
Lemma D_61d28 : decode_any W_61d28 = Some (Load SZ8 true 5 5 1948, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d2c : bv 32 := 0x04e2c283.
Lemma F_61d2c : fetch_word AsanUbsan.M.loaded_segments (0x61d2c : word) = Some W_61d2c.
Proof. vm_refl. Qed.
Lemma D_61d2c : decode_any W_61d2c = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d30 : bv 32 := 0xfc0296e3.
Lemma F_61d30 : fetch_word AsanUbsan.M.loaded_segments (0x61d30 : word) = Some W_61d30.
Proof. vm_refl. Qed.
Lemma D_61d30 : decode_any W_61d30 = Some (Branch BC_NE 5 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d34 : bv 32 := 0x08080c63.
Lemma F_61d34 : fetch_word AsanUbsan.M.loaded_segments (0x61d34 : word) = Some W_61d34.
Proof. vm_refl. Qed.
Lemma D_61d34 : decode_any W_61d34 = Some (Branch BC_EQ 16 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d38 : bv 32 := 0x00385813.
Lemma F_61d38 : fetch_word AsanUbsan.M.loaded_segments (0x61d38 : word) = Some W_61d38.
Proof. vm_refl. Qed.
Lemma D_61d38 : decode_any W_61d38 = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d3c : bv 32 := 0x00a80833.
Lemma F_61d3c : fetch_word AsanUbsan.M.loaded_segments (0x61d3c : word) = Some W_61d3c.
Proof. vm_refl. Qed.
Lemma D_61d3c : decode_any W_61d3c = Some (Op ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d40 : bv 32 := 0x0e887263.
Lemma F_61d40 : fetch_word AsanUbsan.M.loaded_segments (0x61d40 : word) = Some W_61d40.
Proof. vm_refl. Qed.
Lemma D_61d40 : decode_any W_61d40 = Some (Branch BC_GEU 16 8 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d44 : bv 32 := 0x00158813.
Lemma F_61d44 : fetch_word AsanUbsan.M.loaded_segments (0x61d44 : word) = Some W_61d44.
Proof. vm_refl. Qed.
Lemma D_61d44 : decode_any W_61d44 = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d48 : bv 32 := 0x0087e863.
Lemma F_61d48 : fetch_word AsanUbsan.M.loaded_segments (0x61d48 : word) = Some W_61d48.
Proof. vm_refl. Qed.
Lemma D_61d48 : decode_any W_61d48 = Some (Branch BC_LTU 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d4c : bv 32 := 0x0036d793.
Lemma F_61d4c : fetch_word AsanUbsan.M.loaded_segments (0x61d4c : word) = Some W_61d4c.
Proof. vm_refl. Qed.
Lemma D_61d4c : decode_any W_61d4c = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d50 : bv 32 := 0x010787b3.
Lemma F_61d50 : fetch_word AsanUbsan.M.loaded_segments (0x61d50 : word) = Some W_61d50.
Proof. vm_refl. Qed.
Lemma D_61d50 : decode_any W_61d50 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d54 : bv 32 := 0xeaf47ce3.
Lemma F_61d54 : fetch_word AsanUbsan.M.loaded_segments (0x61d54 : word) = Some W_61d54.
Proof. vm_refl. Qed.
Lemma D_61d54 : decode_any W_61d54 = Some (Branch BC_GEU 8 15 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d58 : bv 32 := 0x00168693.
Lemma F_61d58 : fetch_word AsanUbsan.M.loaded_segments (0x61d58 : word) = Some W_61d58.
Proof. vm_refl. Qed.
Lemma D_61d58 : decode_any W_61d58 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d5c : bv 32 := 0xfad460e3.
Lemma F_61d5c : fetch_word AsanUbsan.M.loaded_segments (0x61d5c : word) = Some W_61d5c.
Proof. vm_refl. Qed.
Lemma D_61d5c : decode_any W_61d5c = Some (Branch BC_LTU 8 13 8096, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d60 : bv 32 := 0x01070733.
Lemma F_61d60 : fetch_word AsanUbsan.M.loaded_segments (0x61d60 : word) = Some W_61d60.
Proof. vm_refl. Qed.
Lemma D_61d60 : decode_any W_61d60 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d64 : bv 32 := 0x00375713.
Lemma F_61d64 : fetch_word AsanUbsan.M.loaded_segments (0x61d64 : word) = Some W_61d64.
Proof. vm_refl. Qed.
Lemma D_61d64 : decode_any W_61d64 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d68 : bv 32 := 0x00a70733.
Lemma F_61d68 : fetch_word AsanUbsan.M.loaded_segments (0x61d68 : word) = Some W_61d68.
Proof. vm_refl. Qed.
Lemma D_61d68 : decode_any W_61d68 = Some (Op ALU_ADD 14 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d6c : bv 32 := 0xea8770e3.
Lemma F_61d6c : fetch_word AsanUbsan.M.loaded_segments (0x61d6c : word) = Some W_61d6c.
Proof. vm_refl. Qed.
Lemma D_61d6c : decode_any W_61d6c = Some (Branch BC_GEU 14 8 7840, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d70 : bv 32 := 0xf8dff06f.
Lemma F_61d70 : fetch_word AsanUbsan.M.loaded_segments (0x61d70 : word) = Some W_61d70.
Proof. vm_refl. Qed.
Lemma D_61d70 : decode_any W_61d70 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d74 : bv 32 := 0x00074897.
Lemma F_61d74 : fetch_word AsanUbsan.M.loaded_segments (0x61d74 : word) = Some W_61d74.
Proof. vm_refl. Qed.
Lemma D_61d74 : decode_any W_61d74 = Some (Auipc 17 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d78 : bv 32 := 0x74c8b883.
Lemma F_61d78 : fetch_word AsanUbsan.M.loaded_segments (0x61d78 : word) = Some W_61d78.
Proof. vm_refl. Qed.
Lemma D_61d78 : decode_any W_61d78 = Some (Load SZ8 true 17 17 1868, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d7c : bv 32 := 0x04e8c883.
Lemma F_61d7c : fetch_word AsanUbsan.M.loaded_segments (0x61d7c : word) = Some W_61d7c.
Proof. vm_refl. Qed.
Lemma D_61d7c : decode_any W_61d7c = Some (Load SZ1 false 17 17 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d80 : bv 32 := 0x00088663.
Lemma F_61d80 : fetch_word AsanUbsan.M.loaded_segments (0x61d80 : word) = Some W_61d80.
Proof. vm_refl. Qed.
Lemma D_61d80 : decode_any W_61d80 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d84 : bv 32 := 0x00090413.
Lemma F_61d84 : fetch_word AsanUbsan.M.loaded_segments (0x61d84 : word) = Some W_61d84.
Proof. vm_refl. Qed.
Lemma D_61d84 : decode_any W_61d84 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d88 : bv 32 := 0xf75ff06f.
Lemma F_61d88 : fetch_word AsanUbsan.M.loaded_segments (0x61d88 : word) = Some W_61d88.
Proof. vm_refl. Qed.
Lemma D_61d88 : decode_any W_61d88 = Some (Jal 0 2097012, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d8c : bv 32 := 0x06078663.
Lemma F_61d8c : fetch_word AsanUbsan.M.loaded_segments (0x61d8c : word) = Some W_61d8c.
Proof. vm_refl. Qed.
Lemma D_61d8c : decode_any W_61d8c = Some (Branch BC_EQ 15 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d90 : bv 32 := 0x0037d793.
Lemma F_61d90 : fetch_word AsanUbsan.M.loaded_segments (0x61d90 : word) = Some W_61d90.
Proof. vm_refl. Qed.
Lemma D_61d90 : decode_any W_61d90 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d94 : bv 32 := 0x00a787b3.
Lemma F_61d94 : fetch_word AsanUbsan.M.loaded_segments (0x61d94 : word) = Some W_61d94.
Proof. vm_refl. Qed.
Lemma D_61d94 : decode_any W_61d94 = Some (Op ALU_ADD 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d98 : bv 32 := 0x0b27f463.
Lemma F_61d98 : fetch_word AsanUbsan.M.loaded_segments (0x61d98 : word) = Some W_61d98.
Proof. vm_refl. Qed.
Lemma D_61d98 : decode_any W_61d98 = Some (Branch BC_GEU 15 18 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_61d9c : bv 32 := 0x00158593.
Lemma F_61d9c : fetch_word AsanUbsan.M.loaded_segments (0x61d9c : word) = Some W_61d9c.
Proof. vm_refl. Qed.
Lemma D_61d9c : decode_any W_61d9c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61da0 : bv 32 := 0x01276863.
Lemma F_61da0 : fetch_word AsanUbsan.M.loaded_segments (0x61da0 : word) = Some W_61da0.
Proof. vm_refl. Qed.
Lemma D_61da0 : decode_any W_61da0 = Some (Branch BC_LTU 14 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61da4 : bv 32 := 0x00365713.
Lemma F_61da4 : fetch_word AsanUbsan.M.loaded_segments (0x61da4 : word) = Some W_61da4.
Proof. vm_refl. Qed.
Lemma D_61da4 : decode_any W_61da4 = Some (ShiftImm ALU_SRL 14 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61da8 : bv 32 := 0x00b70733.
Lemma F_61da8 : fetch_word AsanUbsan.M.loaded_segments (0x61da8 : word) = Some W_61da8.
Proof. vm_refl. Qed.
Lemma D_61da8 : decode_any W_61da8 = Some (Op ALU_ADD 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dac : bv 32 := 0xeae974e3.
Lemma F_61dac : fetch_word AsanUbsan.M.loaded_segments (0x61dac : word) = Some W_61dac.
Proof. vm_refl. Qed.
Lemma D_61dac : decode_any W_61dac = Some (Branch BC_GEU 18 14 7848, 4%Z).
Proof. vm_refl. Qed.

Definition W_61db0 : bv 32 := 0x00160613.
Lemma F_61db0 : fetch_word AsanUbsan.M.loaded_segments (0x61db0 : word) = Some W_61db0.
Proof. vm_refl. Qed.
Lemma D_61db0 : decode_any W_61db0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61db4 : bv 32 := 0xfcc968e3.
Lemma F_61db4 : fetch_word AsanUbsan.M.loaded_segments (0x61db4 : word) = Some W_61db4.
Proof. vm_refl. Qed.
Lemma D_61db4 : decode_any W_61db4 = Some (Branch BC_LTU 18 12 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_61db8 : bv 32 := 0x00b685b3.
Lemma F_61db8 : fetch_word AsanUbsan.M.loaded_segments (0x61db8 : word) = Some W_61db8.
Proof. vm_refl. Qed.
Lemma D_61db8 : decode_any W_61db8 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dbc : bv 32 := 0x0035d593.
Lemma F_61dbc : fetch_word AsanUbsan.M.loaded_segments (0x61dbc : word) = Some W_61dbc.
Proof. vm_refl. Qed.
Lemma D_61dbc : decode_any W_61dbc = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dc0 : bv 32 := 0x00a58533.
Lemma F_61dc0 : fetch_word AsanUbsan.M.loaded_segments (0x61dc0 : word) = Some W_61dc0.
Proof. vm_refl. Qed.
Lemma D_61dc0 : decode_any W_61dc0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dc4 : bv 32 := 0xe92578e3.
Lemma F_61dc4 : fetch_word AsanUbsan.M.loaded_segments (0x61dc4 : word) = Some W_61dc4.
Proof. vm_refl. Qed.
Lemma D_61dc4 : decode_any W_61dc4 = Some (Branch BC_GEU 10 18 7824, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dc8 : bv 32 := 0xfbdff06f.
Lemma F_61dc8 : fetch_word AsanUbsan.M.loaded_segments (0x61dc8 : word) = Some W_61dc8.
Proof. vm_refl. Qed.
Lemma D_61dc8 : decode_any W_61dc8 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dcc : bv 32 := 0x08058863.
Lemma F_61dcc : fetch_word AsanUbsan.M.loaded_segments (0x61dcc : word) = Some W_61dcc.
Proof. vm_refl. Qed.
Lemma D_61dcc : decode_any W_61dcc = Some (Branch BC_EQ 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dd0 : bv 32 := 0x00355693.
Lemma F_61dd0 : fetch_word AsanUbsan.M.loaded_segments (0x61dd0 : word) = Some W_61dd0.
Proof. vm_refl. Qed.
Lemma D_61dd0 : decode_any W_61dd0 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dd4 : bv 32 := 0x00b686b3.
Lemma F_61dd4 : fetch_word AsanUbsan.M.loaded_segments (0x61dd4 : word) = Some W_61dd4.
Proof. vm_refl. Qed.
Lemma D_61dd4 : decode_any W_61dd4 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dd8 : bv 32 := 0x00068663.
Lemma F_61dd8 : fetch_word AsanUbsan.M.loaded_segments (0x61dd8 : word) = Some W_61dd8.
Proof. vm_refl. Qed.
Lemma D_61dd8 : decode_any W_61dd8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ddc : bv 32 := 0x00168693.
Lemma F_61ddc : fetch_word AsanUbsan.M.loaded_segments (0x61ddc : word) = Some W_61ddc.
Proof. vm_refl. Qed.
Lemma D_61ddc : decode_any W_61ddc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61de0 : bv 32 := 0xf0d46ee3.
Lemma F_61de0 : fetch_word AsanUbsan.M.loaded_segments (0x61de0 : word) = Some W_61de0.
Proof. vm_refl. Qed.
Lemma D_61de0 : decode_any W_61de0 = Some (Branch BC_LTU 8 13 7964, 4%Z).
Proof. vm_refl. Qed.

Definition W_61de4 : bv 32 := 0x00188893.
Lemma F_61de4 : fetch_word AsanUbsan.M.loaded_segments (0x61de4 : word) = Some W_61de4.
Proof. vm_refl. Qed.
Lemma D_61de4 : decode_any W_61de4 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61de8 : bv 32 := 0x0038d693.
Lemma F_61de8 : fetch_word AsanUbsan.M.loaded_segments (0x61de8 : word) = Some W_61de8.
Proof. vm_refl. Qed.
Lemma D_61de8 : decode_any W_61de8 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dec : bv 32 := 0x00a686b3.
Lemma F_61dec : fetch_word AsanUbsan.M.loaded_segments (0x61dec : word) = Some W_61dec.
Proof. vm_refl. Qed.
Lemma D_61dec : decode_any W_61dec = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61df0 : bv 32 := 0xe086fee3.
Lemma F_61df0 : fetch_word AsanUbsan.M.loaded_segments (0x61df0 : word) = Some W_61df0.
Proof. vm_refl. Qed.
Lemma D_61df0 : decode_any W_61df0 = Some (Branch BC_GEU 13 8 7708, 4%Z).
Proof. vm_refl. Qed.

Definition W_61df4 : bv 32 := 0xf09ff06f.
Lemma F_61df4 : fetch_word AsanUbsan.M.loaded_segments (0x61df4 : word) = Some W_61df4.
Proof. vm_refl. Qed.
Lemma D_61df4 : decode_any W_61df4 = Some (Jal 0 2096904, 4%Z).
Proof. vm_refl. Qed.

Definition W_61df8 : bv 32 := 0x06058c63.
Lemma F_61df8 : fetch_word AsanUbsan.M.loaded_segments (0x61df8 : word) = Some W_61df8.
Proof. vm_refl. Qed.
Lemma D_61df8 : decode_any W_61df8 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_61dfc : bv 32 := 0x00355613.
Lemma F_61dfc : fetch_word AsanUbsan.M.loaded_segments (0x61dfc : word) = Some W_61dfc.
Proof. vm_refl. Qed.
Lemma D_61dfc : decode_any W_61dfc = Some (ShiftImm ALU_SRL 12 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e00 : bv 32 := 0x00b605b3.
Lemma F_61e00 : fetch_word AsanUbsan.M.loaded_segments (0x61e00 : word) = Some W_61e00.
Proof. vm_refl. Qed.
Lemma D_61e00 : decode_any W_61e00 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e04 : bv 32 := 0x00058663.
Lemma F_61e04 : fetch_word AsanUbsan.M.loaded_segments (0x61e04 : word) = Some W_61e04.
Proof. vm_refl. Qed.
Lemma D_61e04 : decode_any W_61e04 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e08 : bv 32 := 0x00158593.
Lemma F_61e08 : fetch_word AsanUbsan.M.loaded_segments (0x61e08 : word) = Some W_61e08.
Proof. vm_refl. Qed.
Lemma D_61e08 : decode_any W_61e08 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e0c : bv 32 := 0xf6b96ce3.
Lemma F_61e0c : fetch_word AsanUbsan.M.loaded_segments (0x61e0c : word) = Some W_61e0c.
Proof. vm_refl. Qed.
Lemma D_61e0c : decode_any W_61e0c = Some (Branch BC_LTU 18 11 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e10 : bv 32 := 0x00180813.
Lemma F_61e10 : fetch_word AsanUbsan.M.loaded_segments (0x61e10 : word) = Some W_61e10.
Proof. vm_refl. Qed.
Lemma D_61e10 : decode_any W_61e10 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e14 : bv 32 := 0x00385593.
Lemma F_61e14 : fetch_word AsanUbsan.M.loaded_segments (0x61e14 : word) = Some W_61e14.
Proof. vm_refl. Qed.
Lemma D_61e14 : decode_any W_61e14 = Some (ShiftImm ALU_SRL 11 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e18 : bv 32 := 0x00a58533.
Lemma F_61e18 : fetch_word AsanUbsan.M.loaded_segments (0x61e18 : word) = Some W_61e18.
Proof. vm_refl. Qed.
Lemma D_61e18 : decode_any W_61e18 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e1c : bv 32 := 0xe3257ce3.
Lemma F_61e1c : fetch_word AsanUbsan.M.loaded_segments (0x61e1c : word) = Some W_61e1c.
Proof. vm_refl. Qed.
Lemma D_61e1c : decode_any W_61e1c = Some (Branch BC_GEU 10 18 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e20 : bv 32 := 0xf65ff06f.
Lemma F_61e20 : fetch_word AsanUbsan.M.loaded_segments (0x61e20 : word) = Some W_61e20.
Proof. vm_refl. Qed.
Lemma D_61e20 : decode_any W_61e20 = Some (Jal 0 2096996, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e24 : bv 32 := 0xde0584e3.
Lemma F_61e24 : fetch_word AsanUbsan.M.loaded_segments (0x61e24 : word) = Some W_61e24.
Proof. vm_refl. Qed.
Lemma D_61e24 : decode_any W_61e24 = Some (Branch BC_EQ 11 0 7656, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e28 : bv 32 := 0x00355693.
Lemma F_61e28 : fetch_word AsanUbsan.M.loaded_segments (0x61e28 : word) = Some W_61e28.
Proof. vm_refl. Qed.
Lemma D_61e28 : decode_any W_61e28 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e2c : bv 32 := 0x00b686b3.
Lemma F_61e2c : fetch_word AsanUbsan.M.loaded_segments (0x61e2c : word) = Some W_61e2c.
Proof. vm_refl. Qed.
Lemma D_61e2c : decode_any W_61e2c = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e30 : bv 32 := 0xdc068ee3.
Lemma F_61e30 : fetch_word AsanUbsan.M.loaded_segments (0x61e30 : word) = Some W_61e30.
Proof. vm_refl. Qed.
Lemma D_61e30 : decode_any W_61e30 = Some (Branch BC_EQ 13 0 7644, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e34 : bv 32 := 0x00168693.
Lemma F_61e34 : fetch_word AsanUbsan.M.loaded_segments (0x61e34 : word) = Some W_61e34.
Proof. vm_refl. Qed.
Lemma D_61e34 : decode_any W_61e34 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e38 : bv 32 := 0xecd462e3.
Lemma F_61e38 : fetch_word AsanUbsan.M.loaded_segments (0x61e38 : word) = Some W_61e38.
Proof. vm_refl. Qed.
Lemma D_61e38 : decode_any W_61e38 = Some (Branch BC_LTU 8 13 7876, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e3c : bv 32 := 0xdd1ff06f.
Lemma F_61e3c : fetch_word AsanUbsan.M.loaded_segments (0x61e3c : word) = Some W_61e3c.
Proof. vm_refl. Qed.
Lemma D_61e3c : decode_any W_61e3c = Some (Jal 0 2096592, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e40 : bv 32 := 0xe0058ae3.
Lemma F_61e40 : fetch_word AsanUbsan.M.loaded_segments (0x61e40 : word) = Some W_61e40.
Proof. vm_refl. Qed.
Lemma D_61e40 : decode_any W_61e40 = Some (Branch BC_EQ 11 0 7700, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e44 : bv 32 := 0x00355513.
Lemma F_61e44 : fetch_word AsanUbsan.M.loaded_segments (0x61e44 : word) = Some W_61e44.
Proof. vm_refl. Qed.
Lemma D_61e44 : decode_any W_61e44 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e48 : bv 32 := 0x00b505b3.
Lemma F_61e48 : fetch_word AsanUbsan.M.loaded_segments (0x61e48 : word) = Some W_61e48.
Proof. vm_refl. Qed.
Lemma D_61e48 : decode_any W_61e48 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e4c : bv 32 := 0xe00584e3.
Lemma F_61e4c : fetch_word AsanUbsan.M.loaded_segments (0x61e4c : word) = Some W_61e4c.
Proof. vm_refl. Qed.
Lemma D_61e4c : decode_any W_61e4c = Some (Branch BC_EQ 11 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e50 : bv 32 := 0x00158593.
Lemma F_61e50 : fetch_word AsanUbsan.M.loaded_segments (0x61e50 : word) = Some W_61e50.
Proof. vm_refl. Qed.
Lemma D_61e50 : decode_any W_61e50 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e54 : bv 32 := 0xf2b968e3.
Lemma F_61e54 : fetch_word AsanUbsan.M.loaded_segments (0x61e54 : word) = Some W_61e54.
Proof. vm_refl. Qed.
Lemma D_61e54 : decode_any W_61e54 = Some (Branch BC_LTU 18 11 7984, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e58 : bv 32 := 0xdfdff06f.
Lemma F_61e58 : fetch_word AsanUbsan.M.loaded_segments (0x61e58 : word) = Some W_61e58.
Proof. vm_refl. Qed.
Lemma D_61e58 : decode_any W_61e58 = Some (Jal 0 2096636, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e5c : bv 32 := 0x00170713.
Lemma F_61e5c : fetch_word AsanUbsan.M.loaded_segments (0x61e5c : word) = Some W_61e5c.
Proof. vm_refl. Qed.
Lemma D_61e5c : decode_any W_61e5c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e60 : bv 32 := 0x00375713.
Lemma F_61e60 : fetch_word AsanUbsan.M.loaded_segments (0x61e60 : word) = Some W_61e60.
Proof. vm_refl. Qed.
Lemma D_61e60 : decode_any W_61e60 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e64 : bv 32 := 0xfff70713.
Lemma F_61e64 : fetch_word AsanUbsan.M.loaded_segments (0x61e64 : word) = Some W_61e64.
Proof. vm_refl. Qed.
Lemma D_61e64 : decode_any W_61e64 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e68 : bv 32 := 0xda8772e3.
Lemma F_61e68 : fetch_word AsanUbsan.M.loaded_segments (0x61e68 : word) = Some W_61e68.
Proof. vm_refl. Qed.
Lemma D_61e68 : decode_any W_61e68 = Some (Branch BC_GEU 14 8 7588, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e6c : bv 32 := 0xe91ff06f.
Lemma F_61e6c : fetch_word AsanUbsan.M.loaded_segments (0x61e6c : word) = Some W_61e6c.
Proof. vm_refl. Qed.
Lemma D_61e6c : decode_any W_61e6c = Some (Jal 0 2096784, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e70 : bv 32 := 0x00168693.
Lemma F_61e70 : fetch_word AsanUbsan.M.loaded_segments (0x61e70 : word) = Some W_61e70.
Proof. vm_refl. Qed.
Lemma D_61e70 : decode_any W_61e70 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e74 : bv 32 := 0x0036d693.
Lemma F_61e74 : fetch_word AsanUbsan.M.loaded_segments (0x61e74 : word) = Some W_61e74.
Proof. vm_refl. Qed.
Lemma D_61e74 : decode_any W_61e74 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e78 : bv 32 := 0xfff68693.
Lemma F_61e78 : fetch_word AsanUbsan.M.loaded_segments (0x61e78 : word) = Some W_61e78.
Proof. vm_refl. Qed.
Lemma D_61e78 : decode_any W_61e78 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e7c : bv 32 := 0xdd26fce3.
Lemma F_61e7c : fetch_word AsanUbsan.M.loaded_segments (0x61e7c : word) = Some W_61e7c.
Proof. vm_refl. Qed.
Lemma D_61e7c : decode_any W_61e7c = Some (Branch BC_GEU 13 18 7640, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e80 : bv 32 := 0xf05ff06f.
Lemma F_61e80 : fetch_word AsanUbsan.M.loaded_segments (0x61e80 : word) = Some W_61e80.
Proof. vm_refl. Qed.
Lemma D_61e80 : decode_any W_61e80 = Some (Jal 0 2096900, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e84 : bv 32 := 0xfffbf517.
Lemma F_61e84 : fetch_word AsanUbsan.M.loaded_segments (0x61e84 : word) = Some W_61e84.
Proof. vm_refl. Qed.
Lemma D_61e84 : decode_any W_61e84 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e88 : bv 32 := 0xfffc0597.
Lemma F_61e88 : fetch_word AsanUbsan.M.loaded_segments (0x61e88 : word) = Some W_61e88.
Proof. vm_refl. Qed.
Lemma D_61e88 : decode_any W_61e88 = Some (Auipc 11 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e8c : bv 32 := 0xe2c50513.
Lemma F_61e8c : fetch_word AsanUbsan.M.loaded_segments (0x61e8c : word) = Some W_61e8c.
Proof. vm_refl. Qed.
Lemma D_61e8c : decode_any W_61e8c = Some (OpImm ALU_ADD 10 10 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e90 : bv 32 := 0xeda58613.
Lemma F_61e90 : fetch_word AsanUbsan.M.loaded_segments (0x61e90 : word) = Some W_61e90.
Proof. vm_refl. Qed.
Lemma D_61e90 : decode_any W_61e90 = Some (OpImm ALU_ADD 12 11 3802, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e94 : bv 32 := 0x0be00593.
Lemma F_61e94 : fetch_word AsanUbsan.M.loaded_segments (0x61e94 : word) = Some W_61e94.
Proof. vm_refl. Qed.
Lemma D_61e94 : decode_any W_61e94 = Some (OpImm ALU_ADD 11 0 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e98 : bv 32 := 0x00040693.
Lemma F_61e98 : fetch_word AsanUbsan.M.loaded_segments (0x61e98 : word) = Some W_61e98.
Proof. vm_refl. Qed.
Lemma D_61e98 : decode_any W_61e98 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61e9c : bv 32 := 0x00090713.
Lemma F_61e9c : fetch_word AsanUbsan.M.loaded_segments (0x61e9c : word) = Some W_61e9c.
Proof. vm_refl. Qed.
Lemma D_61e9c : decode_any W_61e9c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ea0 : bv 32 := 0x448170ef.
Lemma F_61ea0 : fetch_word AsanUbsan.M.loaded_segments (0x61ea0 : word) = Some W_61ea0.
Proof. vm_refl. Qed.
Lemma D_61ea0 : decode_any W_61ea0 = Some (Jal 1 95304, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ea4 : bv 32 := 0xfffbf517.
Lemma F_61ea4 : fetch_word AsanUbsan.M.loaded_segments (0x61ea4 : word) = Some W_61ea4.
Proof. vm_refl. Qed.
Lemma D_61ea4 : decode_any W_61ea4 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ea8 : bv 32 := 0xfffb4597.
Lemma F_61ea8 : fetch_word AsanUbsan.M.loaded_segments (0x61ea8 : word) = Some W_61ea8.
Proof. vm_refl. Qed.
Lemma D_61ea8 : decode_any W_61ea8 = Some (Auipc 11 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_61eac : bv 32 := 0xe0c50513.
Lemma F_61eac : fetch_word AsanUbsan.M.loaded_segments (0x61eac : word) = Some W_61eac.
Proof. vm_refl. Qed.
Lemma D_61eac : decode_any W_61eac = Some (OpImm ALU_ADD 10 10 3596, 4%Z).
Proof. vm_refl. Qed.

Definition W_61eb0 : bv 32 := 0xc3858613.
Lemma F_61eb0 : fetch_word AsanUbsan.M.loaded_segments (0x61eb0 : word) = Some W_61eb0.
Proof. vm_refl. Qed.
Lemma D_61eb0 : decode_any W_61eb0 = Some (OpImm ALU_ADD 12 11 3128, 4%Z).
Proof. vm_refl. Qed.

Definition W_61eb4 : bv 32 := 0x0d000593.
Lemma F_61eb4 : fetch_word AsanUbsan.M.loaded_segments (0x61eb4 : word) = Some W_61eb4.
Proof. vm_refl. Qed.
Lemma D_61eb4 : decode_any W_61eb4 = Some (OpImm ALU_ADD 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_61eb8 : bv 32 := 0x00000693.
Lemma F_61eb8 : fetch_word AsanUbsan.M.loaded_segments (0x61eb8 : word) = Some W_61eb8.
Proof. vm_refl. Qed.
Lemma D_61eb8 : decode_any W_61eb8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ebc : bv 32 := 0x00000713.
Lemma F_61ebc : fetch_word AsanUbsan.M.loaded_segments (0x61ebc : word) = Some W_61ebc.
Proof. vm_refl. Qed.
Lemma D_61ebc : decode_any W_61ebc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ec0 : bv 32 := 0x428170ef.
Lemma F_61ec0 : fetch_word AsanUbsan.M.loaded_segments (0x61ec0 : word) = Some W_61ec0.
Proof. vm_refl. Qed.
Lemma D_61ec0 : decode_any W_61ec0 = Some (Jal 1 95272, 4%Z).
Proof. vm_refl. Qed.
