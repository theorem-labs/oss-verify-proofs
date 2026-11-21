(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No the author licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_19adc : bv 32 := 0x00008067.
Lemma F_19adc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bc4 : word) = Some W_19adc.
Proof. vm_refl. Qed.
Lemma D_19adc : decode_any W_19adc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae0 : bv 32 := 0xe8010113.
Lemma F_19ae0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bc8 : word) = Some W_19ae0.
Proof. vm_refl. Qed.
Lemma D_19ae0 : decode_any W_19ae0 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae4 : bv 32 := 0x16113c23.
Lemma F_19ae4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bcc : word) = Some W_19ae4.
Proof. vm_refl. Qed.
Lemma D_19ae4 : decode_any W_19ae4 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae8 : bv 32 := 0x16813823.
Lemma F_19ae8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bd0 : word) = Some W_19ae8.
Proof. vm_refl. Qed.
Lemma D_19ae8 : decode_any W_19ae8 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aec : bv 32 := 0x16913423.
Lemma F_19aec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bd4 : word) = Some W_19aec.
Proof. vm_refl. Qed.
Lemma D_19aec : decode_any W_19aec = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af0 : bv 32 := 0x17213023.
Lemma F_19af0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bd8 : word) = Some W_19af0.
Proof. vm_refl. Qed.
Lemma D_19af0 : decode_any W_19af0 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af4 : bv 32 := 0x00058413.
Lemma F_19af4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bdc : word) = Some W_19af4.
Proof. vm_refl. Qed.
Lemma D_19af4 : decode_any W_19af4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af8 : bv 32 := 0x00050493.
Lemma F_19af8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19be0 : word) = Some W_19af8.
Proof. vm_refl. Qed.
Lemma D_19af8 : decode_any W_19af8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19afc : bv 32 := 0x03010513.
Lemma F_19afc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19be4 : word) = Some W_19afc.
Proof. vm_refl. Qed.
Lemma D_19afc : decode_any W_19afc = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b00 : bv 32 := 0x13000613.
Lemma F_19b00 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19be8 : word) = Some W_19b00.
Proof. vm_refl. Qed.
Lemma D_19b00 : decode_any W_19b00 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b04 : bv 32 := 0x00000593.
Lemma F_19b04 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bec : word) = Some W_19b04.
Proof. vm_refl. Qed.
Lemma D_19b04 : decode_any W_19b04 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b08 : bv 32 := 0x459070ef.
Lemma F_19b08 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bf0 : word) = Some W_19b08.
Proof. vm_refl. Qed.
Lemma D_19b08 : decode_any W_19b08 = Some (Jal 1 31832, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b0c : bv 32 := 0x00009517.
Lemma F_19b0c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bf4 : word) = Some W_19b0c.
Proof. vm_refl. Qed.
Lemma D_19b0c : decode_any W_19b0c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b10 : bv 32 := 0x2a453503.
Lemma F_19b10 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bf8 : word) = Some W_19b10.
Proof. vm_refl. Qed.
Lemma D_19b10 : decode_any W_19b10 = Some (Load SZ8 true 10 10 676, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b14 : bv 32 := 0x00953023.
Lemma F_19b14 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19bfc : word) = Some W_19b14.
Proof. vm_refl. Qed.
Lemma D_19b14 : decode_any W_19b14 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b18 : bv 32 := 0x0004b503.
Lemma F_19b18 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c00 : word) = Some W_19b18.
Proof. vm_refl. Qed.
Lemma D_19b18 : decode_any W_19b18 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b1c : bv 32 := 0x00848493.
Lemma F_19b1c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c04 : word) = Some W_19b1c.
Proof. vm_refl. Qed.
Lemma D_19b1c : decode_any W_19b1c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b20 : bv 32 := 0xfe051ce3.
Lemma F_19b20 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c08 : word) = Some W_19b20.
Proof. vm_refl. Qed.
Lemma D_19b20 : decode_any W_19b20 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b24 : bv 32 := 0x0007b517.
Lemma F_19b24 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c0c : word) = Some W_19b24.
Proof. vm_refl. Qed.
Lemma D_19b24 : decode_any W_19b24 = Some (Auipc 10 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b28 : bv 32 := 0x8bc50913.
Lemma F_19b28 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c10 : word) = Some W_19b28.
Proof. vm_refl. Qed.
Lemma D_19b28 : decode_any W_19b28 = Some (OpImm ALU_ADD 18 10 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b2c : bv 32 := 0x00993423.
Lemma F_19b2c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c14 : word) = Some W_19b2c.
Proof. vm_refl. Qed.
Lemma D_19b2c : decode_any W_19b2c = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b30 : bv 32 := 0x0004b583.
Lemma F_19b30 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c18 : word) = Some W_19b30.
Proof. vm_refl. Qed.
Lemma D_19b30 : decode_any W_19b30 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b34 : bv 32 := 0x04058c63.
Lemma F_19b34 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c1c : word) = Some W_19b34.
Proof. vm_refl. Qed.
Lemma D_19b34 : decode_any W_19b34 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b38 : bv 32 := 0x01048493.
Lemma F_19b38 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c20 : word) = Some W_19b38.
Proof. vm_refl. Qed.
Lemma D_19b38 : decode_any W_19b38 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b3c : bv 32 := 0x02500513.
Lemma F_19b3c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c24 : word) = Some W_19b3c.
Proof. vm_refl. Qed.
Lemma D_19b3c : decode_any W_19b3c = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b40 : bv 32 := 0x03010613.
Lemma F_19b40 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c28 : word) = Some W_19b40.
Proof. vm_refl. Qed.
Lemma D_19b40 : decode_any W_19b40 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b44 : bv 32 := 0x0100006f.
Lemma F_19b44 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c2c : word) = Some W_19b44.
Proof. vm_refl. Qed.
Lemma D_19b44 : decode_any W_19b44 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b48 : bv 32 := 0x0004b583.
Lemma F_19b48 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c30 : word) = Some W_19b48.
Proof. vm_refl. Qed.
Lemma D_19b48 : decode_any W_19b48 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b4c : bv 32 := 0x01048493.
Lemma F_19b4c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c34 : word) = Some W_19b4c.
Proof. vm_refl. Qed.
Lemma D_19b4c : decode_any W_19b4c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b50 : bv 32 := 0x00058e63.
Lemma F_19b50 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c38 : word) = Some W_19b50.
Proof. vm_refl. Qed.
Lemma D_19b50 : decode_any W_19b50 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b54 : bv 32 := 0xfeb56ae3.
Lemma F_19b54 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c3c : word) = Some W_19b54.
Proof. vm_refl. Qed.
Lemma D_19b54 : decode_any W_19b54 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b58 : bv 32 := 0xff84b683.
Lemma F_19b58 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c40 : word) = Some W_19b58.
Proof. vm_refl. Qed.
Lemma D_19b58 : decode_any W_19b58 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b5c : bv 32 := 0x00359593.
Lemma F_19b5c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c44 : word) = Some W_19b5c.
Proof. vm_refl. Qed.
Lemma D_19b5c : decode_any W_19b5c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b60 : bv 32 := 0x00b605b3.
Lemma F_19b60 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c48 : word) = Some W_19b60.
Proof. vm_refl. Qed.
Lemma D_19b60 : decode_any W_19b60 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b64 : bv 32 := 0x00d5b023.
Lemma F_19b64 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c4c : word) = Some W_19b64.
Proof. vm_refl. Qed.
Lemma D_19b64 : decode_any W_19b64 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b68 : bv 32 := 0xfe1ff06f.
Lemma F_19b68 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c50 : word) = Some W_19b68.
Proof. vm_refl. Qed.
Lemma D_19b68 : decode_any W_19b68 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b6c : bv 32 := 0x0b013583.
Lemma F_19b6c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c54 : word) = Some W_19b6c.
Proof. vm_refl. Qed.
Lemma D_19b6c : decode_any W_19b6c = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b70 : bv 32 := 0x13013503.
Lemma F_19b70 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c58 : word) = Some W_19b70.
Proof. vm_refl. Qed.
Lemma D_19b70 : decode_any W_19b70 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b74 : bv 32 := 0x0007b617.
Lemma F_19b74 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c5c : word) = Some W_19b74.
Proof. vm_refl. Qed.
Lemma D_19b74 : decode_any W_19b74 = Some (Auipc 12 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b78 : bv 32 := 0x8cb63a23.
Lemma F_19b78 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c60 : word) = Some W_19b78.
Proof. vm_refl. Qed.
Lemma D_19b78 : decode_any W_19b78 = Some (Store SZ8 12 11 2260, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b7c : bv 32 := 0x00050c63.
Lemma F_19b7c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c64 : word) = Some W_19b7c.
Proof. vm_refl. Qed.
Lemma D_19b7c : decode_any W_19b7c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b80 : bv 32 := 0x0007b597.
Lemma F_19b80 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c68 : word) = Some W_19b80.
Proof. vm_refl. Qed.
Lemma D_19b80 : decode_any W_19b80 = Some (Auipc 11 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b84 : bv 32 := 0x84a5b423.
Lemma F_19b84 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c6c : word) = Some W_19b84.
Proof. vm_refl. Qed.
Lemma D_19b84 : decode_any W_19b84 = Some (Store SZ8 11 10 2120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b88 : bv 32 := 0x00c0006f.
Lemma F_19b88 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c70 : word) = Some W_19b88.
Proof. vm_refl. Qed.
Lemma D_19b88 : decode_any W_19b88 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b8c : bv 32 := 0x0007b517.
Lemma F_19b8c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c74 : word) = Some W_19b8c.
Proof. vm_refl. Qed.
Lemma D_19b8c : decode_any W_19b8c = Some (Auipc 10 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b90 : bv 32 := 0x8a053e23.
Lemma F_19b90 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c78 : word) = Some W_19b90.
Proof. vm_refl. Qed.
Lemma D_19b90 : decode_any W_19b90 = Some (Store SZ8 10 0 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b94 : bv 32 := 0x06013503.
Lemma F_19b94 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c7c : word) = Some W_19b94.
Proof. vm_refl. Qed.
Lemma D_19b94 : decode_any W_19b94 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b98 : bv 32 := 0x02a93823.
Lemma F_19b98 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c80 : word) = Some W_19b98.
Proof. vm_refl. Qed.
Lemma D_19b98 : decode_any W_19b98 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b9c : bv 32 := 0x00041463.
Lemma F_19b9c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c84 : word) = Some W_19b9c.
Proof. vm_refl. Qed.
Lemma D_19b9c : decode_any W_19b9c = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba0 : bv 32 := 0x12813403.
Lemma F_19ba0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c88 : word) = Some W_19ba0.
Proof. vm_refl. Qed.
Lemma D_19ba0 : decode_any W_19ba0 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba4 : bv 32 := 0x00041663.
Lemma F_19ba4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c8c : word) = Some W_19ba4.
Proof. vm_refl. Qed.
Lemma D_19ba4 : decode_any W_19ba4 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba8 : bv 32 := 0xffff6517.
Lemma F_19ba8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c90 : word) = Some W_19ba8.
Proof. vm_refl. Qed.
Lemma D_19ba8 : decode_any W_19ba8 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bac : bv 32 := 0x6a850413.
Lemma F_19bac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c94 : word) = Some W_19bac.
Proof. vm_refl. Qed.
Lemma D_19bac : decode_any W_19bac = Some (OpImm ALU_ADD 8 10 1704, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb0 : bv 32 := 0x00009517.
Lemma F_19bb0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c98 : word) = Some W_19bb0.
Proof. vm_refl. Qed.
Lemma D_19bb0 : decode_any W_19bb0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb4 : bv 32 := 0x20853583.
Lemma F_19bb4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19c9c : word) = Some W_19bb4.
Proof. vm_refl. Qed.
Lemma D_19bb4 : decode_any W_19bb4 = Some (Load SZ8 true 11 10 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb8 : bv 32 := 0x00009517.
Lemma F_19bb8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ca0 : word) = Some W_19bb8.
Proof. vm_refl. Qed.
Lemma D_19bb8 : decode_any W_19bb8 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bbc : bv 32 := 0x20853503.
Lemma F_19bbc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ca4 : word) = Some W_19bbc.
Proof. vm_refl. Qed.
Lemma D_19bbc : decode_any W_19bbc = Some (Load SZ8 true 10 10 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bc0 : bv 32 := 0x0085b023.
Lemma F_19bc0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ca8 : word) = Some W_19bc0.
Proof. vm_refl. Qed.
Lemma D_19bc0 : decode_any W_19bc0 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bc4 : bv 32 := 0x00140593.
Lemma F_19bc4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cac : word) = Some W_19bc4.
Proof. vm_refl. Qed.
Lemma D_19bc4 : decode_any W_19bc4 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bc8 : bv 32 := 0x00853023.
Lemma F_19bc8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cb0 : word) = Some W_19bc8.
Proof. vm_refl. Qed.
Lemma D_19bc8 : decode_any W_19bc8 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bcc : bv 32 := 0x02f00613.
Lemma F_19bcc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cb4 : word) = Some W_19bcc.
Proof. vm_refl. Qed.
Lemma D_19bcc : decode_any W_19bcc = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bd0 : bv 32 := 0x00c0006f.
Lemma F_19bd0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cb8 : word) = Some W_19bd0.
Proof. vm_refl. Qed.
Lemma D_19bd0 : decode_any W_19bd0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bd4 : bv 32 := 0x00b53023.
Lemma F_19bd4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cbc : word) = Some W_19bd4.
Proof. vm_refl. Qed.
Lemma D_19bd4 : decode_any W_19bd4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bd8 : bv 32 := 0x00158593.
Lemma F_19bd8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cc0 : word) = Some W_19bd8.
Proof. vm_refl. Qed.
Lemma D_19bd8 : decode_any W_19bd8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bdc : bv 32 := 0xfff5c683.
Lemma F_19bdc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cc4 : word) = Some W_19bdc.
Proof. vm_refl. Qed.
Lemma D_19bdc : decode_any W_19bdc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_19be0 : bv 32 := 0xfec68ae3.
Lemma F_19be0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cc8 : word) = Some W_19be0.
Proof. vm_refl. Qed.
Lemma D_19be0 : decode_any W_19be0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_19be4 : bv 32 := 0xfe069ae3.
Lemma F_19be4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ccc : word) = Some W_19be4.
Proof. vm_refl. Qed.
Lemma D_19be4 : decode_any W_19be4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_19be8 : bv 32 := 0x03010513.
Lemma F_19be8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cd0 : word) = Some W_19be8.
Proof. vm_refl. Qed.
Lemma D_19be8 : decode_any W_19be8 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bec : bv 32 := 0x214000ef.
Lemma F_19bec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cd4 : word) = Some W_19bec.
Proof. vm_refl. Qed.
Lemma D_19bec : decode_any W_19bec = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bf0 : bv 32 := 0x0f813503.
Lemma F_19bf0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cd8 : word) = Some W_19bf0.
Proof. vm_refl. Qed.
Lemma D_19bf0 : decode_any W_19bf0 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bf4 : bv 32 := 0x015000ef.
Lemma F_19bf4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cdc : word) = Some W_19bf4.
Proof. vm_refl. Qed.
Lemma D_19bf4 : decode_any W_19bf4 = Some (Jal 1 2068, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bf8 : bv 32 := 0x08813503.
Lemma F_19bf8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ce0 : word) = Some W_19bf8.
Proof. vm_refl. Qed.
Lemma D_19bf8 : decode_any W_19bf8 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bfc : bv 32 := 0x09013583.
Lemma F_19bfc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ce4 : word) = Some W_19bfc.
Proof. vm_refl. Qed.
Lemma D_19bfc : decode_any W_19bfc = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c00 : bv 32 := 0x00b51c63.
Lemma F_19c00 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ce8 : word) = Some W_19c00.
Proof. vm_refl. Qed.
Lemma D_19c00 : decode_any W_19c00 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c04 : bv 32 := 0x09813503.
Lemma F_19c04 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cec : word) = Some W_19c04.
Proof. vm_refl. Qed.
Lemma D_19c04 : decode_any W_19c04 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c08 : bv 32 := 0x0a013583.
Lemma F_19c08 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cf0 : word) = Some W_19c08.
Proof. vm_refl. Qed.
Lemma D_19c08 : decode_any W_19c08 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c0c : bv 32 := 0x00b51663.
Lemma F_19c0c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cf4 : word) = Some W_19c0c.
Proof. vm_refl. Qed.
Lemma D_19c0c : decode_any W_19c0c = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c10 : bv 32 := 0x0e813503.
Lemma F_19c10 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cf8 : word) = Some W_19c10.
Proof. vm_refl. Qed.
Lemma D_19c10 : decode_any W_19c10 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c14 : bv 32 := 0x0e050063.
Lemma F_19c14 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19cfc : word) = Some W_19c14.
Proof. vm_refl. Qed.
Lemma D_19c14 : decode_any W_19c14 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c18 : bv 32 := 0x00200693.
Lemma F_19c18 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d00 : word) = Some W_19c18.
Proof. vm_refl. Qed.
Lemma D_19c18 : decode_any W_19c18 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c1c : bv 32 := 0x00100793.
Lemma F_19c1c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d04 : word) = Some W_19c1c.
Proof. vm_refl. Qed.
Lemma D_19c1c : decode_any W_19c1c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c20 : bv 32 := 0x00013423.
Lemma F_19c20 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d08 : word) = Some W_19c20.
Proof. vm_refl. Qed.
Lemma D_19c20 : decode_any W_19c20 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c24 : bv 32 := 0x00013823.
Lemma F_19c24 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d0c : word) = Some W_19c24.
Proof. vm_refl. Qed.
Lemma D_19c24 : decode_any W_19c24 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c28 : bv 32 := 0x04900893.
Lemma F_19c28 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d10 : word) = Some W_19c28.
Proof. vm_refl. Qed.
Lemma D_19c28 : decode_any W_19c28 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c2c : bv 32 := 0x01810513.
Lemma F_19c2c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d14 : word) = Some W_19c2c.
Proof. vm_refl. Qed.
Lemma D_19c2c : decode_any W_19c2c = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c30 : bv 32 := 0x00300593.
Lemma F_19c30 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d18 : word) = Some W_19c30.
Proof. vm_refl. Qed.
Lemma D_19c30 : decode_any W_19c30 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c34 : bv 32 := 0x00810613.
Lemma F_19c34 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d1c : word) = Some W_19c34.
Proof. vm_refl. Qed.
Lemma D_19c34 : decode_any W_19c34 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c38 : bv 32 := 0x00800713.
Lemma F_19c38 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d20 : word) = Some W_19c38.
Proof. vm_refl. Qed.
Lemma D_19c38 : decode_any W_19c38 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c3c : bv 32 := 0x00013c23.
Lemma F_19c3c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d24 : word) = Some W_19c3c.
Proof. vm_refl. Qed.
Lemma D_19c3c : decode_any W_19c3c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c40 : bv 32 := 0x02f13023.
Lemma F_19c40 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d28 : word) = Some W_19c40.
Proof. vm_refl. Qed.
Lemma D_19c40 : decode_any W_19c40 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c44 : bv 32 := 0x02d13423.
Lemma F_19c44 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d2c : word) = Some W_19c44.
Proof. vm_refl. Qed.
Lemma D_19c44 : decode_any W_19c44 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c48 : bv 32 := 0x00000693.
Lemma F_19c48 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d30 : word) = Some W_19c48.
Proof. vm_refl. Qed.
Lemma D_19c48 : decode_any W_19c48 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c4c : bv 32 := 0x00000073.
Lemma F_19c4c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d34 : word) = Some W_19c4c.
Proof. vm_refl. Qed.
Lemma D_19c4c : decode_any W_19c4c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19c4c : is_ecall W_19c4c = true.
Proof. reflexivity. Qed.

Definition W_19c50 : bv 32 := 0x02051513.
Lemma F_19c50 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d38 : word) = Some W_19c50.
Proof. vm_refl. Qed.
Lemma D_19c50 : decode_any W_19c50 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c54 : bv 32 := 0x00055463.
Lemma F_19c54 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d3c : word) = Some W_19c54.
Proof. vm_refl. Qed.
Lemma D_19c54 : decode_any W_19c54 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c58 : bv 32 := 0x00000023.
Lemma F_19c58 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d40 : word) = Some W_19c58.
Proof. vm_refl. Qed.
Lemma D_19c58 : decode_any W_19c58 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c5c : bv 32 := 0x01e15503.
Lemma F_19c5c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d44 : word) = Some W_19c5c.
Proof. vm_refl. Qed.
Lemma D_19c5c : decode_any W_19c5c = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c60 : bv 32 := 0x02057513.
Lemma F_19c60 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d48 : word) = Some W_19c60.
Proof. vm_refl. Qed.
Lemma D_19c60 : decode_any W_19c60 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c64 : bv 32 := 0x02050463.
Lemma F_19c64 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d4c : word) = Some W_19c64.
Proof. vm_refl. Qed.
Lemma D_19c64 : decode_any W_19c64 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c68 : bv 32 := 0xffff6517.
Lemma F_19c68 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d50 : word) = Some W_19c68.
Proof. vm_refl. Qed.
Lemma D_19c68 : decode_any W_19c68 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c6c : bv 32 := 0x00008637.
Lemma F_19c6c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d54 : word) = Some W_19c6c.
Proof. vm_refl. Qed.
Lemma D_19c6c : decode_any W_19c6c = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c70 : bv 32 := 0x03800893.
Lemma F_19c70 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d58 : word) = Some W_19c70.
Proof. vm_refl. Qed.
Lemma D_19c70 : decode_any W_19c70 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c74 : bv 32 := 0x7ff50593.
Lemma F_19c74 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d5c : word) = Some W_19c74.
Proof. vm_refl. Qed.
Lemma D_19c74 : decode_any W_19c74 = Some (OpImm ALU_ADD 11 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c78 : bv 32 := 0x0026061b.
Lemma F_19c78 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d60 : word) = Some W_19c78.
Proof. vm_refl. Qed.
Lemma D_19c78 : decode_any W_19c78 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c7c : bv 32 := 0xf9c00513.
Lemma F_19c7c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d64 : word) = Some W_19c7c.
Proof. vm_refl. Qed.
Lemma D_19c7c : decode_any W_19c7c = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c80 : bv 32 := 0x00000073.
Lemma F_19c80 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d68 : word) = Some W_19c80.
Proof. vm_refl. Qed.
Lemma D_19c80 : decode_any W_19c80 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19c80 : is_ecall W_19c80 = true.
Proof. reflexivity. Qed.

Definition W_19c84 : bv 32 := 0x00055463.
Lemma F_19c84 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d6c : word) = Some W_19c84.
Proof. vm_refl. Qed.
Lemma D_19c84 : decode_any W_19c84 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c88 : bv 32 := 0x00000023.
Lemma F_19c88 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d70 : word) = Some W_19c88.
Proof. vm_refl. Qed.
Lemma D_19c88 : decode_any W_19c88 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c8c : bv 32 := 0x02615503.
Lemma F_19c8c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d74 : word) = Some W_19c8c.
Proof. vm_refl. Qed.
Lemma D_19c8c : decode_any W_19c8c = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c90 : bv 32 := 0x02057513.
Lemma F_19c90 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d78 : word) = Some W_19c90.
Proof. vm_refl. Qed.
Lemma D_19c90 : decode_any W_19c90 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c94 : bv 32 := 0x02050463.
Lemma F_19c94 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d7c : word) = Some W_19c94.
Proof. vm_refl. Qed.
Lemma D_19c94 : decode_any W_19c94 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c98 : bv 32 := 0xffff6517.
Lemma F_19c98 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d80 : word) = Some W_19c98.
Proof. vm_refl. Qed.
Lemma D_19c98 : decode_any W_19c98 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c9c : bv 32 := 0x00008637.
Lemma F_19c9c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d84 : word) = Some W_19c9c.
Proof. vm_refl. Qed.
Lemma D_19c9c : decode_any W_19c9c = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ca0 : bv 32 := 0x03800893.
Lemma F_19ca0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d88 : word) = Some W_19ca0.
Proof. vm_refl. Qed.
Lemma D_19ca0 : decode_any W_19ca0 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ca4 : bv 32 := 0x7cf50593.
Lemma F_19ca4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d8c : word) = Some W_19ca4.
Proof. vm_refl. Qed.
Lemma D_19ca4 : decode_any W_19ca4 = Some (OpImm ALU_ADD 11 10 1999, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ca8 : bv 32 := 0x0026061b.
Lemma F_19ca8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d90 : word) = Some W_19ca8.
Proof. vm_refl. Qed.
Lemma D_19ca8 : decode_any W_19ca8 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cac : bv 32 := 0xf9c00513.
Lemma F_19cac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d94 : word) = Some W_19cac.
Proof. vm_refl. Qed.
Lemma D_19cac : decode_any W_19cac = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cb0 : bv 32 := 0x00000073.
Lemma F_19cb0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d98 : word) = Some W_19cb0.
Proof. vm_refl. Qed.
Lemma D_19cb0 : decode_any W_19cb0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19cb0 : is_ecall W_19cb0 = true.
Proof. reflexivity. Qed.

Definition W_19cb4 : bv 32 := 0x00055463.
Lemma F_19cb4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19d9c : word) = Some W_19cb4.
Proof. vm_refl. Qed.
Lemma D_19cb4 : decode_any W_19cb4 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cb8 : bv 32 := 0x00000023.
Lemma F_19cb8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19da0 : word) = Some W_19cb8.
Proof. vm_refl. Qed.
Lemma D_19cb8 : decode_any W_19cb8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cbc : bv 32 := 0x02e15503.
Lemma F_19cbc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19da4 : word) = Some W_19cbc.
Proof. vm_refl. Qed.
Lemma D_19cbc : decode_any W_19cbc = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cc0 : bv 32 := 0x02057513.
Lemma F_19cc0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19da8 : word) = Some W_19cc0.
Proof. vm_refl. Qed.
Lemma D_19cc0 : decode_any W_19cc0 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cc4 : bv 32 := 0x02050463.
Lemma F_19cc4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dac : word) = Some W_19cc4.
Proof. vm_refl. Qed.
Lemma D_19cc4 : decode_any W_19cc4 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cc8 : bv 32 := 0xffff6517.
Lemma F_19cc8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19db0 : word) = Some W_19cc8.
Proof. vm_refl. Qed.
Lemma D_19cc8 : decode_any W_19cc8 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ccc : bv 32 := 0x00008637.
Lemma F_19ccc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19db4 : word) = Some W_19ccc.
Proof. vm_refl. Qed.
Lemma D_19ccc : decode_any W_19ccc = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cd0 : bv 32 := 0x03800893.
Lemma F_19cd0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19db8 : word) = Some W_19cd0.
Proof. vm_refl. Qed.
Lemma D_19cd0 : decode_any W_19cd0 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cd4 : bv 32 := 0x79f50593.
Lemma F_19cd4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dbc : word) = Some W_19cd4.
Proof. vm_refl. Qed.
Lemma D_19cd4 : decode_any W_19cd4 = Some (OpImm ALU_ADD 11 10 1951, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cd8 : bv 32 := 0x0026061b.
Lemma F_19cd8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dc0 : word) = Some W_19cd8.
Proof. vm_refl. Qed.
Lemma D_19cd8 : decode_any W_19cd8 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cdc : bv 32 := 0xf9c00513.
Lemma F_19cdc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dc4 : word) = Some W_19cdc.
Proof. vm_refl. Qed.
Lemma D_19cdc : decode_any W_19cdc = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ce0 : bv 32 := 0x00000073.
Lemma F_19ce0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dc8 : word) = Some W_19ce0.
Proof. vm_refl. Qed.
Lemma D_19ce0 : decode_any W_19ce0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19ce0 : is_ecall W_19ce0 = true.
Proof. reflexivity. Qed.

Definition W_19ce4 : bv 32 := 0x00055463.
Lemma F_19ce4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dcc : word) = Some W_19ce4.
Proof. vm_refl. Qed.
Lemma D_19ce4 : decode_any W_19ce4 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ce8 : bv 32 := 0x00000023.
Lemma F_19ce8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dd0 : word) = Some W_19ce8.
Proof. vm_refl. Qed.
Lemma D_19ce8 : decode_any W_19ce8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cec : bv 32 := 0x00100513.
Lemma F_19cec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dd4 : word) = Some W_19cec.
Proof. vm_refl. Qed.
Lemma D_19cec : decode_any W_19cec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cf0 : bv 32 := 0x00a90123.
Lemma F_19cf0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dd8 : word) = Some W_19cf0.
Proof. vm_refl. Qed.
Lemma D_19cf0 : decode_any W_19cf0 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cf4 : bv 32 := 0x17813083.
Lemma F_19cf4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ddc : word) = Some W_19cf4.
Proof. vm_refl. Qed.
Lemma D_19cf4 : decode_any W_19cf4 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cf8 : bv 32 := 0x17013403.
Lemma F_19cf8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19de0 : word) = Some W_19cf8.
Proof. vm_refl. Qed.
Lemma D_19cf8 : decode_any W_19cf8 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cfc : bv 32 := 0x16813483.
Lemma F_19cfc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19de4 : word) = Some W_19cfc.
Proof. vm_refl. Qed.
Lemma D_19cfc : decode_any W_19cfc = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d00 : bv 32 := 0x16013903.
Lemma F_19d00 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19de8 : word) = Some W_19d00.
Proof. vm_refl. Qed.
Lemma D_19d00 : decode_any W_19d00 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d04 : bv 32 := 0x18010113.
Lemma F_19d04 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dec : word) = Some W_19d04.
Proof. vm_refl. Qed.
Lemma D_19d04 : decode_any W_19d04 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d08 : bv 32 := 0x00008067.
Lemma F_19d08 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19df0 : word) = Some W_19d08.
Proof. vm_refl. Qed.
Lemma D_19d08 : decode_any W_19d08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d0c : bv 32 := 0xfe010113.
Lemma F_19d0c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19df4 : word) = Some W_19d0c.
Proof. vm_refl. Qed.
Lemma D_19d0c : decode_any W_19d0c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d10 : bv 32 := 0x00113c23.
Lemma F_19d10 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19df8 : word) = Some W_19d10.
Proof. vm_refl. Qed.
Lemma D_19d10 : decode_any W_19d10 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d14 : bv 32 := 0x00813823.
Lemma F_19d14 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19dfc : word) = Some W_19d14.
Proof. vm_refl. Qed.
Lemma D_19d14 : decode_any W_19d14 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d18 : bv 32 := 0x00913423.
Lemma F_19d18 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e00 : word) = Some W_19d18.
Proof. vm_refl. Qed.
Lemma D_19d18 : decode_any W_19d18 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d1c : bv 32 := 0xdc1ff0ef.
Lemma F_19d1c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e04 : word) = Some W_19d1c.
Proof. vm_refl. Qed.
Lemma D_19d1c : decode_any W_19d1c = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d20 : bv 32 := 0x00009517.
Lemma F_19d20 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e08 : word) = Some W_19d20.
Proof. vm_refl. Qed.
Lemma D_19d20 : decode_any W_19d20 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d24 : bv 32 := 0x00009597.
Lemma F_19d24 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e0c : word) = Some W_19d24.
Proof. vm_refl. Qed.
Lemma D_19d24 : decode_any W_19d24 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d28 : bv 32 := 0x0a853403.
Lemma F_19d28 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e10 : word) = Some W_19d28.
Proof. vm_refl. Qed.
Lemma D_19d28 : decode_any W_19d28 = Some (Load SZ8 true 8 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d2c : bv 32 := 0x0ac5b483.
Lemma F_19d2c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e14 : word) = Some W_19d2c.
Proof. vm_refl. Qed.
Lemma D_19d2c : decode_any W_19d2c = Some (Load SZ8 true 9 11 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d30 : bv 32 := 0x0084fa63.
Lemma F_19d30 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e18 : word) = Some W_19d30.
Proof. vm_refl. Qed.
Lemma D_19d30 : decode_any W_19d30 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d34 : bv 32 := 0x0004b503.
Lemma F_19d34 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e1c : word) = Some W_19d34.
Proof. vm_refl. Qed.
Lemma D_19d34 : decode_any W_19d34 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d38 : bv 32 := 0x000500e7.
Lemma F_19d38 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e20 : word) = Some W_19d38.
Proof. vm_refl. Qed.
Lemma D_19d38 : decode_any W_19d38 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d3c : bv 32 := 0x00848493.
Lemma F_19d3c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e24 : word) = Some W_19d3c.
Proof. vm_refl. Qed.
Lemma D_19d3c : decode_any W_19d3c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d40 : bv 32 := 0xfe84eae3.
Lemma F_19d40 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e28 : word) = Some W_19d40.
Proof. vm_refl. Qed.
Lemma D_19d40 : decode_any W_19d40 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d44 : bv 32 := 0x01813083.
Lemma F_19d44 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e2c : word) = Some W_19d44.
Proof. vm_refl. Qed.
Lemma D_19d44 : decode_any W_19d44 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d48 : bv 32 := 0x01013403.
Lemma F_19d48 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e30 : word) = Some W_19d48.
Proof. vm_refl. Qed.
Lemma D_19d48 : decode_any W_19d48 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d4c : bv 32 := 0x00813483.
Lemma F_19d4c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e34 : word) = Some W_19d4c.
Proof. vm_refl. Qed.
Lemma D_19d4c : decode_any W_19d4c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d50 : bv 32 := 0x02010113.
Lemma F_19d50 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e38 : word) = Some W_19d50.
Proof. vm_refl. Qed.
Lemma D_19d50 : decode_any W_19d50 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d54 : bv 32 := 0x00008067.
Lemma F_19d54 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e3c : word) = Some W_19d54.
Proof. vm_refl. Qed.
Lemma D_19d54 : decode_any W_19d54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d58 : bv 32 := 0xfe010113.
Lemma F_19d58 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e40 : word) = Some W_19d58.
Proof. vm_refl. Qed.
Lemma D_19d58 : decode_any W_19d58 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d5c : bv 32 := 0x00113c23.
Lemma F_19d5c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e44 : word) = Some W_19d5c.
Proof. vm_refl. Qed.
Lemma D_19d5c : decode_any W_19d5c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d60 : bv 32 := 0x00813823.
Lemma F_19d60 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e48 : word) = Some W_19d60.
Proof. vm_refl. Qed.
Lemma D_19d60 : decode_any W_19d60 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d64 : bv 32 := 0x00913423.
Lemma F_19d64 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e4c : word) = Some W_19d64.
Proof. vm_refl. Qed.
Lemma D_19d64 : decode_any W_19d64 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d68 : bv 32 := 0x01213023.
Lemma F_19d68 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e50 : word) = Some W_19d68.
Proof. vm_refl. Qed.
Lemma D_19d68 : decode_any W_19d68 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d6c : bv 32 := 0x00060413.
Lemma F_19d6c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e54 : word) = Some W_19d6c.
Proof. vm_refl. Qed.
Lemma D_19d6c : decode_any W_19d6c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d70 : bv 32 := 0x00058493.
Lemma F_19d70 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e58 : word) = Some W_19d70.
Proof. vm_refl. Qed.
Lemma D_19d70 : decode_any W_19d70 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d74 : bv 32 := 0x00050913.
Lemma F_19d74 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e5c : word) = Some W_19d74.
Proof. vm_refl. Qed.
Lemma D_19d74 : decode_any W_19d74 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d78 : bv 32 := 0x00063583.
Lemma F_19d78 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e60 : word) = Some W_19d78.
Proof. vm_refl. Qed.
Lemma D_19d78 : decode_any W_19d78 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d7c : bv 32 := 0x00349513.
Lemma F_19d7c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e64 : word) = Some W_19d7c.
Proof. vm_refl. Qed.
Lemma D_19d7c : decode_any W_19d7c = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d80 : bv 32 := 0x00a60533.
Lemma F_19d80 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e68 : word) = Some W_19d80.
Proof. vm_refl. Qed.
Lemma D_19d80 : decode_any W_19d80 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d84 : bv 32 := 0x00850513.
Lemma F_19d84 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e6c : word) = Some W_19d84.
Proof. vm_refl. Qed.
Lemma D_19d84 : decode_any W_19d84 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d88 : bv 32 := 0xd59ff0ef.
Lemma F_19d88 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e70 : word) = Some W_19d88.
Proof. vm_refl. Qed.
Lemma D_19d88 : decode_any W_19d88 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d8c : bv 32 := 0x00000517.
Lemma F_19d8c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e74 : word) = Some W_19d8c.
Proof. vm_refl. Qed.
Lemma D_19d8c : decode_any W_19d8c = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d90 : bv 32 := 0x02c50313.
Lemma F_19d90 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e78 : word) = Some W_19d90.
Proof. vm_refl. Qed.
Lemma D_19d90 : decode_any W_19d90 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d94 : bv 32 := 0x00090513.
Lemma F_19d94 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e7c : word) = Some W_19d94.
Proof. vm_refl. Qed.
Lemma D_19d94 : decode_any W_19d94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d98 : bv 32 := 0x00048593.
Lemma F_19d98 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e80 : word) = Some W_19d98.
Proof. vm_refl. Qed.
Lemma D_19d98 : decode_any W_19d98 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d9c : bv 32 := 0x00040613.
Lemma F_19d9c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e84 : word) = Some W_19d9c.
Proof. vm_refl. Qed.
Lemma D_19d9c : decode_any W_19d9c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19da0 : bv 32 := 0x01813083.
Lemma F_19da0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e88 : word) = Some W_19da0.
Proof. vm_refl. Qed.
Lemma D_19da0 : decode_any W_19da0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19da4 : bv 32 := 0x01013403.
Lemma F_19da4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e8c : word) = Some W_19da4.
Proof. vm_refl. Qed.
Lemma D_19da4 : decode_any W_19da4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19da8 : bv 32 := 0x00813483.
Lemma F_19da8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e90 : word) = Some W_19da8.
Proof. vm_refl. Qed.
Lemma D_19da8 : decode_any W_19da8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dac : bv 32 := 0x00013903.
Lemma F_19dac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e94 : word) = Some W_19dac.
Proof. vm_refl. Qed.
Lemma D_19dac : decode_any W_19dac = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19db0 : bv 32 := 0x02010113.
Lemma F_19db0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e98 : word) = Some W_19db0.
Proof. vm_refl. Qed.
Lemma D_19db0 : decode_any W_19db0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19db4 : bv 32 := 0x00030067.
Lemma F_19db4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19e9c : word) = Some W_19db4.
Proof. vm_refl. Qed.
Lemma D_19db4 : decode_any W_19db4 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19db8 : bv 32 := 0xfd010113.
Lemma F_19db8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ea0 : word) = Some W_19db8.
Proof. vm_refl. Qed.
Lemma D_19db8 : decode_any W_19db8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dbc : bv 32 := 0x02113423.
Lemma F_19dbc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ea4 : word) = Some W_19dbc.
Proof. vm_refl. Qed.
Lemma D_19dbc : decode_any W_19dbc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dc0 : bv 32 := 0x02813023.
Lemma F_19dc0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ea8 : word) = Some W_19dc0.
Proof. vm_refl. Qed.
Lemma D_19dc0 : decode_any W_19dc0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dc4 : bv 32 := 0x00913c23.
Lemma F_19dc4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19eac : word) = Some W_19dc4.
Proof. vm_refl. Qed.
Lemma D_19dc4 : decode_any W_19dc4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dc8 : bv 32 := 0x01213823.
Lemma F_19dc8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19eb0 : word) = Some W_19dc8.
Proof. vm_refl. Qed.
Lemma D_19dc8 : decode_any W_19dc8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dcc : bv 32 := 0x01313423.
Lemma F_19dcc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19eb4 : word) = Some W_19dcc.
Proof. vm_refl. Qed.
Lemma D_19dcc : decode_any W_19dcc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dd0 : bv 32 := 0x00060413.
Lemma F_19dd0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19eb8 : word) = Some W_19dd0.
Proof. vm_refl. Qed.
Lemma D_19dd0 : decode_any W_19dd0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dd4 : bv 32 := 0x00058493.
Lemma F_19dd4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ebc : word) = Some W_19dd4.
Proof. vm_refl. Qed.
Lemma D_19dd4 : decode_any W_19dd4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dd8 : bv 32 := 0x00050913.
Lemma F_19dd8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ec0 : word) = Some W_19dd8.
Proof. vm_refl. Qed.
Lemma D_19dd8 : decode_any W_19dd8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ddc : bv 32 := 0x00359513.
Lemma F_19ddc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ec4 : word) = Some W_19ddc.
Proof. vm_refl. Qed.
Lemma D_19ddc : decode_any W_19ddc = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19de0 : bv 32 := 0x00a60533.
Lemma F_19de0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ec8 : word) = Some W_19de0.
Proof. vm_refl. Qed.
Lemma D_19de0 : decode_any W_19de0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19de4 : bv 32 := 0x00850993.
Lemma F_19de4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ecc : word) = Some W_19de4.
Proof. vm_refl. Qed.
Lemma D_19de4 : decode_any W_19de4 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19de8 : bv 32 := 0xf25ff0ef.
Lemma F_19de8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ed0 : word) = Some W_19de8.
Proof. vm_refl. Qed.
Lemma D_19de8 : decode_any W_19de8 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dec : bv 32 := 0x00048513.
Lemma F_19dec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ed4 : word) = Some W_19dec.
Proof. vm_refl. Qed.
Lemma D_19dec : decode_any W_19dec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19df0 : bv 32 := 0x00040593.
Lemma F_19df0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ed8 : word) = Some W_19df0.
Proof. vm_refl. Qed.
Lemma D_19df0 : decode_any W_19df0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19df4 : bv 32 := 0x00098613.
Lemma F_19df4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19edc : word) = Some W_19df4.
Proof. vm_refl. Qed.
Lemma D_19df4 : decode_any W_19df4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19df8 : bv 32 := 0x000900e7.
Lemma F_19df8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ee0 : word) = Some W_19df8.
Proof. vm_refl. Qed.
Lemma D_19df8 : decode_any W_19df8 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dfc : bv 32 := 0x498000ef.
Lemma F_19dfc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ee4 : word) = Some W_19dfc.
Proof. vm_refl. Qed.
Lemma D_19dfc : decode_any W_19dfc = Some (Jal 1 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e00 : bv 32 := 0xfc010113.
Lemma F_19e00 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ee8 : word) = Some W_19e00.
Proof. vm_refl. Qed.
Lemma D_19e00 : decode_any W_19e00 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19eec : bv 32 := 0x02113c23.
Lemma TF_19eec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19eec : word) = Some TW_19eec.
Proof. vm_refl. Qed.
Lemma TD_19eec : decode_any TW_19eec = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ef0 : bv 32 := 0x02813823.
Lemma TF_19ef0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ef0 : word) = Some TW_19ef0.
Proof. vm_refl. Qed.
Lemma TD_19ef0 : decode_any TW_19ef0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ef4 : bv 32 := 0x02913423.
Lemma TF_19ef4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ef4 : word) = Some TW_19ef4.
Proof. vm_refl. Qed.
Lemma TD_19ef4 : decode_any TW_19ef4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ef8 : bv 32 := 0x03213023.
Lemma TF_19ef8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ef8 : word) = Some TW_19ef8.
Proof. vm_refl. Qed.
Lemma TD_19ef8 : decode_any TW_19ef8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19efc : bv 32 := 0x01313c23.
Lemma TF_19efc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19efc : word) = Some TW_19efc.
Proof. vm_refl. Qed.
Lemma TD_19efc : decode_any TW_19efc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f00 : bv 32 := 0x01413823.
Lemma TF_19f00 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f00 : word) = Some TW_19f00.
Proof. vm_refl. Qed.
Lemma TD_19f00 : decode_any TW_19f00 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f04 : bv 32 := 0x01513423.
Lemma TF_19f04 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f04 : word) = Some TW_19f04.
Proof. vm_refl. Qed.
Lemma TD_19f04 : decode_any TW_19f04 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f08 : bv 32 := 0x02853683.
Lemma TF_19f08 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f08 : word) = Some TW_19f08.
Proof. vm_refl. Qed.
Lemma TD_19f08 : decode_any TW_19f08 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f0c : bv 32 := 0x0007a597.
Lemma TF_19f0c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f0c : word) = Some TW_19f0c.
Proof. vm_refl. Qed.
Lemma TD_19f0c : decode_any TW_19f0c = Some (Auipc 11 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f10 : bv 32 := 0x33c58593.
Lemma TF_19f10 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f10 : word) = Some TW_19f10.
Proof. vm_refl. Qed.
Lemma TD_19f10 : decode_any TW_19f10 = Some (OpImm ALU_ADD 11 11 828, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f14 : bv 32 := 0x0007a617.
Lemma TF_19f14 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f14 : word) = Some TW_19f14.
Proof. vm_refl. Qed.
Lemma TD_19f14 : decode_any TW_19f14 = Some (Auipc 12 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f18 : bv 32 := 0x5b460493.
Lemma TF_19f18 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f18 : word) = Some TW_19f18.
Proof. vm_refl. Qed.
Lemma TD_19f18 : decode_any TW_19f18 = Some (OpImm ALU_ADD 9 12 1460, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f1c : bv 32 := 0x0c068e63.
Lemma TF_19f1c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f1c : word) = Some TW_19f1c.
Proof. vm_refl. Qed.
Lemma TD_19f1c : decode_any TW_19f1c = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f20 : bv 32 := 0x00000613.
Lemma TF_19f20 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f20 : word) = Some TW_19f20.
Proof. vm_refl. Qed.
Lemma TD_19f20 : decode_any TW_19f20 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f24 : bv 32 := 0x00000893.
Lemma TF_19f24 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f24 : word) = Some TW_19f24.
Proof. vm_refl. Qed.
Lemma TD_19f24 : decode_any TW_19f24 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f28 : bv 32 := 0x0000a717.
Lemma TF_19f28 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f28 : word) = Some TW_19f28.
Proof. vm_refl. Qed.
Lemma TD_19f28 : decode_any TW_19f28 = Some (Auipc 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f2c : bv 32 := 0x01853783.
Lemma TF_19f2c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f2c : word) = Some TW_19f2c.
Proof. vm_refl. Qed.
Lemma TD_19f2c : decode_any TW_19f2c = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f30 : bv 32 := 0x02053503.
Lemma TF_19f30 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f30 : word) = Some TW_19f30.
Proof. vm_refl. Qed.
Lemma TD_19f30 : decode_any TW_19f30 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f34 : bv 32 := 0x00600813.
Lemma TF_19f34 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f34 : word) = Some TW_19f34.
Proof. vm_refl. Qed.
Lemma TD_19f34 : decode_any TW_19f34 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f38 : bv 32 := 0x00009297.
Lemma TF_19f38 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f38 : word) = Some TW_19f38.
Proof. vm_refl. Qed.
Lemma TD_19f38 : decode_any TW_19f38 = Some (Auipc 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f3c : bv 32 := 0x1b876f03.
Lemma TF_19f3c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f3c : word) = Some TW_19f3c.
Proof. vm_refl. Qed.
Lemma TD_19f3c : decode_any TW_19f3c = Some (Load SZ4 false 30 14 440, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f40 : bv 32 := 0xf102b283.
Lemma TF_19f40 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f40 : word) = Some TW_19f40.
Proof. vm_refl. Qed.
Lemma TD_19f40 : decode_any TW_19f40 = Some (Load SZ8 true 5 5 3856, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f44 : bv 32 := 0x00200313.
Lemma TF_19f44 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f44 : word) = Some TW_19f44.
Proof. vm_refl. Qed.
Lemma TD_19f44 : decode_any TW_19f44 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f48 : bv 32 := 0x00700393.
Lemma TF_19f48 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f48 : word) = Some TW_19f48.
Proof. vm_refl. Qed.
Lemma TD_19f48 : decode_any TW_19f48 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f4c : bv 32 := 0x6474ee37.
Lemma TF_19f4c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f4c : word) = Some TW_19f4c.
Proof. vm_refl. Qed.
Lemma TD_19f4c : decode_any TW_19f4c = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f50 : bv 32 := 0x551e0e1b.
Lemma TF_19f50 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f50 : word) = Some TW_19f50.
Proof. vm_refl. Qed.
Lemma TD_19f50 : decode_any TW_19f50 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f54 : bv 32 := 0x00078e93.
Lemma TF_19f54 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f54 : word) = Some TW_19f54.
Proof. vm_refl. Qed.
Lemma TD_19f54 : decode_any TW_19f54 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f58 : bv 32 := 0x0180006f.
Lemma TF_19f58 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f58 : word) = Some TW_19f58.
Proof. vm_refl. Qed.
Lemma TD_19f58 : decode_any TW_19f58 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f5c : bv 32 := 0x010eb603.
Lemma TF_19f5c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f5c : word) = Some TW_19f5c.
Proof. vm_refl. Qed.
Lemma TD_19f5c : decode_any TW_19f5c = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f60 : bv 32 := 0x40c78633.
Lemma TF_19f60 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f60 : word) = Some TW_19f60.
Proof. vm_refl. Qed.
Lemma TD_19f60 : decode_any TW_19f60 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f64 : bv 32 := 0xfff68693.
Lemma TF_19f64 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f64 : word) = Some TW_19f64.
Proof. vm_refl. Qed.
Lemma TD_19f64 : decode_any TW_19f64 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f68 : bv 32 := 0x00ae8eb3.
Lemma TF_19f68 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f68 : word) = Some TW_19f68.
Proof. vm_refl. Qed.
Lemma TD_19f68 : decode_any TW_19f68 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f6c : bv 32 := 0x04068a63.
Lemma TF_19f6c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f6c : word) = Some TW_19f6c.
Proof. vm_refl. Qed.
Lemma TD_19f6c : decode_any TW_19f6c = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f70 : bv 32 := 0x000ea403.
Lemma TF_19f70 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f70 : word) = Some TW_19f70.
Proof. vm_refl. Qed.
Lemma TD_19f70 : decode_any TW_19f70 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f74 : bv 32 := 0xff0404e3.
Lemma TF_19f74 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f74 : word) = Some TW_19f74.
Proof. vm_refl. Qed.
Lemma TD_19f74 : decode_any TW_19f74 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f78 : bv 32 := 0x00028a63.
Lemma TF_19f78 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f78 : word) = Some TW_19f78.
Proof. vm_refl. Qed.
Lemma TD_19f78 : decode_any TW_19f78 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f7c : bv 32 := 0x00641863.
Lemma TF_19f7c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f7c : word) = Some TW_19f7c.
Proof. vm_refl. Qed.
Lemma TD_19f7c : decode_any TW_19f7c = Some (Branch BC_NE 8 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f80 : bv 32 := 0x010eb603.
Lemma TF_19f80 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f80 : word) = Some TW_19f80.
Proof. vm_refl. Qed.
Lemma TD_19f80 : decode_any TW_19f80 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f84 : bv 32 := 0x40c28633.
Lemma TF_19f84 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f84 : word) = Some TW_19f84.
Proof. vm_refl. Qed.
Lemma TD_19f84 : decode_any TW_19f84 = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f88 : bv 32 := 0xfddff06f.
Lemma TF_19f88 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f88 : word) = Some TW_19f88.
Proof. vm_refl. Qed.
Lemma TD_19f88 : decode_any TW_19f88 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f8c : bv 32 := 0x000e8f93.
Lemma TF_19f8c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f8c : word) = Some TW_19f8c.
Proof. vm_refl. Qed.
Lemma TD_19f8c : decode_any TW_19f8c = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f90 : bv 32 := 0x00740463.
Lemma TF_19f90 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f90 : word) = Some TW_19f90.
Proof. vm_refl. Qed.
Lemma TD_19f90 : decode_any TW_19f90 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f94 : bv 32 := 0x00088f93.
Lemma TF_19f94 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f94 : word) = Some TW_19f94.
Proof. vm_refl. Qed.
Lemma TD_19f94 : decode_any TW_19f94 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f98 : bv 32 := 0x03c41063.
Lemma TF_19f98 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f98 : word) = Some TW_19f98.
Proof. vm_refl. Qed.
Lemma TD_19f98 : decode_any TW_19f98 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19f9c : bv 32 := 0x028eb883.
Lemma TF_19f9c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19f9c : word) = Some TW_19f9c.
Proof. vm_refl. Qed.
Lemma TD_19f9c : decode_any TW_19f9c = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fa0 : bv 32 := 0x011f7c63.
Lemma TF_19fa0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fa0 : word) = Some TW_19fa0.
Proof. vm_refl. Qed.
Lemma TD_19fa0 : decode_any TW_19fa0 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fa4 : bv 32 := 0x00800f37.
Lemma TF_19fa4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fa4 : word) = Some TW_19fa4.
Proof. vm_refl. Qed.
Lemma TD_19fa4 : decode_any TW_19fa4 = Some (Lui 30 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fa8 : bv 32 := 0x01e8e463.
Lemma TF_19fa8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fa8 : word) = Some TW_19fa8.
Proof. vm_refl. Qed.
Lemma TD_19fa8 : decode_any TW_19fa8 = Some (Branch BC_LTU 17 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fac : bv 32 := 0x008008b7.
Lemma TF_19fac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fac : word) = Some TW_19fac.
Proof. vm_refl. Qed.
Lemma TD_19fac : decode_any TW_19fac = Some (Lui 17 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fb0 : bv 32 := 0x1b172c23.
Lemma TF_19fb0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fb0 : word) = Some TW_19fb0.
Proof. vm_refl. Qed.
Lemma TD_19fb0 : decode_any TW_19fb0 = Some (Store SZ4 14 17 440, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fb4 : bv 32 := 0x00088f13.
Lemma TF_19fb4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fb4 : word) = Some TW_19fb4.
Proof. vm_refl. Qed.
Lemma TD_19fb4 : decode_any TW_19fb4 = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fb8 : bv 32 := 0x000f8893.
Lemma TF_19fb8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fb8 : word) = Some TW_19fb8.
Proof. vm_refl. Qed.
Lemma TD_19fb8 : decode_any TW_19fb8 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fbc : bv 32 := 0xfa9ff06f.
Lemma TF_19fbc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fbc : word) = Some TW_19fbc.
Proof. vm_refl. Qed.
Lemma TD_19fbc : decode_any TW_19fbc = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fc0 : bv 32 := 0x02088c63.
Lemma TF_19fc0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fc0 : word) = Some TW_19fc0.
Proof. vm_refl. Qed.
Lemma TD_19fc0 : decode_any TW_19fc0 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fc4 : bv 32 := 0x00858713.
Lemma TF_19fc4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fc4 : word) = Some TW_19fc4.
Proof. vm_refl. Qed.
Lemma TD_19fc4 : decode_any TW_19fc4 = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fc8 : bv 32 := 0x0108b783.
Lemma TF_19fc8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fc8 : word) = Some TW_19fc8.
Proof. vm_refl. Qed.
Lemma TD_19fc8 : decode_any TW_19fc8 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fcc : bv 32 := 0x0208b803.
Lemma TF_19fcc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fcc : word) = Some TW_19fcc.
Proof. vm_refl. Qed.
Lemma TD_19fcc : decode_any TW_19fcc = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fd0 : bv 32 := 0x0288b683.
Lemma TF_19fd0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fd0 : word) = Some TW_19fd0.
Proof. vm_refl. Qed.
Lemma TD_19fd0 : decode_any TW_19fd0 = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fd4 : bv 32 := 0x0308b503.
Lemma TF_19fd4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fd4 : word) = Some TW_19fd4.
Proof. vm_refl. Qed.
Lemma TD_19fd4 : decode_any TW_19fd4 = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fd8 : bv 32 := 0x00c78633.
Lemma TF_19fd8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fd8 : word) = Some TW_19fd8.
Proof. vm_refl. Qed.
Lemma TD_19fd8 : decode_any TW_19fd8 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fdc : bv 32 := 0x00100793.
Lemma TF_19fdc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fdc : word) = Some TW_19fdc.
Proof. vm_refl. Qed.
Lemma TD_19fdc : decode_any TW_19fdc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fe0 : bv 32 := 0x00c5b823.
Lemma TF_19fe0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fe0 : word) = Some TW_19fe0.
Proof. vm_refl. Qed.
Lemma TD_19fe0 : decode_any TW_19fe0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fe4 : bv 32 := 0x0105bc23.
Lemma TF_19fe4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fe4 : word) = Some TW_19fe4.
Proof. vm_refl. Qed.
Lemma TD_19fe4 : decode_any TW_19fe4 = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fe8 : bv 32 := 0x02a5b423.
Lemma TF_19fe8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fe8 : word) = Some TW_19fe8.
Proof. vm_refl. Qed.
Lemma TD_19fe8 : decode_any TW_19fe8 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19fec : bv 32 := 0x00e4b823.
Lemma TF_19fec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19fec : word) = Some TW_19fec.
Proof. vm_refl. Qed.
Lemma TD_19fec : decode_any TW_19fec = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ff0 : bv 32 := 0x02f4b423.
Lemma TF_19ff0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ff0 : word) = Some TW_19ff0.
Proof. vm_refl. Qed.
Lemma TD_19ff0 : decode_any TW_19ff0 = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ff4 : bv 32 := 0x0100006f.
Lemma TF_19ff4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ff4 : word) = Some TW_19ff4.
Proof. vm_refl. Qed.
Lemma TD_19ff4 : decode_any TW_19ff4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ff8 : bv 32 := 0x0105b603.
Lemma TF_19ff8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ff8 : word) = Some TW_19ff8.
Proof. vm_refl. Qed.
Lemma TD_19ff8 : decode_any TW_19ff8 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_19ffc : bv 32 := 0x0205b683.
Lemma TF_19ffc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x19ffc : word) = Some TW_19ffc.
Proof. vm_refl. Qed.
Lemma TD_19ffc : decode_any TW_19ffc = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a000 : bv 32 := 0x0285b503.
Lemma TF_1a000 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a000 : word) = Some TW_1a000.
Proof. vm_refl. Qed.
Lemma TD_1a000 : decode_any TW_1a000 = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a004 : bv 32 := 0x00c68733.
Lemma TF_1a004 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a004 : word) = Some TW_1a004.
Proof. vm_refl. Qed.
Lemma TD_1a004 : decode_any TW_1a004 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a008 : bv 32 := 0xfff50793.
Lemma TF_1a008 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a008 : word) = Some TW_1a008.
Proof. vm_refl. Qed.
Lemma TD_1a008 : decode_any TW_1a008 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a00c : bv 32 := 0x40e00733.
Lemma TF_1a00c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a00c : word) = Some TW_1a00c.
Proof. vm_refl. Qed.
Lemma TD_1a00c : decode_any TW_1a00c = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a010 : bv 32 := 0x00c7f633.
Lemma TF_1a010 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a010 : word) = Some TW_1a010.
Proof. vm_refl. Qed.
Lemma TD_1a010 : decode_any TW_1a010 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a014 : bv 32 := 0x00e7f733.
Lemma TF_1a014 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a014 : word) = Some TW_1a014.
Proof. vm_refl. Qed.
Lemma TD_1a014 : decode_any TW_1a014 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a018 : bv 32 := 0x00700793.
Lemma TF_1a018 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a018 : word) = Some TW_1a018.
Proof. vm_refl. Qed.
Lemma TD_1a018 : decode_any TW_1a018 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a01c : bv 32 := 0x00d706b3.
Lemma TF_1a01c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a01c : word) = Some TW_1a01c.
Proof. vm_refl. Qed.
Lemma TD_1a01c : decode_any TW_1a01c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a020 : bv 32 := 0x02d5b023.
Lemma TF_1a020 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a020 : word) = Some TW_1a020.
Proof. vm_refl. Qed.
Lemma TD_1a020 : decode_any TW_1a020 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a024 : bv 32 := 0x02c5b823.
Lemma TF_1a024 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a024 : word) = Some TW_1a024.
Proof. vm_refl. Qed.
Lemma TD_1a024 : decode_any TW_1a024 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a028 : bv 32 := 0x00a7e663.
Lemma TF_1a028 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a028 : word) = Some TW_1a028.
Proof. vm_refl. Qed.
Lemma TD_1a028 : decode_any TW_1a028 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a02c : bv 32 := 0x00800513.
Lemma TF_1a02c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a02c : word) = Some TW_1a02c.
Proof. vm_refl. Qed.
Lemma TD_1a02c : decode_any TW_1a02c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a030 : bv 32 := 0x02a5b423.
Lemma TF_1a030 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a030 : word) = Some TW_1a030.
Proof. vm_refl. Qed.
Lemma TD_1a030 : decode_any TW_1a030 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a034 : bv 32 := 0x00d60633.
Lemma TF_1a034 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a034 : word) = Some TW_1a034.
Proof. vm_refl. Qed.
Lemma TD_1a034 : decode_any TW_1a034 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a038 : bv 32 := 0x000205b7.
Lemma TF_1a038 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a038 : word) = Some TW_1a038.
Proof. vm_refl. Qed.
Lemma TD_1a038 : decode_any TW_1a038 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a03c : bv 32 := 0x00a60633.
Lemma TF_1a03c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a03c : word) = Some TW_1a03c.
Proof. vm_refl. Qed.
Lemma TD_1a03c : decode_any TW_1a03c = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a040 : bv 32 := 0x0d15869b.
Lemma TF_1a040 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a040 : word) = Some TW_1a040.
Proof. vm_refl. Qed.
Lemma TD_1a040 : decode_any TW_1a040 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a044 : bv 32 := 0x0df60593.
Lemma TF_1a044 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a044 : word) = Some TW_1a044.
Proof. vm_refl. Qed.
Lemma TD_1a044 : decode_any TW_1a044 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a048 : bv 32 := 0xff85f593.
Lemma TF_1a048 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a048 : word) = Some TW_1a048.
Proof. vm_refl. Qed.
Lemma TD_1a048 : decode_any TW_1a048 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a04c : bv 32 := 0x00b4bc23.
Lemma TF_1a04c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a04c : word) = Some TW_1a04c.
Proof. vm_refl. Qed.
Lemma TD_1a04c : decode_any TW_1a04c = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a050 : bv 32 := 0x02a4b023.
Lemma TF_1a050 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a050 : word) = Some TW_1a050.
Proof. vm_refl. Qed.
Lemma TD_1a050 : decode_any TW_1a050 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a054 : bv 32 := 0x02d5ea63.
Lemma TF_1a054 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a054 : word) = Some TW_1a054.
Proof. vm_refl. Qed.
Lemma TD_1a054 : decode_any TW_1a054 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a058 : bv 32 := 0xffff8597.
Lemma TF_1a058 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a058 : word) = Some TW_1a058.
Proof. vm_refl. Qed.
Lemma TD_1a058 : decode_any TW_1a058 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a05c : bv 32 := 0x04000893.
Lemma TF_1a05c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a05c : word) = Some TW_1a05c.
Proof. vm_refl. Qed.
Lemma TD_1a05c : decode_any TW_1a05c = Some (OpImm ALU_ADD 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a060 : bv 32 := 0x00200513.
Lemma TF_1a060 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a060 : word) = Some TW_1a060.
Proof. vm_refl. Qed.
Lemma TD_1a060 : decode_any TW_1a060 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a064 : bv 32 := 0x38858593.
Lemma TF_1a064 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a064 : word) = Some TW_1a064.
Proof. vm_refl. Qed.
Lemma TD_1a064 : decode_any TW_1a064 = Some (OpImm ALU_ADD 11 11 904, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a068 : bv 32 := 0x05b00613.
Lemma TF_1a068 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a068 : word) = Some TW_1a068.
Proof. vm_refl. Qed.
Lemma TD_1a068 : decode_any TW_1a068 = Some (OpImm ALU_ADD 12 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a06c : bv 32 := 0x00000073.
Lemma TF_1a06c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a06c : word) = Some TW_1a06c.
Proof. vm_refl. Qed.
Lemma TD_1a06c : decode_any TW_1a06c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_1a06c : is_ecall TW_1a06c = true.
Proof. reflexivity. Qed.

Definition TW_1a070 : bv 32 := 0x00000023.
Lemma TF_1a070 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a070 : word) = Some TW_1a070.
Proof. vm_refl. Qed.
Lemma TD_1a070 : decode_any TW_1a070 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a074 : bv 32 := 0x05e00893.
Lemma TF_1a074 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a074 : word) = Some TW_1a074.
Proof. vm_refl. Qed.
Lemma TD_1a074 : decode_any TW_1a074 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a078 : bv 32 := 0x07f00513.
Lemma TF_1a078 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a078 : word) = Some TW_1a078.
Proof. vm_refl. Qed.
Lemma TD_1a078 : decode_any TW_1a078 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a07c : bv 32 := 0x00000073.
Lemma TF_1a07c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a07c : word) = Some TW_1a07c.
Proof. vm_refl. Qed.
Lemma TD_1a07c : decode_any TW_1a07c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_1a07c : is_ecall TW_1a07c = true.
Proof. reflexivity. Qed.

Definition TW_1a080 : bv 32 := 0x0184b583.
Lemma TF_1a080 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a080 : word) = Some TW_1a080.
Proof. vm_refl. Qed.
Lemma TD_1a080 : decode_any TW_1a080 = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a084 : bv 32 := 0x0204b503.
Lemma TF_1a084 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a084 : word) = Some TW_1a084.
Proof. vm_refl. Qed.
Lemma TD_1a084 : decode_any TW_1a084 = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a088 : bv 32 := 0x0005a697.
Lemma TF_1a088 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a088 : word) = Some TW_1a088.
Proof. vm_refl. Qed.
Lemma TD_1a088 : decode_any TW_1a088 = Some (Auipc 13 90, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a08c : bv 32 := 0x0104b983.
Lemma TF_1a08c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a08c : word) = Some TW_1a08c.
Proof. vm_refl. Qed.
Lemma TD_1a08c : decode_any TW_1a08c = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a090 : bv 32 := 0x0284b603.
Lemma TF_1a090 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a090 : word) = Some TW_1a090.
Proof. vm_refl. Qed.
Lemma TD_1a090 : decode_any TW_1a090 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a094 : bv 32 := 0xfff50713.
Lemma TF_1a094 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a094 : word) = Some TW_1a094.
Proof. vm_refl. Qed.
Lemma TD_1a094 : decode_any TW_1a094 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a098 : bv 32 := 0xf3800793.
Lemma TF_1a098 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a098 : word) = Some TW_1a098.
Proof. vm_refl. Qed.
Lemma TD_1a098 : decode_any TW_1a098 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a09c : bv 32 := 0x0f068513.
Lemma TF_1a09c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a09c : word) = Some TW_1a09c.
Proof. vm_refl. Qed.
Lemma TD_1a09c : decode_any TW_1a09c = Some (OpImm ALU_ADD 10 13 240, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0a0 : bv 32 := 0x40a787b3.
Lemma TF_1a0a0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0a0 : word) = Some TW_1a0a0.
Proof. vm_refl. Qed.
Lemma TD_1a0a0 : decode_any TW_1a0a0 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0a4 : bv 32 := 0x00f77733.
Lemma TF_1a0a4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0a4 : word) = Some TW_1a0a4.
Proof. vm_refl. Qed.
Lemma TD_1a0a4 : decode_any TW_1a0a4 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0a8 : bv 32 := 0xfff64693.
Lemma TF_1a0a8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0a8 : word) = Some TW_1a0a8.
Proof. vm_refl. Qed.
Lemma TD_1a0a8 : decode_any TW_1a0a8 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0ac : bv 32 := 0x00e50933.
Lemma TF_1a0ac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0ac : word) = Some TW_1a0ac.
Proof. vm_refl. Qed.
Lemma TD_1a0ac : decode_any TW_1a0ac = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0b0 : bv 32 := 0x00369693.
Lemma TF_1a0b0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0b0 : word) = Some TW_1a0b0.
Proof. vm_refl. Qed.
Lemma TD_1a0b0 : decode_any TW_1a0b0 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0b4 : bv 32 := 0x00d506b3.
Lemma TF_1a0b4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0b4 : word) = Some TW_1a0b4.
Proof. vm_refl. Qed.
Lemma TD_1a0b4 : decode_any TW_1a0b4 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0b8 : bv 32 := 0x00b68a33.
Lemma TF_1a0b8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0b8 : word) = Some TW_1a0b8.
Proof. vm_refl. Qed.
Lemma TD_1a0b8 : decode_any TW_1a0b8 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0bc : bv 32 := 0x0c890413.
Lemma TF_1a0bc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0bc : word) = Some TW_1a0bc.
Proof. vm_refl. Qed.
Lemma TD_1a0bc : decode_any TW_1a0bc = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0c0 : bv 32 := 0x04098463.
Lemma TF_1a0c0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0c0 : word) = Some TW_1a0c0.
Proof. vm_refl. Qed.
Lemma TD_1a0c0 : decode_any TW_1a0c0 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0c4 : bv 32 := 0x00361613.
Lemma TF_1a0c4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0c4 : word) = Some TW_1a0c4.
Proof. vm_refl. Qed.
Lemma TD_1a0c4 : decode_any TW_1a0c4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0c8 : bv 32 := 0x40c50533.
Lemma TF_1a0c8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0c8 : word) = Some TW_1a0c8.
Proof. vm_refl. Qed.
Lemma TD_1a0c8 : decode_any TW_1a0c8 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0cc : bv 32 := 0x00b50ab3.
Lemma TF_1a0cc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0cc : word) = Some TW_1a0cc.
Proof. vm_refl. Qed.
Lemma TD_1a0cc : decode_any TW_1a0cc = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0d0 : bv 32 := 0x0289b503.
Lemma TF_1a0d0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0d0 : word) = Some TW_1a0d0.
Proof. vm_refl. Qed.
Lemma TD_1a0d0 : decode_any TW_1a0d0 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0d4 : bv 32 := 0x00a40533.
Lemma TF_1a0d4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0d4 : word) = Some TW_1a0d4.
Proof. vm_refl. Qed.
Lemma TD_1a0d4 : decode_any TW_1a0d4 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0d8 : bv 32 := 0x7ff50513.
Lemma TF_1a0d8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0d8 : word) = Some TW_1a0d8.
Proof. vm_refl. Qed.
Lemma TD_1a0d8 : decode_any TW_1a0d8 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0dc : bv 32 := 0x00150513.
Lemma TF_1a0dc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0dc : word) = Some TW_1a0dc.
Proof. vm_refl. Qed.
Lemma TD_1a0dc : decode_any TW_1a0dc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0e0 : bv 32 := 0x00aab023.
Lemma TF_1a0e0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0e0 : word) = Some TW_1a0e0.
Proof. vm_refl. Qed.
Lemma TD_1a0e0 : decode_any TW_1a0e0 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0e4 : bv 32 := 0x0289b503.
Lemma TF_1a0e4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0e4 : word) = Some TW_1a0e4.
Proof. vm_refl. Qed.
Lemma TD_1a0e4 : decode_any TW_1a0e4 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.
