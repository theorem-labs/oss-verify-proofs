(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a49f8 : bv 32 := 0x00008067.
Lemma F_a49f8 : fetch_word Ubsan.M.loaded_segments (0xa67f4 : word) = Some W_a49f8.
Proof. vm_refl. Qed.
Lemma D_a49f8 : decode_any W_a49f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a49fc : bv 32 := 0xe8010113.
Lemma F_a49fc : fetch_word Ubsan.M.loaded_segments (0xa67f8 : word) = Some W_a49fc.
Proof. vm_refl. Qed.
Lemma D_a49fc : decode_any W_a49fc = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a00 : bv 32 := 0x16113c23.
Lemma F_a4a00 : fetch_word Ubsan.M.loaded_segments (0xa67fc : word) = Some W_a4a00.
Proof. vm_refl. Qed.
Lemma D_a4a00 : decode_any W_a4a00 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a04 : bv 32 := 0x16813823.
Lemma F_a4a04 : fetch_word Ubsan.M.loaded_segments (0xa6800 : word) = Some W_a4a04.
Proof. vm_refl. Qed.
Lemma D_a4a04 : decode_any W_a4a04 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a08 : bv 32 := 0x16913423.
Lemma F_a4a08 : fetch_word Ubsan.M.loaded_segments (0xa6804 : word) = Some W_a4a08.
Proof. vm_refl. Qed.
Lemma D_a4a08 : decode_any W_a4a08 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a0c : bv 32 := 0x17213023.
Lemma F_a4a0c : fetch_word Ubsan.M.loaded_segments (0xa6808 : word) = Some W_a4a0c.
Proof. vm_refl. Qed.
Lemma D_a4a0c : decode_any W_a4a0c = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a10 : bv 32 := 0x00058413.
Lemma F_a4a10 : fetch_word Ubsan.M.loaded_segments (0xa680c : word) = Some W_a4a10.
Proof. vm_refl. Qed.
Lemma D_a4a10 : decode_any W_a4a10 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a14 : bv 32 := 0x00050493.
Lemma F_a4a14 : fetch_word Ubsan.M.loaded_segments (0xa6810 : word) = Some W_a4a14.
Proof. vm_refl. Qed.
Lemma D_a4a14 : decode_any W_a4a14 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a18 : bv 32 := 0x03010513.
Lemma F_a4a18 : fetch_word Ubsan.M.loaded_segments (0xa6814 : word) = Some W_a4a18.
Proof. vm_refl. Qed.
Lemma D_a4a18 : decode_any W_a4a18 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a1c : bv 32 := 0x13000613.
Lemma F_a4a1c : fetch_word Ubsan.M.loaded_segments (0xa6818 : word) = Some W_a4a1c.
Proof. vm_refl. Qed.
Lemma D_a4a1c : decode_any W_a4a1c = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a20 : bv 32 := 0x00000593.
Lemma F_a4a20 : fetch_word Ubsan.M.loaded_segments (0xa681c : word) = Some W_a4a20.
Proof. vm_refl. Qed.
Lemma D_a4a20 : decode_any W_a4a20 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a24 : bv 32 := 0x5f4110ef.
Lemma F_a4a24 : fetch_word Ubsan.M.loaded_segments (0xa6820 : word) = Some W_a4a24.
Proof. vm_refl. Qed.
Lemma D_a4a24 : decode_any W_a4a24 = Some (Jal 1 71156, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a28 : bv 32 := 0x0001d517.
Lemma F_a4a28 : fetch_word Ubsan.M.loaded_segments (0xa6824 : word) = Some W_a4a28.
Proof. vm_refl. Qed.
Lemma D_a4a28 : decode_any W_a4a28 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a2c : bv 32 := 0x1fc53503.
Lemma F_a4a2c : fetch_word Ubsan.M.loaded_segments (0xa6828 : word) = Some W_a4a2c.
Proof. vm_refl. Qed.
Lemma D_a4a2c : decode_any W_a4a2c = Some (Load SZ8 true 10 10 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a30 : bv 32 := 0x00953023.
Lemma F_a4a30 : fetch_word Ubsan.M.loaded_segments (0xa682c : word) = Some W_a4a30.
Proof. vm_refl. Qed.
Lemma D_a4a30 : decode_any W_a4a30 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a34 : bv 32 := 0x0004b503.
Lemma F_a4a34 : fetch_word Ubsan.M.loaded_segments (0xa6830 : word) = Some W_a4a34.
Proof. vm_refl. Qed.
Lemma D_a4a34 : decode_any W_a4a34 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a38 : bv 32 := 0x00848493.
Lemma F_a4a38 : fetch_word Ubsan.M.loaded_segments (0xa6834 : word) = Some W_a4a38.
Proof. vm_refl. Qed.
Lemma D_a4a38 : decode_any W_a4a38 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a3c : bv 32 := 0xfe051ce3.
Lemma F_a4a3c : fetch_word Ubsan.M.loaded_segments (0xa6838 : word) = Some W_a4a3c.
Proof. vm_refl. Qed.
Lemma D_a4a3c : decode_any W_a4a3c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a40 : bv 32 := 0x00050517.
Lemma F_a4a40 : fetch_word Ubsan.M.loaded_segments (0xa683c : word) = Some W_a4a40.
Proof. vm_refl. Qed.
Lemma D_a4a40 : decode_any W_a4a40 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a44 : bv 32 := 0x25450913.
Lemma F_a4a44 : fetch_word Ubsan.M.loaded_segments (0xa6840 : word) = Some W_a4a44.
Proof. vm_refl. Qed.
Lemma D_a4a44 : decode_any W_a4a44 = Some (OpImm ALU_ADD 18 10 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a48 : bv 32 := 0x00993423.
Lemma F_a4a48 : fetch_word Ubsan.M.loaded_segments (0xa6844 : word) = Some W_a4a48.
Proof. vm_refl. Qed.
Lemma D_a4a48 : decode_any W_a4a48 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a4c : bv 32 := 0x0004b583.
Lemma F_a4a4c : fetch_word Ubsan.M.loaded_segments (0xa6848 : word) = Some W_a4a4c.
Proof. vm_refl. Qed.
Lemma D_a4a4c : decode_any W_a4a4c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a50 : bv 32 := 0x04058c63.
Lemma F_a4a50 : fetch_word Ubsan.M.loaded_segments (0xa684c : word) = Some W_a4a50.
Proof. vm_refl. Qed.
Lemma D_a4a50 : decode_any W_a4a50 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a54 : bv 32 := 0x01048493.
Lemma F_a4a54 : fetch_word Ubsan.M.loaded_segments (0xa6850 : word) = Some W_a4a54.
Proof. vm_refl. Qed.
Lemma D_a4a54 : decode_any W_a4a54 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a58 : bv 32 := 0x02500513.
Lemma F_a4a58 : fetch_word Ubsan.M.loaded_segments (0xa6854 : word) = Some W_a4a58.
Proof. vm_refl. Qed.
Lemma D_a4a58 : decode_any W_a4a58 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a5c : bv 32 := 0x03010613.
Lemma F_a4a5c : fetch_word Ubsan.M.loaded_segments (0xa6858 : word) = Some W_a4a5c.
Proof. vm_refl. Qed.
Lemma D_a4a5c : decode_any W_a4a5c = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a60 : bv 32 := 0x0100006f.
Lemma F_a4a60 : fetch_word Ubsan.M.loaded_segments (0xa685c : word) = Some W_a4a60.
Proof. vm_refl. Qed.
Lemma D_a4a60 : decode_any W_a4a60 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a64 : bv 32 := 0x0004b583.
Lemma F_a4a64 : fetch_word Ubsan.M.loaded_segments (0xa6860 : word) = Some W_a4a64.
Proof. vm_refl. Qed.
Lemma D_a4a64 : decode_any W_a4a64 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a68 : bv 32 := 0x01048493.
Lemma F_a4a68 : fetch_word Ubsan.M.loaded_segments (0xa6864 : word) = Some W_a4a68.
Proof. vm_refl. Qed.
Lemma D_a4a68 : decode_any W_a4a68 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a6c : bv 32 := 0x00058e63.
Lemma F_a4a6c : fetch_word Ubsan.M.loaded_segments (0xa6868 : word) = Some W_a4a6c.
Proof. vm_refl. Qed.
Lemma D_a4a6c : decode_any W_a4a6c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a70 : bv 32 := 0xfeb56ae3.
Lemma F_a4a70 : fetch_word Ubsan.M.loaded_segments (0xa686c : word) = Some W_a4a70.
Proof. vm_refl. Qed.
Lemma D_a4a70 : decode_any W_a4a70 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a74 : bv 32 := 0xff84b683.
Lemma F_a4a74 : fetch_word Ubsan.M.loaded_segments (0xa6870 : word) = Some W_a4a74.
Proof. vm_refl. Qed.
Lemma D_a4a74 : decode_any W_a4a74 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a78 : bv 32 := 0x00359593.
Lemma F_a4a78 : fetch_word Ubsan.M.loaded_segments (0xa6874 : word) = Some W_a4a78.
Proof. vm_refl. Qed.
Lemma D_a4a78 : decode_any W_a4a78 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a7c : bv 32 := 0x00b605b3.
Lemma F_a4a7c : fetch_word Ubsan.M.loaded_segments (0xa6878 : word) = Some W_a4a7c.
Proof. vm_refl. Qed.
Lemma D_a4a7c : decode_any W_a4a7c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a80 : bv 32 := 0x00d5b023.
Lemma F_a4a80 : fetch_word Ubsan.M.loaded_segments (0xa687c : word) = Some W_a4a80.
Proof. vm_refl. Qed.
Lemma D_a4a80 : decode_any W_a4a80 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a84 : bv 32 := 0xfe1ff06f.
Lemma F_a4a84 : fetch_word Ubsan.M.loaded_segments (0xa6880 : word) = Some W_a4a84.
Proof. vm_refl. Qed.
Lemma D_a4a84 : decode_any W_a4a84 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a88 : bv 32 := 0x0b013583.
Lemma F_a4a88 : fetch_word Ubsan.M.loaded_segments (0xa6884 : word) = Some W_a4a88.
Proof. vm_refl. Qed.
Lemma D_a4a88 : decode_any W_a4a88 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a8c : bv 32 := 0x13013503.
Lemma F_a4a8c : fetch_word Ubsan.M.loaded_segments (0xa6888 : word) = Some W_a4a8c.
Proof. vm_refl. Qed.
Lemma D_a4a8c : decode_any W_a4a8c = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a90 : bv 32 := 0x00050617.
Lemma F_a4a90 : fetch_word Ubsan.M.loaded_segments (0xa688c : word) = Some W_a4a90.
Proof. vm_refl. Qed.
Lemma D_a4a90 : decode_any W_a4a90 = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a94 : bv 32 := 0x26b63623.
Lemma F_a4a94 : fetch_word Ubsan.M.loaded_segments (0xa6890 : word) = Some W_a4a94.
Proof. vm_refl. Qed.
Lemma D_a4a94 : decode_any W_a4a94 = Some (Store SZ8 12 11 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4a98 : bv 32 := 0x00050c63.
Lemma F_a4a98 : fetch_word Ubsan.M.loaded_segments (0xa6894 : word) = Some W_a4a98.
Proof. vm_refl. Qed.
Lemma D_a4a98 : decode_any W_a4a98 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ab0 : bv 32 := 0x06013503.
Lemma F_a4ab0 : fetch_word Ubsan.M.loaded_segments (0xa68ac : word) = Some W_a4ab0.
Proof. vm_refl. Qed.
Lemma D_a4ab0 : decode_any W_a4ab0 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ab4 : bv 32 := 0x02a93823.
Lemma F_a4ab4 : fetch_word Ubsan.M.loaded_segments (0xa68b0 : word) = Some W_a4ab4.
Proof. vm_refl. Qed.
Lemma D_a4ab4 : decode_any W_a4ab4 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ab8 : bv 32 := 0x00041463.
Lemma F_a4ab8 : fetch_word Ubsan.M.loaded_segments (0xa68b4 : word) = Some W_a4ab8.
Proof. vm_refl. Qed.
Lemma D_a4ab8 : decode_any W_a4ab8 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ac0 : bv 32 := 0x00041663.
Lemma F_a4ac0 : fetch_word Ubsan.M.loaded_segments (0xa68bc : word) = Some W_a4ac0.
Proof. vm_refl. Qed.
Lemma D_a4ac0 : decode_any W_a4ac0 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4acc : bv 32 := 0x0001d517.
Lemma F_a4acc : fetch_word Ubsan.M.loaded_segments (0xa68c8 : word) = Some W_a4acc.
Proof. vm_refl. Qed.
Lemma D_a4acc : decode_any W_a4acc = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ad0 : bv 32 := 0x16053583.
Lemma F_a4ad0 : fetch_word Ubsan.M.loaded_segments (0xa68cc : word) = Some W_a4ad0.
Proof. vm_refl. Qed.
Lemma D_a4ad0 : decode_any W_a4ad0 = Some (Load SZ8 true 11 10 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ad4 : bv 32 := 0x0001d517.
Lemma F_a4ad4 : fetch_word Ubsan.M.loaded_segments (0xa68d0 : word) = Some W_a4ad4.
Proof. vm_refl. Qed.
Lemma D_a4ad4 : decode_any W_a4ad4 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ad8 : bv 32 := 0x16053503.
Lemma F_a4ad8 : fetch_word Ubsan.M.loaded_segments (0xa68d4 : word) = Some W_a4ad8.
Proof. vm_refl. Qed.
Lemma D_a4ad8 : decode_any W_a4ad8 = Some (Load SZ8 true 10 10 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4adc : bv 32 := 0x0085b023.
Lemma F_a4adc : fetch_word Ubsan.M.loaded_segments (0xa68d8 : word) = Some W_a4adc.
Proof. vm_refl. Qed.
Lemma D_a4adc : decode_any W_a4adc = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ae0 : bv 32 := 0x00140593.
Lemma F_a4ae0 : fetch_word Ubsan.M.loaded_segments (0xa68dc : word) = Some W_a4ae0.
Proof. vm_refl. Qed.
Lemma D_a4ae0 : decode_any W_a4ae0 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ae4 : bv 32 := 0x00853023.
Lemma F_a4ae4 : fetch_word Ubsan.M.loaded_segments (0xa68e0 : word) = Some W_a4ae4.
Proof. vm_refl. Qed.
Lemma D_a4ae4 : decode_any W_a4ae4 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ae8 : bv 32 := 0x02f00613.
Lemma F_a4ae8 : fetch_word Ubsan.M.loaded_segments (0xa68e4 : word) = Some W_a4ae8.
Proof. vm_refl. Qed.
Lemma D_a4ae8 : decode_any W_a4ae8 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4aec : bv 32 := 0x00c0006f.
Lemma F_a4aec : fetch_word Ubsan.M.loaded_segments (0xa68e8 : word) = Some W_a4aec.
Proof. vm_refl. Qed.
Lemma D_a4aec : decode_any W_a4aec = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4af0 : bv 32 := 0x00b53023.
Lemma F_a4af0 : fetch_word Ubsan.M.loaded_segments (0xa68ec : word) = Some W_a4af0.
Proof. vm_refl. Qed.
Lemma D_a4af0 : decode_any W_a4af0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4af4 : bv 32 := 0x00158593.
Lemma F_a4af4 : fetch_word Ubsan.M.loaded_segments (0xa68f0 : word) = Some W_a4af4.
Proof. vm_refl. Qed.
Lemma D_a4af4 : decode_any W_a4af4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4af8 : bv 32 := 0xfff5c683.
Lemma F_a4af8 : fetch_word Ubsan.M.loaded_segments (0xa68f4 : word) = Some W_a4af8.
Proof. vm_refl. Qed.
Lemma D_a4af8 : decode_any W_a4af8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4afc : bv 32 := 0xfec68ae3.
Lemma F_a4afc : fetch_word Ubsan.M.loaded_segments (0xa68f8 : word) = Some W_a4afc.
Proof. vm_refl. Qed.
Lemma D_a4afc : decode_any W_a4afc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b00 : bv 32 := 0xfe069ae3.
Lemma F_a4b00 : fetch_word Ubsan.M.loaded_segments (0xa68fc : word) = Some W_a4b00.
Proof. vm_refl. Qed.
Lemma D_a4b00 : decode_any W_a4b00 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b04 : bv 32 := 0x03010513.
Lemma F_a4b04 : fetch_word Ubsan.M.loaded_segments (0xa6900 : word) = Some W_a4b04.
Proof. vm_refl. Qed.
Lemma D_a4b04 : decode_any W_a4b04 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b08 : bv 32 := 0x214000ef.
Lemma F_a4b08 : fetch_word Ubsan.M.loaded_segments (0xa6904 : word) = Some W_a4b08.
Proof. vm_refl. Qed.
Lemma D_a4b08 : decode_any W_a4b08 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b0c : bv 32 := 0x0f813503.
Lemma F_a4b0c : fetch_word Ubsan.M.loaded_segments (0xa6908 : word) = Some W_a4b0c.
Proof. vm_refl. Qed.
Lemma D_a4b0c : decode_any W_a4b0c = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b10 : bv 32 := 0x1ad000ef.
Lemma F_a4b10 : fetch_word Ubsan.M.loaded_segments (0xa690c : word) = Some W_a4b10.
Proof. vm_refl. Qed.
Lemma D_a4b10 : decode_any W_a4b10 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b14 : bv 32 := 0x08813503.
Lemma F_a4b14 : fetch_word Ubsan.M.loaded_segments (0xa6910 : word) = Some W_a4b14.
Proof. vm_refl. Qed.
Lemma D_a4b14 : decode_any W_a4b14 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b18 : bv 32 := 0x09013583.
Lemma F_a4b18 : fetch_word Ubsan.M.loaded_segments (0xa6914 : word) = Some W_a4b18.
Proof. vm_refl. Qed.
Lemma D_a4b18 : decode_any W_a4b18 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b1c : bv 32 := 0x00b51c63.
Lemma F_a4b1c : fetch_word Ubsan.M.loaded_segments (0xa6918 : word) = Some W_a4b1c.
Proof. vm_refl. Qed.
Lemma D_a4b1c : decode_any W_a4b1c = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b20 : bv 32 := 0x09813503.
Lemma F_a4b20 : fetch_word Ubsan.M.loaded_segments (0xa691c : word) = Some W_a4b20.
Proof. vm_refl. Qed.
Lemma D_a4b20 : decode_any W_a4b20 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b24 : bv 32 := 0x0a013583.
Lemma F_a4b24 : fetch_word Ubsan.M.loaded_segments (0xa6920 : word) = Some W_a4b24.
Proof. vm_refl. Qed.
Lemma D_a4b24 : decode_any W_a4b24 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b28 : bv 32 := 0x00b51663.
Lemma F_a4b28 : fetch_word Ubsan.M.loaded_segments (0xa6924 : word) = Some W_a4b28.
Proof. vm_refl. Qed.
Lemma D_a4b28 : decode_any W_a4b28 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b2c : bv 32 := 0x0e813503.
Lemma F_a4b2c : fetch_word Ubsan.M.loaded_segments (0xa6928 : word) = Some W_a4b2c.
Proof. vm_refl. Qed.
Lemma D_a4b2c : decode_any W_a4b2c = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4b30 : bv 32 := 0x0e050063.
Lemma F_a4b30 : fetch_word Ubsan.M.loaded_segments (0xa692c : word) = Some W_a4b30.
Proof. vm_refl. Qed.
Lemma D_a4b30 : decode_any W_a4b30 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c10 : bv 32 := 0x17813083.
Lemma F_a4c10 : fetch_word Ubsan.M.loaded_segments (0xa6a0c : word) = Some W_a4c10.
Proof. vm_refl. Qed.
Lemma D_a4c10 : decode_any W_a4c10 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c14 : bv 32 := 0x17013403.
Lemma F_a4c14 : fetch_word Ubsan.M.loaded_segments (0xa6a10 : word) = Some W_a4c14.
Proof. vm_refl. Qed.
Lemma D_a4c14 : decode_any W_a4c14 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c18 : bv 32 := 0x16813483.
Lemma F_a4c18 : fetch_word Ubsan.M.loaded_segments (0xa6a14 : word) = Some W_a4c18.
Proof. vm_refl. Qed.
Lemma D_a4c18 : decode_any W_a4c18 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c1c : bv 32 := 0x16013903.
Lemma F_a4c1c : fetch_word Ubsan.M.loaded_segments (0xa6a18 : word) = Some W_a4c1c.
Proof. vm_refl. Qed.
Lemma D_a4c1c : decode_any W_a4c1c = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c20 : bv 32 := 0x18010113.
Lemma F_a4c20 : fetch_word Ubsan.M.loaded_segments (0xa6a1c : word) = Some W_a4c20.
Proof. vm_refl. Qed.
Lemma D_a4c20 : decode_any W_a4c20 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c24 : bv 32 := 0x00008067.
Lemma F_a4c24 : fetch_word Ubsan.M.loaded_segments (0xa6a20 : word) = Some W_a4c24.
Proof. vm_refl. Qed.
Lemma D_a4c24 : decode_any W_a4c24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c28 : bv 32 := 0xfe010113.
Lemma F_a4c28 : fetch_word Ubsan.M.loaded_segments (0xa6a24 : word) = Some W_a4c28.
Proof. vm_refl. Qed.
Lemma D_a4c28 : decode_any W_a4c28 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c2c : bv 32 := 0x00113c23.
Lemma F_a4c2c : fetch_word Ubsan.M.loaded_segments (0xa6a28 : word) = Some W_a4c2c.
Proof. vm_refl. Qed.
Lemma D_a4c2c : decode_any W_a4c2c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c30 : bv 32 := 0x00813823.
Lemma F_a4c30 : fetch_word Ubsan.M.loaded_segments (0xa6a2c : word) = Some W_a4c30.
Proof. vm_refl. Qed.
Lemma D_a4c30 : decode_any W_a4c30 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c34 : bv 32 := 0x00913423.
Lemma F_a4c34 : fetch_word Ubsan.M.loaded_segments (0xa6a30 : word) = Some W_a4c34.
Proof. vm_refl. Qed.
Lemma D_a4c34 : decode_any W_a4c34 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c38 : bv 32 := 0xdc1ff0ef.
Lemma F_a4c38 : fetch_word Ubsan.M.loaded_segments (0xa6a34 : word) = Some W_a4c38.
Proof. vm_refl. Qed.
Lemma D_a4c38 : decode_any W_a4c38 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c3c : bv 32 := 0x0001d517.
Lemma F_a4c3c : fetch_word Ubsan.M.loaded_segments (0xa6a38 : word) = Some W_a4c3c.
Proof. vm_refl. Qed.
Lemma D_a4c3c : decode_any W_a4c3c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c40 : bv 32 := 0x0001d597.
Lemma F_a4c40 : fetch_word Ubsan.M.loaded_segments (0xa6a3c : word) = Some W_a4c40.
Proof. vm_refl. Qed.
Lemma D_a4c40 : decode_any W_a4c40 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c44 : bv 32 := 0x00053403.
Lemma F_a4c44 : fetch_word Ubsan.M.loaded_segments (0xa6a40 : word) = Some W_a4c44.
Proof. vm_refl. Qed.
Lemma D_a4c44 : decode_any W_a4c44 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c48 : bv 32 := 0x0045b483.
Lemma F_a4c48 : fetch_word Ubsan.M.loaded_segments (0xa6a44 : word) = Some W_a4c48.
Proof. vm_refl. Qed.
Lemma D_a4c48 : decode_any W_a4c48 = Some (Load SZ8 true 9 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c4c : bv 32 := 0x0084fa63.
Lemma F_a4c4c : fetch_word Ubsan.M.loaded_segments (0xa6a48 : word) = Some W_a4c4c.
Proof. vm_refl. Qed.
Lemma D_a4c4c : decode_any W_a4c4c = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c50 : bv 32 := 0x0004b503.
Lemma F_a4c50 : fetch_word Ubsan.M.loaded_segments (0xa6a4c : word) = Some W_a4c50.
Proof. vm_refl. Qed.
Lemma D_a4c50 : decode_any W_a4c50 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c54 : bv 32 := 0x000500e7.
Lemma F_a4c54 : fetch_word Ubsan.M.loaded_segments (0xa6a50 : word) = Some W_a4c54.
Proof. vm_refl. Qed.
Lemma D_a4c54 : decode_any W_a4c54 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c58 : bv 32 := 0x00848493.
Lemma F_a4c58 : fetch_word Ubsan.M.loaded_segments (0xa6a54 : word) = Some W_a4c58.
Proof. vm_refl. Qed.
Lemma D_a4c58 : decode_any W_a4c58 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c5c : bv 32 := 0xfe84eae3.
Lemma F_a4c5c : fetch_word Ubsan.M.loaded_segments (0xa6a58 : word) = Some W_a4c5c.
Proof. vm_refl. Qed.
Lemma D_a4c5c : decode_any W_a4c5c = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c60 : bv 32 := 0x01813083.
Lemma F_a4c60 : fetch_word Ubsan.M.loaded_segments (0xa6a5c : word) = Some W_a4c60.
Proof. vm_refl. Qed.
Lemma D_a4c60 : decode_any W_a4c60 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c64 : bv 32 := 0x01013403.
Lemma F_a4c64 : fetch_word Ubsan.M.loaded_segments (0xa6a60 : word) = Some W_a4c64.
Proof. vm_refl. Qed.
Lemma D_a4c64 : decode_any W_a4c64 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c68 : bv 32 := 0x00813483.
Lemma F_a4c68 : fetch_word Ubsan.M.loaded_segments (0xa6a64 : word) = Some W_a4c68.
Proof. vm_refl. Qed.
Lemma D_a4c68 : decode_any W_a4c68 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c6c : bv 32 := 0x02010113.
Lemma F_a4c6c : fetch_word Ubsan.M.loaded_segments (0xa6a68 : word) = Some W_a4c6c.
Proof. vm_refl. Qed.
Lemma D_a4c6c : decode_any W_a4c6c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c70 : bv 32 := 0x00008067.
Lemma F_a4c70 : fetch_word Ubsan.M.loaded_segments (0xa6a6c : word) = Some W_a4c70.
Proof. vm_refl. Qed.
Lemma D_a4c70 : decode_any W_a4c70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c74 : bv 32 := 0xfe010113.
Lemma F_a4c74 : fetch_word Ubsan.M.loaded_segments (0xa6a70 : word) = Some W_a4c74.
Proof. vm_refl. Qed.
Lemma D_a4c74 : decode_any W_a4c74 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c78 : bv 32 := 0x00113c23.
Lemma F_a4c78 : fetch_word Ubsan.M.loaded_segments (0xa6a74 : word) = Some W_a4c78.
Proof. vm_refl. Qed.
Lemma D_a4c78 : decode_any W_a4c78 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c7c : bv 32 := 0x00813823.
Lemma F_a4c7c : fetch_word Ubsan.M.loaded_segments (0xa6a78 : word) = Some W_a4c7c.
Proof. vm_refl. Qed.
Lemma D_a4c7c : decode_any W_a4c7c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c80 : bv 32 := 0x00913423.
Lemma F_a4c80 : fetch_word Ubsan.M.loaded_segments (0xa6a7c : word) = Some W_a4c80.
Proof. vm_refl. Qed.
Lemma D_a4c80 : decode_any W_a4c80 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c84 : bv 32 := 0x01213023.
Lemma F_a4c84 : fetch_word Ubsan.M.loaded_segments (0xa6a80 : word) = Some W_a4c84.
Proof. vm_refl. Qed.
Lemma D_a4c84 : decode_any W_a4c84 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c88 : bv 32 := 0x00060413.
Lemma F_a4c88 : fetch_word Ubsan.M.loaded_segments (0xa6a84 : word) = Some W_a4c88.
Proof. vm_refl. Qed.
Lemma D_a4c88 : decode_any W_a4c88 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c8c : bv 32 := 0x00058493.
Lemma F_a4c8c : fetch_word Ubsan.M.loaded_segments (0xa6a88 : word) = Some W_a4c8c.
Proof. vm_refl. Qed.
Lemma D_a4c8c : decode_any W_a4c8c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c90 : bv 32 := 0x00050913.
Lemma F_a4c90 : fetch_word Ubsan.M.loaded_segments (0xa6a8c : word) = Some W_a4c90.
Proof. vm_refl. Qed.
Lemma D_a4c90 : decode_any W_a4c90 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c94 : bv 32 := 0x00063583.
Lemma F_a4c94 : fetch_word Ubsan.M.loaded_segments (0xa6a90 : word) = Some W_a4c94.
Proof. vm_refl. Qed.
Lemma D_a4c94 : decode_any W_a4c94 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c98 : bv 32 := 0x00349513.
Lemma F_a4c98 : fetch_word Ubsan.M.loaded_segments (0xa6a94 : word) = Some W_a4c98.
Proof. vm_refl. Qed.
Lemma D_a4c98 : decode_any W_a4c98 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4c9c : bv 32 := 0x00a60533.
Lemma F_a4c9c : fetch_word Ubsan.M.loaded_segments (0xa6a98 : word) = Some W_a4c9c.
Proof. vm_refl. Qed.
Lemma D_a4c9c : decode_any W_a4c9c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ca0 : bv 32 := 0x00850513.
Lemma F_a4ca0 : fetch_word Ubsan.M.loaded_segments (0xa6a9c : word) = Some W_a4ca0.
Proof. vm_refl. Qed.
Lemma D_a4ca0 : decode_any W_a4ca0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ca4 : bv 32 := 0xd59ff0ef.
Lemma F_a4ca4 : fetch_word Ubsan.M.loaded_segments (0xa6aa0 : word) = Some W_a4ca4.
Proof. vm_refl. Qed.
Lemma D_a4ca4 : decode_any W_a4ca4 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ca8 : bv 32 := 0x00000517.
Lemma F_a4ca8 : fetch_word Ubsan.M.loaded_segments (0xa6aa4 : word) = Some W_a4ca8.
Proof. vm_refl. Qed.
Lemma D_a4ca8 : decode_any W_a4ca8 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cac : bv 32 := 0x02c50313.
Lemma F_a4cac : fetch_word Ubsan.M.loaded_segments (0xa6aa8 : word) = Some W_a4cac.
Proof. vm_refl. Qed.
Lemma D_a4cac : decode_any W_a4cac = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cb0 : bv 32 := 0x00090513.
Lemma F_a4cb0 : fetch_word Ubsan.M.loaded_segments (0xa6aac : word) = Some W_a4cb0.
Proof. vm_refl. Qed.
Lemma D_a4cb0 : decode_any W_a4cb0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cb4 : bv 32 := 0x00048593.
Lemma F_a4cb4 : fetch_word Ubsan.M.loaded_segments (0xa6ab0 : word) = Some W_a4cb4.
Proof. vm_refl. Qed.
Lemma D_a4cb4 : decode_any W_a4cb4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cb8 : bv 32 := 0x00040613.
Lemma F_a4cb8 : fetch_word Ubsan.M.loaded_segments (0xa6ab4 : word) = Some W_a4cb8.
Proof. vm_refl. Qed.
Lemma D_a4cb8 : decode_any W_a4cb8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cbc : bv 32 := 0x01813083.
Lemma F_a4cbc : fetch_word Ubsan.M.loaded_segments (0xa6ab8 : word) = Some W_a4cbc.
Proof. vm_refl. Qed.
Lemma D_a4cbc : decode_any W_a4cbc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cc0 : bv 32 := 0x01013403.
Lemma F_a4cc0 : fetch_word Ubsan.M.loaded_segments (0xa6abc : word) = Some W_a4cc0.
Proof. vm_refl. Qed.
Lemma D_a4cc0 : decode_any W_a4cc0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cc4 : bv 32 := 0x00813483.
Lemma F_a4cc4 : fetch_word Ubsan.M.loaded_segments (0xa6ac0 : word) = Some W_a4cc4.
Proof. vm_refl. Qed.
Lemma D_a4cc4 : decode_any W_a4cc4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cc8 : bv 32 := 0x00013903.
Lemma F_a4cc8 : fetch_word Ubsan.M.loaded_segments (0xa6ac4 : word) = Some W_a4cc8.
Proof. vm_refl. Qed.
Lemma D_a4cc8 : decode_any W_a4cc8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ccc : bv 32 := 0x02010113.
Lemma F_a4ccc : fetch_word Ubsan.M.loaded_segments (0xa6ac8 : word) = Some W_a4ccc.
Proof. vm_refl. Qed.
Lemma D_a4ccc : decode_any W_a4ccc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cd0 : bv 32 := 0x00030067.
Lemma F_a4cd0 : fetch_word Ubsan.M.loaded_segments (0xa6acc : word) = Some W_a4cd0.
Proof. vm_refl. Qed.
Lemma D_a4cd0 : decode_any W_a4cd0 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cd4 : bv 32 := 0xfd010113.
Lemma F_a4cd4 : fetch_word Ubsan.M.loaded_segments (0xa6ad0 : word) = Some W_a4cd4.
Proof. vm_refl. Qed.
Lemma D_a4cd4 : decode_any W_a4cd4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cd8 : bv 32 := 0x02113423.
Lemma F_a4cd8 : fetch_word Ubsan.M.loaded_segments (0xa6ad4 : word) = Some W_a4cd8.
Proof. vm_refl. Qed.
Lemma D_a4cd8 : decode_any W_a4cd8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cdc : bv 32 := 0x02813023.
Lemma F_a4cdc : fetch_word Ubsan.M.loaded_segments (0xa6ad8 : word) = Some W_a4cdc.
Proof. vm_refl. Qed.
Lemma D_a4cdc : decode_any W_a4cdc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ce0 : bv 32 := 0x00913c23.
Lemma F_a4ce0 : fetch_word Ubsan.M.loaded_segments (0xa6adc : word) = Some W_a4ce0.
Proof. vm_refl. Qed.
Lemma D_a4ce0 : decode_any W_a4ce0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ce4 : bv 32 := 0x01213823.
Lemma F_a4ce4 : fetch_word Ubsan.M.loaded_segments (0xa6ae0 : word) = Some W_a4ce4.
Proof. vm_refl. Qed.
Lemma D_a4ce4 : decode_any W_a4ce4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ce8 : bv 32 := 0x01313423.
Lemma F_a4ce8 : fetch_word Ubsan.M.loaded_segments (0xa6ae4 : word) = Some W_a4ce8.
Proof. vm_refl. Qed.
Lemma D_a4ce8 : decode_any W_a4ce8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cec : bv 32 := 0x00060413.
Lemma F_a4cec : fetch_word Ubsan.M.loaded_segments (0xa6ae8 : word) = Some W_a4cec.
Proof. vm_refl. Qed.
Lemma D_a4cec : decode_any W_a4cec = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cf0 : bv 32 := 0x00058493.
Lemma F_a4cf0 : fetch_word Ubsan.M.loaded_segments (0xa6aec : word) = Some W_a4cf0.
Proof. vm_refl. Qed.
Lemma D_a4cf0 : decode_any W_a4cf0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cf4 : bv 32 := 0x00050913.
Lemma F_a4cf4 : fetch_word Ubsan.M.loaded_segments (0xa6af0 : word) = Some W_a4cf4.
Proof. vm_refl. Qed.
Lemma D_a4cf4 : decode_any W_a4cf4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cf8 : bv 32 := 0x00359513.
Lemma F_a4cf8 : fetch_word Ubsan.M.loaded_segments (0xa6af4 : word) = Some W_a4cf8.
Proof. vm_refl. Qed.
Lemma D_a4cf8 : decode_any W_a4cf8 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4cfc : bv 32 := 0x00a60533.
Lemma F_a4cfc : fetch_word Ubsan.M.loaded_segments (0xa6af8 : word) = Some W_a4cfc.
Proof. vm_refl. Qed.
Lemma D_a4cfc : decode_any W_a4cfc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4d00 : bv 32 := 0x00850993.
Lemma F_a4d00 : fetch_word Ubsan.M.loaded_segments (0xa6afc : word) = Some W_a4d00.
Proof. vm_refl. Qed.
Lemma D_a4d00 : decode_any W_a4d00 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4d04 : bv 32 := 0xf25ff0ef.
Lemma F_a4d04 : fetch_word Ubsan.M.loaded_segments (0xa6b00 : word) = Some W_a4d04.
Proof. vm_refl. Qed.
Lemma D_a4d04 : decode_any W_a4d04 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4d08 : bv 32 := 0x00048513.
Lemma F_a4d08 : fetch_word Ubsan.M.loaded_segments (0xa6b04 : word) = Some W_a4d08.
Proof. vm_refl. Qed.
Lemma D_a4d08 : decode_any W_a4d08 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4d0c : bv 32 := 0x00040593.
Lemma F_a4d0c : fetch_word Ubsan.M.loaded_segments (0xa6b08 : word) = Some W_a4d0c.
Proof. vm_refl. Qed.
Lemma D_a4d0c : decode_any W_a4d0c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4d10 : bv 32 := 0x00098613.
Lemma F_a4d10 : fetch_word Ubsan.M.loaded_segments (0xa6b0c : word) = Some W_a4d10.
Proof. vm_refl. Qed.
Lemma D_a4d10 : decode_any W_a4d10 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4d14 : bv 32 := 0x000900e7.
Lemma F_a4d14 : fetch_word Ubsan.M.loaded_segments (0xa6b10 : word) = Some W_a4d14.
Proof. vm_refl. Qed.
Lemma D_a4d14 : decode_any W_a4d14 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

