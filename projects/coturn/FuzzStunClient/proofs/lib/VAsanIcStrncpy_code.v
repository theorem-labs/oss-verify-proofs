(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_442c0 : bv 32 := 0x1110506f.
Lemma F_442c0 : fetch_word Asan.M.loaded_segments (0x442c0 : word) = Some W_442c0.
Proof. vm_refl. Qed.
Lemma D_442c0 : decode_any W_442c0 = Some (Jal 0 22800, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_49bd0 : bv 32 := 0x81010113.
Lemma F_49bd0 : fetch_word Asan.M.loaded_segments (0x49bd0 : word) = Some W_49bd0.
Proof. vm_refl. Qed.
Lemma D_49bd0 : decode_any W_49bd0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bd4 : bv 32 := 0x7e113423.
Lemma F_49bd4 : fetch_word Asan.M.loaded_segments (0x49bd4 : word) = Some W_49bd4.
Proof. vm_refl. Qed.
Lemma D_49bd4 : decode_any W_49bd4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bd8 : bv 32 := 0x7e813023.
Lemma F_49bd8 : fetch_word Asan.M.loaded_segments (0x49bd8 : word) = Some W_49bd8.
Proof. vm_refl. Qed.
Lemma D_49bd8 : decode_any W_49bd8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bdc : bv 32 := 0x7c913c23.
Lemma F_49bdc : fetch_word Asan.M.loaded_segments (0x49bdc : word) = Some W_49bdc.
Proof. vm_refl. Qed.
Lemma D_49bdc : decode_any W_49bdc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49be0 : bv 32 := 0x7d213823.
Lemma F_49be0 : fetch_word Asan.M.loaded_segments (0x49be0 : word) = Some W_49be0.
Proof. vm_refl. Qed.
Lemma D_49be0 : decode_any W_49be0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49be4 : bv 32 := 0x7d313423.
Lemma F_49be4 : fetch_word Asan.M.loaded_segments (0x49be4 : word) = Some W_49be4.
Proof. vm_refl. Qed.
Lemma D_49be4 : decode_any W_49be4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49be8 : bv 32 := 0x7d413023.
Lemma F_49be8 : fetch_word Asan.M.loaded_segments (0x49be8 : word) = Some W_49be8.
Proof. vm_refl. Qed.
Lemma D_49be8 : decode_any W_49be8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bec : bv 32 := 0x7b513c23.
Lemma F_49bec : fetch_word Asan.M.loaded_segments (0x49bec : word) = Some W_49bec.
Proof. vm_refl. Qed.
Lemma D_49bec : decode_any W_49bec = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bf0 : bv 32 := 0x7b613823.
Lemma F_49bf0 : fetch_word Asan.M.loaded_segments (0x49bf0 : word) = Some W_49bf0.
Proof. vm_refl. Qed.
Lemma D_49bf0 : decode_any W_49bf0 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bf4 : bv 32 := 0x7b713423.
Lemma F_49bf4 : fetch_word Asan.M.loaded_segments (0x49bf4 : word) = Some W_49bf4.
Proof. vm_refl. Qed.
Lemma D_49bf4 : decode_any W_49bf4 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bf8 : bv 32 := 0x7b813023.
Lemma F_49bf8 : fetch_word Asan.M.loaded_segments (0x49bf8 : word) = Some W_49bf8.
Proof. vm_refl. Qed.
Lemma D_49bf8 : decode_any W_49bf8 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49bfc : bv 32 := 0x7f010413.
Lemma F_49bfc : fetch_word Asan.M.loaded_segments (0x49bfc : word) = Some W_49bfc.
Proof. vm_refl. Qed.
Lemma D_49bfc : decode_any W_49bfc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c00 : bv 32 := 0xf8010113.
Lemma F_49c00 : fetch_word Asan.M.loaded_segments (0x49c00 : word) = Some W_49c00.
Proof. vm_refl. Qed.
Lemma D_49c00 : decode_any W_49c00 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c04 : bv 32 := 0x00060493.
Lemma F_49c04 : fetch_word Asan.M.loaded_segments (0x49c04 : word) = Some W_49c04.
Proof. vm_refl. Qed.
Lemma D_49c04 : decode_any W_49c04 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c08 : bv 32 := 0x00058913.
Lemma F_49c08 : fetch_word Asan.M.loaded_segments (0x49c08 : word) = Some W_49c08.
Proof. vm_refl. Qed.
Lemma D_49c08 : decode_any W_49c08 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c0c : bv 32 := 0x00050993.
Lemma F_49c0c : fetch_word Asan.M.loaded_segments (0x49c0c : word) = Some W_49c0c.
Proof. vm_refl. Qed.
Lemma D_49c0c : decode_any W_49c0c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c10 : bv 32 := 0x6ed110ef.
Lemma F_49c10 : fetch_word Asan.M.loaded_segments (0x49c10 : word) = Some W_49c10.
Proof. vm_refl. Qed.
Lemma D_49c10 : decode_any W_49c10 = Some (Jal 1 73452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c14 : bv 32 := 0x00061517.
Lemma F_49c14 : fetch_word Asan.M.loaded_segments (0x49c14 : word) = Some W_49c14.
Proof. vm_refl. Qed.
Lemma D_49c14 : decode_any W_49c14 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c18 : bv 32 := 0x26453503.
Lemma F_49c18 : fetch_word Asan.M.loaded_segments (0x49c18 : word) = Some W_49c18.
Proof. vm_refl. Qed.
Lemma D_49c18 : decode_any W_49c18 = Some (Load SZ8 true 10 10 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c1c : bv 32 := 0x01d54503.
Lemma F_49c1c : fetch_word Asan.M.loaded_segments (0x49c1c : word) = Some W_49c1c.
Proof. vm_refl. Qed.
Lemma D_49c1c : decode_any W_49c1c = Some (Load SZ1 false 10 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c20 : bv 32 := 0x00063597.
Lemma F_49c20 : fetch_word Asan.M.loaded_segments (0x49c20 : word) = Some W_49c20.
Proof. vm_refl. Qed.
Lemma D_49c20 : decode_any W_49c20 = Some (Auipc 11 99, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c24 : bv 32 := 0x07858b93.
Lemma F_49c24 : fetch_word Asan.M.loaded_segments (0x49c24 : word) = Some W_49c24.
Proof. vm_refl. Qed.
Lemma D_49c24 : decode_any W_49c24 = Some (OpImm ALU_ADD 23 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c28 : bv 32 := 0x0c050e63.
Lemma F_49c28 : fetch_word Asan.M.loaded_segments (0x49c28 : word) = Some W_49c28.
Proof. vm_refl. Qed.
Lemma D_49c28 : decode_any W_49c28 = Some (Branch BC_EQ 10 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c2c : bv 32 := 0x000bb603.
Lemma F_49c2c : fetch_word Asan.M.loaded_segments (0x49c2c : word) = Some W_49c2c.
Proof. vm_refl. Qed.
Lemma D_49c2c : decode_any W_49c2c = Some (Load SZ8 true 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c30 : bv 32 := 0x10060e63.
Lemma F_49c30 : fetch_word Asan.M.loaded_segments (0x49c30 : word) = Some W_49c30.
Proof. vm_refl. Qed.
Lemma D_49c30 : decode_any W_49c30 = Some (Branch BC_EQ 12 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c34 : bv 32 := 0x00090513.
Lemma F_49c34 : fetch_word Asan.M.loaded_segments (0x49c34 : word) = Some W_49c34.
Proof. vm_refl. Qed.
Lemma D_49c34 : decode_any W_49c34 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c38 : bv 32 := 0x00048593.
Lemma F_49c38 : fetch_word Asan.M.loaded_segments (0x49c38 : word) = Some W_49c38.
Proof. vm_refl. Qed.
Lemma D_49c38 : decode_any W_49c38 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c3c : bv 32 := 0x000600e7.
Lemma F_49c3c : fetch_word Asan.M.loaded_segments (0x49c3c : word) = Some W_49c3c.
Proof. vm_refl. Qed.
Lemma D_49c3c : decode_any W_49c3c = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c40 : bv 32 := 0x00150513.
Lemma F_49c40 : fetch_word Asan.M.loaded_segments (0x49c40 : word) = Some W_49c40.
Proof. vm_refl. Qed.
Lemma D_49c40 : decode_any W_49c40 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c44 : bv 32 := 0x00048a13.
Lemma F_49c44 : fetch_word Asan.M.loaded_segments (0x49c44 : word) = Some W_49c44.
Proof. vm_refl. Qed.
Lemma D_49c44 : decode_any W_49c44 = Some (OpImm ALU_ADD 20 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c48 : bv 32 := 0x00a4e463.
Lemma F_49c48 : fetch_word Asan.M.loaded_segments (0x49c48 : word) = Some W_49c48.
Proof. vm_refl. Qed.
Lemma D_49c48 : decode_any W_49c48 = Some (Branch BC_LTU 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c4c : bv 32 := 0x00050a13.
Lemma F_49c4c : fetch_word Asan.M.loaded_segments (0x49c4c : word) = Some W_49c4c.
Proof. vm_refl. Qed.
Lemma D_49c4c : decode_any W_49c4c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c50 : bv 32 := 0x80040c13.
Lemma F_49c50 : fetch_word Asan.M.loaded_segments (0x49c50 : word) = Some W_49c50.
Proof. vm_refl. Qed.
Lemma D_49c50 : decode_any W_49c50 = Some (OpImm ALU_ADD 24 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c54 : bv 32 := 0xf98c0c13.
Lemma F_49c54 : fetch_word Asan.M.loaded_segments (0x49c54 : word) = Some W_49c54.
Proof. vm_refl. Qed.
Lemma D_49c54 : decode_any W_49c54 = Some (OpImm ALU_ADD 24 24 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c58 : bv 32 := 0x01498533.
Lemma F_49c58 : fetch_word Asan.M.loaded_segments (0x49c58 : word) = Some W_49c58.
Proof. vm_refl. Qed.
Lemma D_49c58 : decode_any W_49c58 = Some (Op ALU_ADD 10 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c5c : bv 32 := 0x01490ab3.
Lemma F_49c5c : fetch_word Asan.M.loaded_segments (0x49c5c : word) = Some W_49c5c.
Proof. vm_refl. Qed.
Lemma D_49c5c : decode_any W_49c5c = Some (Op ALU_ADD 21 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c60 : bv 32 := 0x00a97463.
Lemma F_49c60 : fetch_word Asan.M.loaded_segments (0x49c60 : word) = Some W_49c60.
Proof. vm_refl. Qed.
Lemma D_49c60 : decode_any W_49c60 = Some (Branch BC_GEU 18 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c64 : bv 32 := 0x1159e263.
Lemma F_49c64 : fetch_word Asan.M.loaded_segments (0x49c64 : word) = Some W_49c64.
Proof. vm_refl. Qed.
Lemma D_49c64 : decode_any W_49c64 = Some (Branch BC_LTU 19 21 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c68 : bv 32 := 0xfff94513.
Lemma F_49c68 : fetch_word Asan.M.loaded_segments (0x49c68 : word) = Some W_49c68.
Proof. vm_refl. Qed.
Lemma D_49c68 : decode_any W_49c68 = Some (OpImm ALU_XOR 10 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c6c : bv 32 := 0x19456e63.
Lemma F_49c6c : fetch_word Asan.M.loaded_segments (0x49c6c : word) = Some W_49c6c.
Proof. vm_refl. Qed.
Lemma D_49c6c : decode_any W_49c6c = Some (Branch BC_LTU 10 20 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c70 : bv 32 := 0xfbfa0513.
Lemma F_49c70 : fetch_word Asan.M.loaded_segments (0x49c70 : word) = Some W_49c70.
Proof. vm_refl. Qed.
Lemma D_49c70 : decode_any W_49c70 = Some (OpImm ALU_ADD 10 20 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c74 : bv 32 := 0xfbf00593.
Lemma F_49c74 : fetch_word Asan.M.loaded_segments (0x49c74 : word) = Some W_49c74.
Proof. vm_refl. Qed.
Lemma D_49c74 : decode_any W_49c74 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c78 : bv 32 := 0x20a5f063.
Lemma F_49c78 : fetch_word Asan.M.loaded_segments (0x49c78 : word) = Some W_49c78.
Proof. vm_refl. Qed.
Lemma D_49c78 : decode_any W_49c78 = Some (Branch BC_GEU 11 10 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c7c : bv 32 := 0x00061517.
Lemma F_49c7c : fetch_word Asan.M.loaded_segments (0x49c7c : word) = Some W_49c7c.
Proof. vm_refl. Qed.
Lemma D_49c7c : decode_any W_49c7c = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c80 : bv 32 := 0x20453503.
Lemma F_49c80 : fetch_word Asan.M.loaded_segments (0x49c80 : word) = Some W_49c80.
Proof. vm_refl. Qed.
Lemma D_49c80 : decode_any W_49c80 = Some (Load SZ8 true 10 10 516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c84 : bv 32 := 0x00053583.
Lemma F_49c84 : fetch_word Asan.M.loaded_segments (0x49c84 : word) = Some W_49c84.
Proof. vm_refl. Qed.
Lemma D_49c84 : decode_any W_49c84 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c88 : bv 32 := 0xfffa8a93.
Lemma F_49c88 : fetch_word Asan.M.loaded_segments (0x49c88 : word) = Some W_49c88.
Proof. vm_refl. Qed.
Lemma D_49c88 : decode_any W_49c88 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c8c : bv 32 := 0x00395513.
Lemma F_49c8c : fetch_word Asan.M.loaded_segments (0x49c8c : word) = Some W_49c8c.
Proof. vm_refl. Qed.
Lemma D_49c8c : decode_any W_49c8c = Some (ShiftImm ALU_SRL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c90 : bv 32 := 0x003ad613.
Lemma F_49c90 : fetch_word Asan.M.loaded_segments (0x49c90 : word) = Some W_49c90.
Proof. vm_refl. Qed.
Lemma D_49c90 : decode_any W_49c90 = Some (ShiftImm ALU_SRL 12 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c94 : bv 32 := 0x00a58533.
Lemma F_49c94 : fetch_word Asan.M.loaded_segments (0x49c94 : word) = Some W_49c94.
Proof. vm_refl. Qed.
Lemma D_49c94 : decode_any W_49c94 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c98 : bv 32 := 0x00c585b3.
Lemma F_49c98 : fetch_word Asan.M.loaded_segments (0x49c98 : word) = Some W_49c98.
Proof. vm_refl. Qed.
Lemma D_49c98 : decode_any W_49c98 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49c9c : bv 32 := 0xff857613.
Lemma F_49c9c : fetch_word Asan.M.loaded_segments (0x49c9c : word) = Some W_49c9c.
Proof. vm_refl. Qed.
Lemma D_49c9c : decode_any W_49c9c = Some (OpImm ALU_AND 12 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ca0 : bv 32 := 0xff85f693.
Lemma F_49ca0 : fetch_word Asan.M.loaded_segments (0x49ca0 : word) = Some W_49ca0.
Proof. vm_refl. Qed.
Lemma D_49ca0 : decode_any W_49ca0 = Some (OpImm ALU_AND 13 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ca4 : bv 32 := 0x00063603.
Lemma F_49ca4 : fetch_word Asan.M.loaded_segments (0x49ca4 : word) = Some W_49ca4.
Proof. vm_refl. Qed.
Lemma D_49ca4 : decode_any W_49ca4 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ca8 : bv 32 := 0x0006b683.
Lemma F_49ca8 : fetch_word Asan.M.loaded_segments (0x49ca8 : word) = Some W_49ca8.
Proof. vm_refl. Qed.
Lemma D_49ca8 : decode_any W_49ca8 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cac : bv 32 := 0x00c6e633.
Lemma F_49cac : fetch_word Asan.M.loaded_segments (0x49cac : word) = Some W_49cac.
Proof. vm_refl. Qed.
Lemma D_49cac : decode_any W_49cac = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cb0 : bv 32 := 0x24061463.
Lemma F_49cb0 : fetch_word Asan.M.loaded_segments (0x49cb0 : word) = Some W_49cb0.
Proof. vm_refl. Qed.
Lemma D_49cb0 : decode_any W_49cb0 = Some (Branch BC_NE 12 0 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cb4 : bv 32 := 0xfff9c513.
Lemma F_49cb4 : fetch_word Asan.M.loaded_segments (0x49cb4 : word) = Some W_49cb4.
Proof. vm_refl. Qed.
Lemma D_49cb4 : decode_any W_49cb4 = Some (OpImm ALU_XOR 10 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cb8 : bv 32 := 0x1c956463.
Lemma F_49cb8 : fetch_word Asan.M.loaded_segments (0x49cb8 : word) = Some W_49cb8.
Proof. vm_refl. Qed.
Lemma D_49cb8 : decode_any W_49cb8 = Some (Branch BC_LTU 10 9 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cbc : bv 32 := 0xfbf48513.
Lemma F_49cbc : fetch_word Asan.M.loaded_segments (0x49cbc : word) = Some W_49cbc.
Proof. vm_refl. Qed.
Lemma D_49cbc : decode_any W_49cbc = Some (OpImm ALU_ADD 10 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cc0 : bv 32 := 0xfbf00593.
Lemma F_49cc0 : fetch_word Asan.M.loaded_segments (0x49cc0 : word) = Some W_49cc0.
Proof. vm_refl. Qed.
Lemma D_49cc0 : decode_any W_49cc0 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cc4 : bv 32 := 0x22a5f663.
Lemma F_49cc4 : fetch_word Asan.M.loaded_segments (0x49cc4 : word) = Some W_49cc4.
Proof. vm_refl. Qed.
Lemma D_49cc4 : decode_any W_49cc4 = Some (Branch BC_GEU 11 10 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cc8 : bv 32 := 0x00061517.
Lemma F_49cc8 : fetch_word Asan.M.loaded_segments (0x49cc8 : word) = Some W_49cc8.
Proof. vm_refl. Qed.
Lemma D_49cc8 : decode_any W_49cc8 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ccc : bv 32 := 0x1b853503.
Lemma F_49ccc : fetch_word Asan.M.loaded_segments (0x49ccc : word) = Some W_49ccc.
Proof. vm_refl. Qed.
Lemma D_49ccc : decode_any W_49ccc = Some (Load SZ8 true 10 10 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cd0 : bv 32 := 0x00998633.
Lemma F_49cd0 : fetch_word Asan.M.loaded_segments (0x49cd0 : word) = Some W_49cd0.
Proof. vm_refl. Qed.
Lemma D_49cd0 : decode_any W_49cd0 = Some (Op ALU_ADD 12 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cd4 : bv 32 := 0x00053583.
Lemma F_49cd4 : fetch_word Asan.M.loaded_segments (0x49cd4 : word) = Some W_49cd4.
Proof. vm_refl. Qed.
Lemma D_49cd4 : decode_any W_49cd4 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cd8 : bv 32 := 0x0039d513.
Lemma F_49cd8 : fetch_word Asan.M.loaded_segments (0x49cd8 : word) = Some W_49cd8.
Proof. vm_refl. Qed.
Lemma D_49cd8 : decode_any W_49cd8 = Some (ShiftImm ALU_SRL 10 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cdc : bv 32 := 0xfff60613.
Lemma F_49cdc : fetch_word Asan.M.loaded_segments (0x49cdc : word) = Some W_49cdc.
Proof. vm_refl. Qed.
Lemma D_49cdc : decode_any W_49cdc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ce0 : bv 32 := 0x00365693.
Lemma F_49ce0 : fetch_word Asan.M.loaded_segments (0x49ce0 : word) = Some W_49ce0.
Proof. vm_refl. Qed.
Lemma D_49ce0 : decode_any W_49ce0 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ce4 : bv 32 := 0x00a58533.
Lemma F_49ce4 : fetch_word Asan.M.loaded_segments (0x49ce4 : word) = Some W_49ce4.
Proof. vm_refl. Qed.
Lemma D_49ce4 : decode_any W_49ce4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ce8 : bv 32 := 0x00d585b3.
Lemma F_49ce8 : fetch_word Asan.M.loaded_segments (0x49ce8 : word) = Some W_49ce8.
Proof. vm_refl. Qed.
Lemma D_49ce8 : decode_any W_49ce8 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cec : bv 32 := 0xff857693.
Lemma F_49cec : fetch_word Asan.M.loaded_segments (0x49cec : word) = Some W_49cec.
Proof. vm_refl. Qed.
Lemma D_49cec : decode_any W_49cec = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cf0 : bv 32 := 0xff85f713.
Lemma F_49cf0 : fetch_word Asan.M.loaded_segments (0x49cf0 : word) = Some W_49cf0.
Proof. vm_refl. Qed.
Lemma D_49cf0 : decode_any W_49cf0 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cf4 : bv 32 := 0x0006b683.
Lemma F_49cf4 : fetch_word Asan.M.loaded_segments (0x49cf4 : word) = Some W_49cf4.
Proof. vm_refl. Qed.
Lemma D_49cf4 : decode_any W_49cf4 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cf8 : bv 32 := 0x00073703.
Lemma F_49cf8 : fetch_word Asan.M.loaded_segments (0x49cf8 : word) = Some W_49cf8.
Proof. vm_refl. Qed.
Lemma D_49cf8 : decode_any W_49cf8 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49cfc : bv 32 := 0x00d766b3.
Lemma F_49cfc : fetch_word Asan.M.loaded_segments (0x49cfc : word) = Some W_49cfc.
Proof. vm_refl. Qed.
Lemma D_49cfc : decode_any W_49cfc = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d00 : bv 32 := 0x2c069063.
Lemma F_49d00 : fetch_word Asan.M.loaded_segments (0x49d00 : word) = Some W_49d00.
Proof. vm_refl. Qed.
Lemma D_49d00 : decode_any W_49d00 = Some (Branch BC_NE 13 0 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d04 : bv 32 := 0x020bb683.
Lemma F_49d04 : fetch_word Asan.M.loaded_segments (0x49d04 : word) = Some W_49d04.
Proof. vm_refl. Qed.
Lemma D_49d04 : decode_any W_49d04 = Some (Load SZ8 true 13 23 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d08 : bv 32 := 0x00098513.
Lemma F_49d08 : fetch_word Asan.M.loaded_segments (0x49d08 : word) = Some W_49d08.
Proof. vm_refl. Qed.
Lemma D_49d08 : decode_any W_49d08 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d0c : bv 32 := 0x00090593.
Lemma F_49d0c : fetch_word Asan.M.loaded_segments (0x49d0c : word) = Some W_49d0c.
Proof. vm_refl. Qed.
Lemma D_49d0c : decode_any W_49d0c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d10 : bv 32 := 0x00048613.
Lemma F_49d10 : fetch_word Asan.M.loaded_segments (0x49d10 : word) = Some W_49d10.
Proof. vm_refl. Qed.
Lemma D_49d10 : decode_any W_49d10 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d14 : bv 32 := 0x000680e7.
Lemma F_49d14 : fetch_word Asan.M.loaded_segments (0x49d14 : word) = Some W_49d14.
Proof. vm_refl. Qed.
Lemma D_49d14 : decode_any W_49d14 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d18 : bv 32 := 0x08010113.
Lemma F_49d18 : fetch_word Asan.M.loaded_segments (0x49d18 : word) = Some W_49d18.
Proof. vm_refl. Qed.
Lemma D_49d18 : decode_any W_49d18 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d1c : bv 32 := 0x7e813083.
Lemma F_49d1c : fetch_word Asan.M.loaded_segments (0x49d1c : word) = Some W_49d1c.
Proof. vm_refl. Qed.
Lemma D_49d1c : decode_any W_49d1c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d20 : bv 32 := 0x7e013403.
Lemma F_49d20 : fetch_word Asan.M.loaded_segments (0x49d20 : word) = Some W_49d20.
Proof. vm_refl. Qed.
Lemma D_49d20 : decode_any W_49d20 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d24 : bv 32 := 0x7d813483.
Lemma F_49d24 : fetch_word Asan.M.loaded_segments (0x49d24 : word) = Some W_49d24.
Proof. vm_refl. Qed.
Lemma D_49d24 : decode_any W_49d24 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d28 : bv 32 := 0x7d013903.
Lemma F_49d28 : fetch_word Asan.M.loaded_segments (0x49d28 : word) = Some W_49d28.
Proof. vm_refl. Qed.
Lemma D_49d28 : decode_any W_49d28 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d2c : bv 32 := 0x7c813983.
Lemma F_49d2c : fetch_word Asan.M.loaded_segments (0x49d2c : word) = Some W_49d2c.
Proof. vm_refl. Qed.
Lemma D_49d2c : decode_any W_49d2c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d30 : bv 32 := 0x7c013a03.
Lemma F_49d30 : fetch_word Asan.M.loaded_segments (0x49d30 : word) = Some W_49d30.
Proof. vm_refl. Qed.
Lemma D_49d30 : decode_any W_49d30 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d34 : bv 32 := 0x7b813a83.
Lemma F_49d34 : fetch_word Asan.M.loaded_segments (0x49d34 : word) = Some W_49d34.
Proof. vm_refl. Qed.
Lemma D_49d34 : decode_any W_49d34 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d38 : bv 32 := 0x7b013b03.
Lemma F_49d38 : fetch_word Asan.M.loaded_segments (0x49d38 : word) = Some W_49d38.
Proof. vm_refl. Qed.
Lemma D_49d38 : decode_any W_49d38 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d3c : bv 32 := 0x7a813b83.
Lemma F_49d3c : fetch_word Asan.M.loaded_segments (0x49d3c : word) = Some W_49d3c.
Proof. vm_refl. Qed.
Lemma D_49d3c : decode_any W_49d3c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d40 : bv 32 := 0x7a013c03.
Lemma F_49d40 : fetch_word Asan.M.loaded_segments (0x49d40 : word) = Some W_49d40.
Proof. vm_refl. Qed.
Lemma D_49d40 : decode_any W_49d40 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d44 : bv 32 := 0x7f010113.
Lemma F_49d44 : fetch_word Asan.M.loaded_segments (0x49d44 : word) = Some W_49d44.
Proof. vm_refl. Qed.
Lemma D_49d44 : decode_any W_49d44 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d48 : bv 32 := 0x00008067.
Lemma F_49d48 : fetch_word Asan.M.loaded_segments (0x49d48 : word) = Some W_49d48.
Proof. vm_refl. Qed.
Lemma D_49d48 : decode_any W_49d48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d4c : bv 32 := 0x00090513.
Lemma F_49d4c : fetch_word Asan.M.loaded_segments (0x49d4c : word) = Some W_49d4c.
Proof. vm_refl. Qed.
Lemma D_49d4c : decode_any W_49d4c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d50 : bv 32 := 0x00048593.
Lemma F_49d50 : fetch_word Asan.M.loaded_segments (0x49d50 : word) = Some W_49d50.
Proof. vm_refl. Qed.
Lemma D_49d50 : decode_any W_49d50 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d54 : bv 32 := 0x0211c0ef.
Lemma F_49d54 : fetch_word Asan.M.loaded_segments (0x49d54 : word) = Some W_49d54.
Proof. vm_refl. Qed.
Lemma D_49d54 : decode_any W_49d54 = Some (Jal 1 116768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d58 : bv 32 := 0x00150513.
Lemma F_49d58 : fetch_word Asan.M.loaded_segments (0x49d58 : word) = Some W_49d58.
Proof. vm_refl. Qed.
Lemma D_49d58 : decode_any W_49d58 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d5c : bv 32 := 0x00048a13.
Lemma F_49d5c : fetch_word Asan.M.loaded_segments (0x49d5c : word) = Some W_49d5c.
Proof. vm_refl. Qed.
Lemma D_49d5c : decode_any W_49d5c = Some (OpImm ALU_ADD 20 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d60 : bv 32 := 0xeea4f6e3.
Lemma F_49d60 : fetch_word Asan.M.loaded_segments (0x49d60 : word) = Some W_49d60.
Proof. vm_refl. Qed.
Lemma D_49d60 : decode_any W_49d60 = Some (Branch BC_GEU 9 10 7916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d64 : bv 32 := 0xeedff06f.
Lemma F_49d64 : fetch_word Asan.M.loaded_segments (0x49d64 : word) = Some W_49d64.
Proof. vm_refl. Qed.
Lemma D_49d64 : decode_any W_49d64 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d68 : bv 32 := 0x80040513.
Lemma F_49d68 : fetch_word Asan.M.loaded_segments (0x49d68 : word) = Some W_49d68.
Proof. vm_refl. Qed.
Lemma D_49d68 : decode_any W_49d68 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d6c : bv 32 := 0xfa850513.
Lemma F_49d6c : fetch_word Asan.M.loaded_segments (0x49d6c : word) = Some W_49d6c.
Proof. vm_refl. Qed.
Lemma D_49d6c : decode_any W_49d6c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d70 : bv 32 := 0x80040593.
Lemma F_49d70 : fetch_word Asan.M.loaded_segments (0x49d70 : word) = Some W_49d70.
Proof. vm_refl. Qed.
Lemma D_49d70 : decode_any W_49d70 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d74 : bv 32 := 0xf9858593.
Lemma F_49d74 : fetch_word Asan.M.loaded_segments (0x49d74 : word) = Some W_49d74.
Proof. vm_refl. Qed.
Lemma D_49d74 : decode_any W_49d74 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d78 : bv 32 := 0x7ff58b13.
Lemma F_49d78 : fetch_word Asan.M.loaded_segments (0x49d78 : word) = Some W_49d78.
Proof. vm_refl. Qed.
Lemma D_49d78 : decode_any W_49d78 = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d7c : bv 32 := 0x000b34a3.
Lemma F_49d7c : fetch_word Asan.M.loaded_segments (0x49d7c : word) = Some W_49d7c.
Proof. vm_refl. Qed.
Lemma D_49d7c : decode_any W_49d7c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d80 : bv 32 := 0x00ac3023.
Lemma F_49d80 : fetch_word Asan.M.loaded_segments (0x49d80 : word) = Some W_49d80.
Proof. vm_refl. Qed.
Lemma D_49d80 : decode_any W_49d80 = Some (Store SZ8 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d84 : bv 32 := 0x000c3423.
Lemma F_49d84 : fetch_word Asan.M.loaded_segments (0x49d84 : word) = Some W_49d84.
Proof. vm_refl. Qed.
Lemma D_49d84 : decode_any W_49d84 = Some (Store SZ8 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d88 : bv 32 := 0x1012b0ef.
Lemma F_49d88 : fetch_word Asan.M.loaded_segments (0x49d88 : word) = Some W_49d88.
Proof. vm_refl. Qed.
Lemma D_49d88 : decode_any W_49d88 = Some (Jal 1 178432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d8c : bv 32 := 0x00050593.
Lemma F_49d8c : fetch_word Asan.M.loaded_segments (0x49d8c : word) = Some W_49d8c.
Proof. vm_refl. Qed.
Lemma D_49d8c : decode_any W_49d8c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d90 : bv 32 := 0x00061517.
Lemma F_49d90 : fetch_word Asan.M.loaded_segments (0x49d90 : word) = Some W_49d90.
Proof. vm_refl. Qed.
Lemma D_49d90 : decode_any W_49d90 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d94 : bv 32 := 0x0e053503.
Lemma F_49d94 : fetch_word Asan.M.loaded_segments (0x49d94 : word) = Some W_49d94.
Proof. vm_refl. Qed.
Lemma D_49d94 : decode_any W_49d94 = Some (Load SZ8 true 10 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d98 : bv 32 := 0x02154703.
Lemma F_49d98 : fetch_word Asan.M.loaded_segments (0x49d98 : word) = Some W_49d98.
Proof. vm_refl. Qed.
Lemma D_49d98 : decode_any W_49d98 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49d9c : bv 32 := 0x008b34a3.
Lemma F_49d9c : fetch_word Asan.M.loaded_segments (0x49d9c : word) = Some W_49d9c.
Proof. vm_refl. Qed.
Lemma D_49d9c : decode_any W_49d9c = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49da0 : bv 32 := 0x80040513.
Lemma F_49da0 : fetch_word Asan.M.loaded_segments (0x49da0 : word) = Some W_49da0.
Proof. vm_refl. Qed.
Lemma D_49da0 : decode_any W_49da0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49da4 : bv 32 := 0xf9850513.
Lemma F_49da4 : fetch_word Asan.M.loaded_segments (0x49da4 : word) = Some W_49da4.
Proof. vm_refl. Qed.
Lemma D_49da4 : decode_any W_49da4 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49da8 : bv 32 := 0x0ff00793.
Lemma F_49da8 : fetch_word Asan.M.loaded_segments (0x49da8 : word) = Some W_49da8.
Proof. vm_refl. Qed.
Lemma D_49da8 : decode_any W_49da8 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dac : bv 32 := 0x00040613.
Lemma F_49dac : fetch_word Asan.M.loaded_segments (0x49dac : word) = Some W_49dac.
Proof. vm_refl. Qed.
Lemma D_49dac : decode_any W_49dac = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49db0 : bv 32 := 0x00000693.
Lemma F_49db0 : fetch_word Asan.M.loaded_segments (0x49db0 : word) = Some W_49db0.
Proof. vm_refl. Qed.
Lemma D_49db0 : decode_any W_49db0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49db4 : bv 32 := 0x625120ef.
Lemma F_49db4 : fetch_word Asan.M.loaded_segments (0x49db4 : word) = Some W_49db4.
Proof. vm_refl. Qed.
Lemma D_49db4 : decode_any W_49db4 = Some (Jal 1 77348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49db8 : bv 32 := 0xfffd6517.
Lemma F_49db8 : fetch_word Asan.M.loaded_segments (0x49db8 : word) = Some W_49db8.
Proof. vm_refl. Qed.
Lemma D_49db8 : decode_any W_49db8 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dbc : bv 32 := 0x9f950513.
Lemma F_49dbc : fetch_word Asan.M.loaded_segments (0x49dbc : word) = Some W_49dbc.
Proof. vm_refl. Qed.
Lemma D_49dbc : decode_any W_49dbc = Some (OpImm ALU_ADD 10 10 2553, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dc0 : bv 32 := 0x5c5130ef.
Lemma F_49dc0 : fetch_word Asan.M.loaded_segments (0x49dc0 : word) = Some W_49dc0.
Proof. vm_refl. Qed.
Lemma D_49dc0 : decode_any W_49dc0 = Some (Jal 1 81348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dc4 : bv 32 := 0xea0512e3.
Lemma F_49dc4 : fetch_word Asan.M.loaded_segments (0x49dc4 : word) = Some W_49dc4.
Proof. vm_refl. Qed.
Lemma D_49dc4 : decode_any W_49dc4 = Some (Branch BC_NE 10 0 7844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dc8 : bv 32 := 0x625130ef.
Lemma F_49dc8 : fetch_word Asan.M.loaded_segments (0x49dc8 : word) = Some W_49dc8.
Proof. vm_refl. Qed.
Lemma D_49dc8 : decode_any W_49dc8 = Some (Jal 1 81444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dcc : bv 32 := 0x00050a63.
Lemma F_49dcc : fetch_word Asan.M.loaded_segments (0x49dcc : word) = Some W_49dcc.
Proof. vm_refl. Qed.
Lemma D_49dcc : decode_any W_49dcc = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dd0 : bv 32 := 0x80040513.
Lemma F_49dd0 : fetch_word Asan.M.loaded_segments (0x49dd0 : word) = Some W_49dd0.
Proof. vm_refl. Qed.
Lemma D_49dd0 : decode_any W_49dd0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dd4 : bv 32 := 0xf9850513.
Lemma F_49dd4 : fetch_word Asan.M.loaded_segments (0x49dd4 : word) = Some W_49dd4.
Proof. vm_refl. Qed.
Lemma D_49dd4 : decode_any W_49dd4 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dd8 : bv 32 := 0x11c140ef.
Lemma F_49dd8 : fetch_word Asan.M.loaded_segments (0x49dd8 : word) = Some W_49dd8.
Proof. vm_refl. Qed.
Lemma D_49dd8 : decode_any W_49dd8 = Some (Jal 1 82204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ddc : bv 32 := 0xe80516e3.
Lemma F_49ddc : fetch_word Asan.M.loaded_segments (0x49ddc : word) = Some W_49ddc.
Proof. vm_refl. Qed.
Lemma D_49ddc : decode_any W_49ddc = Some (Branch BC_NE 10 0 7820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49de0 : bv 32 := 0xfffd6517.
Lemma F_49de0 : fetch_word Asan.M.loaded_segments (0x49de0 : word) = Some W_49de0.
Proof. vm_refl. Qed.
Lemma D_49de0 : decode_any W_49de0 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49de4 : bv 32 := 0x9d150513.
Lemma F_49de4 : fetch_word Asan.M.loaded_segments (0x49de4 : word) = Some W_49de4.
Proof. vm_refl. Qed.
Lemma D_49de4 : decode_any W_49de4 = Some (OpImm ALU_ADD 10 10 2513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49de8 : bv 32 := 0x80040793.
Lemma F_49de8 : fetch_word Asan.M.loaded_segments (0x49de8 : word) = Some W_49de8.
Proof. vm_refl. Qed.
Lemma D_49de8 : decode_any W_49de8 = Some (OpImm ALU_ADD 15 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dec : bv 32 := 0xf9878793.
Lemma F_49dec : fetch_word Asan.M.loaded_segments (0x49dec : word) = Some W_49dec.
Proof. vm_refl. Qed.
Lemma D_49dec : decode_any W_49dec = Some (OpImm ALU_ADD 15 15 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49df0 : bv 32 := 0x00098593.
Lemma F_49df0 : fetch_word Asan.M.loaded_segments (0x49df0 : word) = Some W_49df0.
Proof. vm_refl. Qed.
Lemma D_49df0 : decode_any W_49df0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49df4 : bv 32 := 0x000a0613.
Lemma F_49df4 : fetch_word Asan.M.loaded_segments (0x49df4 : word) = Some W_49df4.
Proof. vm_refl. Qed.
Lemma D_49df4 : decode_any W_49df4 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49df8 : bv 32 := 0x00090693.
Lemma F_49df8 : fetch_word Asan.M.loaded_segments (0x49df8 : word) = Some W_49df8.
Proof. vm_refl. Qed.
Lemma D_49df8 : decode_any W_49df8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49dfc : bv 32 := 0x000a0713.
Lemma F_49dfc : fetch_word Asan.M.loaded_segments (0x49dfc : word) = Some W_49dfc.
Proof. vm_refl. Qed.
Lemma D_49dfc : decode_any W_49dfc = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e00 : bv 32 := 0x0bd0f0ef.
Lemma F_49e00 : fetch_word Asan.M.loaded_segments (0x49e00 : word) = Some W_49e00.
Proof. vm_refl. Qed.
Lemma D_49e00 : decode_any W_49e00 = Some (Jal 1 63676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e04 : bv 32 := 0xe65ff06f.
Lemma F_49e04 : fetch_word Asan.M.loaded_segments (0x49e04 : word) = Some W_49e04.
Proof. vm_refl. Qed.
Lemma D_49e04 : decode_any W_49e04 = Some (Jal 0 2096740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e08 : bv 32 := 0x80040513.
Lemma F_49e08 : fetch_word Asan.M.loaded_segments (0x49e08 : word) = Some W_49e08.
Proof. vm_refl. Qed.
Lemma D_49e08 : decode_any W_49e08 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e0c : bv 32 := 0xfa850513.
Lemma F_49e0c : fetch_word Asan.M.loaded_segments (0x49e0c : word) = Some W_49e0c.
Proof. vm_refl. Qed.
Lemma D_49e0c : decode_any W_49e0c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e10 : bv 32 := 0x80040593.
Lemma F_49e10 : fetch_word Asan.M.loaded_segments (0x49e10 : word) = Some W_49e10.
Proof. vm_refl. Qed.
Lemma D_49e10 : decode_any W_49e10 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e14 : bv 32 := 0xf9858593.
Lemma F_49e14 : fetch_word Asan.M.loaded_segments (0x49e14 : word) = Some W_49e14.
Proof. vm_refl. Qed.
Lemma D_49e14 : decode_any W_49e14 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e18 : bv 32 := 0x7ff58b13.
Lemma F_49e18 : fetch_word Asan.M.loaded_segments (0x49e18 : word) = Some W_49e18.
Proof. vm_refl. Qed.
Lemma D_49e18 : decode_any W_49e18 = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e1c : bv 32 := 0x000b34a3.
Lemma F_49e1c : fetch_word Asan.M.loaded_segments (0x49e1c : word) = Some W_49e1c.
Proof. vm_refl. Qed.
Lemma D_49e1c : decode_any W_49e1c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e20 : bv 32 := 0x00ac3023.
Lemma F_49e20 : fetch_word Asan.M.loaded_segments (0x49e20 : word) = Some W_49e20.
Proof. vm_refl. Qed.
Lemma D_49e20 : decode_any W_49e20 = Some (Store SZ8 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e24 : bv 32 := 0x000c3423.
Lemma F_49e24 : fetch_word Asan.M.loaded_segments (0x49e24 : word) = Some W_49e24.
Proof. vm_refl. Qed.
Lemma D_49e24 : decode_any W_49e24 = Some (Store SZ8 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e28 : bv 32 := 0x0612b0ef.
Lemma F_49e28 : fetch_word Asan.M.loaded_segments (0x49e28 : word) = Some W_49e28.
Proof. vm_refl. Qed.
Lemma D_49e28 : decode_any W_49e28 = Some (Jal 1 178272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e2c : bv 32 := 0x00050593.
Lemma F_49e2c : fetch_word Asan.M.loaded_segments (0x49e2c : word) = Some W_49e2c.
Proof. vm_refl. Qed.
Lemma D_49e2c : decode_any W_49e2c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e30 : bv 32 := 0x00061517.
Lemma F_49e30 : fetch_word Asan.M.loaded_segments (0x49e30 : word) = Some W_49e30.
Proof. vm_refl. Qed.
Lemma D_49e30 : decode_any W_49e30 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e34 : bv 32 := 0x04053503.
Lemma F_49e34 : fetch_word Asan.M.loaded_segments (0x49e34 : word) = Some W_49e34.
Proof. vm_refl. Qed.
Lemma D_49e34 : decode_any W_49e34 = Some (Load SZ8 true 10 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e38 : bv 32 := 0x02154703.
Lemma F_49e38 : fetch_word Asan.M.loaded_segments (0x49e38 : word) = Some W_49e38.
Proof. vm_refl. Qed.
Lemma D_49e38 : decode_any W_49e38 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e3c : bv 32 := 0x008b34a3.
Lemma F_49e3c : fetch_word Asan.M.loaded_segments (0x49e3c : word) = Some W_49e3c.
Proof. vm_refl. Qed.
Lemma D_49e3c : decode_any W_49e3c = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e40 : bv 32 := 0x80040513.
Lemma F_49e40 : fetch_word Asan.M.loaded_segments (0x49e40 : word) = Some W_49e40.
Proof. vm_refl. Qed.
Lemma D_49e40 : decode_any W_49e40 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e44 : bv 32 := 0xf9850513.
Lemma F_49e44 : fetch_word Asan.M.loaded_segments (0x49e44 : word) = Some W_49e44.
Proof. vm_refl. Qed.
Lemma D_49e44 : decode_any W_49e44 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e48 : bv 32 := 0x0ff00793.
Lemma F_49e48 : fetch_word Asan.M.loaded_segments (0x49e48 : word) = Some W_49e48.
Proof. vm_refl. Qed.
Lemma D_49e48 : decode_any W_49e48 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e4c : bv 32 := 0x00040613.
Lemma F_49e4c : fetch_word Asan.M.loaded_segments (0x49e4c : word) = Some W_49e4c.
Proof. vm_refl. Qed.
Lemma D_49e4c : decode_any W_49e4c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e50 : bv 32 := 0x00000693.
Lemma F_49e50 : fetch_word Asan.M.loaded_segments (0x49e50 : word) = Some W_49e50.
Proof. vm_refl. Qed.
Lemma D_49e50 : decode_any W_49e50 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e54 : bv 32 := 0x585120ef.
Lemma F_49e54 : fetch_word Asan.M.loaded_segments (0x49e54 : word) = Some W_49e54.
Proof. vm_refl. Qed.
Lemma D_49e54 : decode_any W_49e54 = Some (Jal 1 77188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e58 : bv 32 := 0x80040613.
Lemma F_49e58 : fetch_word Asan.M.loaded_segments (0x49e58 : word) = Some W_49e58.
Proof. vm_refl. Qed.
Lemma D_49e58 : decode_any W_49e58 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e5c : bv 32 := 0xf9860613.
Lemma F_49e5c : fetch_word Asan.M.loaded_segments (0x49e5c : word) = Some W_49e5c.
Proof. vm_refl. Qed.
Lemma D_49e5c : decode_any W_49e5c = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e60 : bv 32 := 0x00090513.
Lemma F_49e60 : fetch_word Asan.M.loaded_segments (0x49e60 : word) = Some W_49e60.
Proof. vm_refl. Qed.
Lemma D_49e60 : decode_any W_49e60 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e64 : bv 32 := 0x000a0593.
Lemma F_49e64 : fetch_word Asan.M.loaded_segments (0x49e64 : word) = Some W_49e64.
Proof. vm_refl. Qed.
Lemma D_49e64 : decode_any W_49e64 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e68 : bv 32 := 0x3290f0ef.
Lemma F_49e68 : fetch_word Asan.M.loaded_segments (0x49e68 : word) = Some W_49e68.
Proof. vm_refl. Qed.
Lemma D_49e68 : decode_any W_49e68 = Some (Jal 1 64296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e6c : bv 32 := 0xfbfa0513.
Lemma F_49e6c : fetch_word Asan.M.loaded_segments (0x49e6c : word) = Some W_49e6c.
Proof. vm_refl. Qed.
Lemma D_49e6c : decode_any W_49e6c = Some (OpImm ALU_ADD 10 20 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e70 : bv 32 := 0xfbf00593.
Lemma F_49e70 : fetch_word Asan.M.loaded_segments (0x49e70 : word) = Some W_49e70.
Proof. vm_refl. Qed.
Lemma D_49e70 : decode_any W_49e70 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e74 : bv 32 := 0xe0a5e4e3.
Lemma F_49e74 : fetch_word Asan.M.loaded_segments (0x49e74 : word) = Some W_49e74.
Proof. vm_refl. Qed.
Lemma D_49e74 : decode_any W_49e74 = Some (Branch BC_LTU 11 10 7688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e78 : bv 32 := 0x0a0a1a63.
Lemma F_49e78 : fetch_word Asan.M.loaded_segments (0x49e78 : word) = Some W_49e78.
Proof. vm_refl. Qed.
Lemma D_49e78 : decode_any W_49e78 = Some (Branch BC_NE 20 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e7c : bv 32 := 0xe39ff06f.
Lemma F_49e7c : fetch_word Asan.M.loaded_segments (0x49e7c : word) = Some W_49e7c.
Proof. vm_refl. Qed.
Lemma D_49e7c : decode_any W_49e7c = Some (Jal 0 2096696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e80 : bv 32 := 0x80040513.
Lemma F_49e80 : fetch_word Asan.M.loaded_segments (0x49e80 : word) = Some W_49e80.
Proof. vm_refl. Qed.
Lemma D_49e80 : decode_any W_49e80 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e84 : bv 32 := 0xfa850513.
Lemma F_49e84 : fetch_word Asan.M.loaded_segments (0x49e84 : word) = Some W_49e84.
Proof. vm_refl. Qed.
Lemma D_49e84 : decode_any W_49e84 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e88 : bv 32 := 0x80040593.
Lemma F_49e88 : fetch_word Asan.M.loaded_segments (0x49e88 : word) = Some W_49e88.
Proof. vm_refl. Qed.
Lemma D_49e88 : decode_any W_49e88 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e8c : bv 32 := 0xf9858593.
Lemma F_49e8c : fetch_word Asan.M.loaded_segments (0x49e8c : word) = Some W_49e8c.
Proof. vm_refl. Qed.
Lemma D_49e8c : decode_any W_49e8c = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e90 : bv 32 := 0x7ff58a13.
Lemma F_49e90 : fetch_word Asan.M.loaded_segments (0x49e90 : word) = Some W_49e90.
Proof. vm_refl. Qed.
Lemma D_49e90 : decode_any W_49e90 = Some (OpImm ALU_ADD 20 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e94 : bv 32 := 0x000a34a3.
Lemma F_49e94 : fetch_word Asan.M.loaded_segments (0x49e94 : word) = Some W_49e94.
Proof. vm_refl. Qed.
Lemma D_49e94 : decode_any W_49e94 = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e98 : bv 32 := 0x00ac3023.
Lemma F_49e98 : fetch_word Asan.M.loaded_segments (0x49e98 : word) = Some W_49e98.
Proof. vm_refl. Qed.
Lemma D_49e98 : decode_any W_49e98 = Some (Store SZ8 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49e9c : bv 32 := 0x000c3423.
Lemma F_49e9c : fetch_word Asan.M.loaded_segments (0x49e9c : word) = Some W_49e9c.
Proof. vm_refl. Qed.
Lemma D_49e9c : decode_any W_49e9c = Some (Store SZ8 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ea0 : bv 32 := 0x7e82b0ef.
Lemma F_49ea0 : fetch_word Asan.M.loaded_segments (0x49ea0 : word) = Some W_49ea0.
Proof. vm_refl. Qed.
Lemma D_49ea0 : decode_any W_49ea0 = Some (Jal 1 178152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ea4 : bv 32 := 0x00050593.
Lemma F_49ea4 : fetch_word Asan.M.loaded_segments (0x49ea4 : word) = Some W_49ea4.
Proof. vm_refl. Qed.
Lemma D_49ea4 : decode_any W_49ea4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ea8 : bv 32 := 0x00061517.
Lemma F_49ea8 : fetch_word Asan.M.loaded_segments (0x49ea8 : word) = Some W_49ea8.
Proof. vm_refl. Qed.
Lemma D_49ea8 : decode_any W_49ea8 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49eac : bv 32 := 0xfc853503.
Lemma F_49eac : fetch_word Asan.M.loaded_segments (0x49eac : word) = Some W_49eac.
Proof. vm_refl. Qed.
Lemma D_49eac : decode_any W_49eac = Some (Load SZ8 true 10 10 4040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49eb0 : bv 32 := 0x02154703.
Lemma F_49eb0 : fetch_word Asan.M.loaded_segments (0x49eb0 : word) = Some W_49eb0.
Proof. vm_refl. Qed.
Lemma D_49eb0 : decode_any W_49eb0 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49eb4 : bv 32 := 0x008a34a3.
Lemma F_49eb4 : fetch_word Asan.M.loaded_segments (0x49eb4 : word) = Some W_49eb4.
Proof. vm_refl. Qed.
Lemma D_49eb4 : decode_any W_49eb4 = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49eb8 : bv 32 := 0x80040513.
Lemma F_49eb8 : fetch_word Asan.M.loaded_segments (0x49eb8 : word) = Some W_49eb8.
Proof. vm_refl. Qed.
Lemma D_49eb8 : decode_any W_49eb8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ebc : bv 32 := 0xf9850513.
Lemma F_49ebc : fetch_word Asan.M.loaded_segments (0x49ebc : word) = Some W_49ebc.
Proof. vm_refl. Qed.
Lemma D_49ebc : decode_any W_49ebc = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ec0 : bv 32 := 0x0ff00793.
Lemma F_49ec0 : fetch_word Asan.M.loaded_segments (0x49ec0 : word) = Some W_49ec0.
Proof. vm_refl. Qed.
Lemma D_49ec0 : decode_any W_49ec0 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ec4 : bv 32 := 0x00040613.
Lemma F_49ec4 : fetch_word Asan.M.loaded_segments (0x49ec4 : word) = Some W_49ec4.
Proof. vm_refl. Qed.
Lemma D_49ec4 : decode_any W_49ec4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ec8 : bv 32 := 0x00000693.
Lemma F_49ec8 : fetch_word Asan.M.loaded_segments (0x49ec8 : word) = Some W_49ec8.
Proof. vm_refl. Qed.
Lemma D_49ec8 : decode_any W_49ec8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ecc : bv 32 := 0x50d120ef.
Lemma F_49ecc : fetch_word Asan.M.loaded_segments (0x49ecc : word) = Some W_49ecc.
Proof. vm_refl. Qed.
Lemma D_49ecc : decode_any W_49ecc = Some (Jal 1 77068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ed0 : bv 32 := 0x80040613.
Lemma F_49ed0 : fetch_word Asan.M.loaded_segments (0x49ed0 : word) = Some W_49ed0.
Proof. vm_refl. Qed.
Lemma D_49ed0 : decode_any W_49ed0 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ed4 : bv 32 := 0xf9860613.
Lemma F_49ed4 : fetch_word Asan.M.loaded_segments (0x49ed4 : word) = Some W_49ed4.
Proof. vm_refl. Qed.
Lemma D_49ed4 : decode_any W_49ed4 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ed8 : bv 32 := 0x00098513.
Lemma F_49ed8 : fetch_word Asan.M.loaded_segments (0x49ed8 : word) = Some W_49ed8.
Proof. vm_refl. Qed.
Lemma D_49ed8 : decode_any W_49ed8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49edc : bv 32 := 0x00048593.
Lemma F_49edc : fetch_word Asan.M.loaded_segments (0x49edc : word) = Some W_49edc.
Proof. vm_refl. Qed.
Lemma D_49edc : decode_any W_49edc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ee0 : bv 32 := 0x2b10f0ef.
Lemma F_49ee0 : fetch_word Asan.M.loaded_segments (0x49ee0 : word) = Some W_49ee0.
Proof. vm_refl. Qed.
Lemma D_49ee0 : decode_any W_49ee0 = Some (Jal 1 64176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ee4 : bv 32 := 0xfbf48513.
Lemma F_49ee4 : fetch_word Asan.M.loaded_segments (0x49ee4 : word) = Some W_49ee4.
Proof. vm_refl. Qed.
Lemma D_49ee4 : decode_any W_49ee4 = Some (OpImm ALU_ADD 10 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ee8 : bv 32 := 0xfbf00593.
Lemma F_49ee8 : fetch_word Asan.M.loaded_segments (0x49ee8 : word) = Some W_49ee8.
Proof. vm_refl. Qed.
Lemma D_49ee8 : decode_any W_49ee8 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49eec : bv 32 := 0xdca5eee3.
Lemma F_49eec : fetch_word Asan.M.loaded_segments (0x49eec : word) = Some W_49eec.
Proof. vm_refl. Qed.
Lemma D_49eec : decode_any W_49eec = Some (Branch BC_LTU 11 10 7644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ef0 : bv 32 := 0x10049263.
Lemma F_49ef0 : fetch_word Asan.M.loaded_segments (0x49ef0 : word) = Some W_49ef0.
Proof. vm_refl. Qed.
Lemma D_49ef0 : decode_any W_49ef0 = Some (Branch BC_NE 9 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ef4 : bv 32 := 0xe11ff06f.
Lemma F_49ef4 : fetch_word Asan.M.loaded_segments (0x49ef4 : word) = Some W_49ef4.
Proof. vm_refl. Qed.
Lemma D_49ef4 : decode_any W_49ef4 = Some (Jal 0 2096656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ef8 : bv 32 := 0x00058603.
Lemma F_49ef8 : fetch_word Asan.M.loaded_segments (0x49ef8 : word) = Some W_49ef8.
Proof. vm_refl. Qed.
Lemma D_49ef8 : decode_any W_49ef8 = Some (Load SZ1 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49efc : bv 32 := 0x007af693.
Lemma F_49efc : fetch_word Asan.M.loaded_segments (0x49efc : word) = Some W_49efc.
Proof. vm_refl. Qed.
Lemma D_49efc : decode_any W_49efc = Some (OpImm ALU_AND 13 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f00 : bv 32 := 0x00c03733.
Lemma F_49f00 : fetch_word Asan.M.loaded_segments (0x49f00 : word) = Some W_49f00.
Proof. vm_refl. Qed.
Lemma D_49f00 : decode_any W_49f00 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f04 : bv 32 := 0x00c6a633.
Lemma F_49f04 : fetch_word Asan.M.loaded_segments (0x49f04 : word) = Some W_49f04.
Proof. vm_refl. Qed.
Lemma D_49f04 : decode_any W_49f04 = Some (Op ALU_SLT 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f08 : bv 32 := 0x00164613.
Lemma F_49f08 : fetch_word Asan.M.loaded_segments (0x49f08 : word) = Some W_49f08.
Proof. vm_refl. Qed.
Lemma D_49f08 : decode_any W_49f08 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f0c : bv 32 := 0x00c77633.
Lemma F_49f0c : fetch_word Asan.M.loaded_segments (0x49f0c : word) = Some W_49f0c.
Proof. vm_refl. Qed.
Lemma D_49f0c : decode_any W_49f0c = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f10 : bv 32 := 0x00b57a63.
Lemma F_49f10 : fetch_word Asan.M.loaded_segments (0x49f10 : word) = Some W_49f10.
Proof. vm_refl. Qed.
Lemma D_49f10 : decode_any W_49f10 = Some (Branch BC_GEU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f14 : bv 32 := 0x00054683.
Lemma F_49f14 : fetch_word Asan.M.loaded_segments (0x49f14 : word) = Some W_49f14.
Proof. vm_refl. Qed.
Lemma D_49f14 : decode_any W_49f14 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f18 : bv 32 := 0x00150513.
Lemma F_49f18 : fetch_word Asan.M.loaded_segments (0x49f18 : word) = Some W_49f18.
Proof. vm_refl. Qed.
Lemma D_49f18 : decode_any W_49f18 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f1c : bv 32 := 0x00c6e633.
Lemma F_49f1c : fetch_word Asan.M.loaded_segments (0x49f1c : word) = Some W_49f1c.
Proof. vm_refl. Qed.
Lemma D_49f1c : decode_any W_49f1c = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f20 : bv 32 := 0xfeb51ae3.
Lemma F_49f20 : fetch_word Asan.M.loaded_segments (0x49f20 : word) = Some W_49f20.
Proof. vm_refl. Qed.
Lemma D_49f20 : decode_any W_49f20 = Some (Branch BC_NE 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f24 : bv 32 := 0x0ff67513.
Lemma F_49f24 : fetch_word Asan.M.loaded_segments (0x49f24 : word) = Some W_49f24.
Proof. vm_refl. Qed.
Lemma D_49f24 : decode_any W_49f24 = Some (OpImm ALU_AND 10 12 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f28 : bv 32 := 0xd80506e3.
Lemma F_49f28 : fetch_word Asan.M.loaded_segments (0x49f28 : word) = Some W_49f28.
Proof. vm_refl. Qed.
Lemma D_49f28 : decode_any W_49f28 = Some (Branch BC_EQ 10 0 7564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f2c : bv 32 := 0x00090513.
Lemma F_49f2c : fetch_word Asan.M.loaded_segments (0x49f2c : word) = Some W_49f2c.
Proof. vm_refl. Qed.
Lemma D_49f2c : decode_any W_49f2c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f30 : bv 32 := 0x000a0593.
Lemma F_49f30 : fetch_word Asan.M.loaded_segments (0x49f30 : word) = Some W_49f30.
Proof. vm_refl. Qed.
Lemma D_49f30 : decode_any W_49f30 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f34 : bv 32 := 0x2790c0ef.
Lemma F_49f34 : fetch_word Asan.M.loaded_segments (0x49f34 : word) = Some W_49f34.
Proof. vm_refl. Qed.
Lemma D_49f34 : decode_any W_49f34 = Some (Jal 1 51832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f38 : bv 32 := 0xd6050ee3.
Lemma F_49f38 : fetch_word Asan.M.loaded_segments (0x49f38 : word) = Some W_49f38.
Proof. vm_refl. Qed.
Lemma D_49f38 : decode_any W_49f38 = Some (Branch BC_EQ 10 0 7548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f3c : bv 32 := 0x00050a93.
Lemma F_49f3c : fetch_word Asan.M.loaded_segments (0x49f3c : word) = Some W_49f3c.
Proof. vm_refl. Qed.
Lemma D_49f3c : decode_any W_49f3c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f40 : bv 32 := 0xfffd6517.
Lemma F_49f40 : fetch_word Asan.M.loaded_segments (0x49f40 : word) = Some W_49f40.
Proof. vm_refl. Qed.
Lemma D_49f40 : decode_any W_49f40 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f44 : bv 32 := 0x87150513.
Lemma F_49f44 : fetch_word Asan.M.loaded_segments (0x49f44 : word) = Some W_49f44.
Proof. vm_refl. Qed.
Lemma D_49f44 : decode_any W_49f44 = Some (OpImm ALU_ADD 10 10 2161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f48 : bv 32 := 0x43d130ef.
Lemma F_49f48 : fetch_word Asan.M.loaded_segments (0x49f48 : word) = Some W_49f48.
Proof. vm_refl. Qed.
Lemma D_49f48 : decode_any W_49f48 = Some (Jal 1 80956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f4c : bv 32 := 0xd60514e3.
Lemma F_49f4c : fetch_word Asan.M.loaded_segments (0x49f4c : word) = Some W_49f4c.
Proof. vm_refl. Qed.
Lemma D_49f4c : decode_any W_49f4c = Some (Branch BC_NE 10 0 7528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f50 : bv 32 := 0x49d130ef.
Lemma F_49f50 : fetch_word Asan.M.loaded_segments (0x49f50 : word) = Some W_49f50.
Proof. vm_refl. Qed.
Lemma D_49f50 : decode_any W_49f50 = Some (Jal 1 81052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f54 : bv 32 := 0x12050a63.
Lemma F_49f54 : fetch_word Asan.M.loaded_segments (0x49f54 : word) = Some W_49f54.
Proof. vm_refl. Qed.
Lemma D_49f54 : decode_any W_49f54 = Some (Branch BC_EQ 10 0 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f58 : bv 32 := 0x80040513.
Lemma F_49f58 : fetch_word Asan.M.loaded_segments (0x49f58 : word) = Some W_49f58.
Proof. vm_refl. Qed.
Lemma D_49f58 : decode_any W_49f58 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f5c : bv 32 := 0xfa850513.
Lemma F_49f5c : fetch_word Asan.M.loaded_segments (0x49f5c : word) = Some W_49f5c.
Proof. vm_refl. Qed.
Lemma D_49f5c : decode_any W_49f5c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f60 : bv 32 := 0x80040593.
Lemma F_49f60 : fetch_word Asan.M.loaded_segments (0x49f60 : word) = Some W_49f60.
Proof. vm_refl. Qed.
Lemma D_49f60 : decode_any W_49f60 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f64 : bv 32 := 0xf9858593.
Lemma F_49f64 : fetch_word Asan.M.loaded_segments (0x49f64 : word) = Some W_49f64.
Proof. vm_refl. Qed.
Lemma D_49f64 : decode_any W_49f64 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f68 : bv 32 := 0x7ff58b13.
Lemma F_49f68 : fetch_word Asan.M.loaded_segments (0x49f68 : word) = Some W_49f68.
Proof. vm_refl. Qed.
Lemma D_49f68 : decode_any W_49f68 = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f6c : bv 32 := 0x000b34a3.
Lemma F_49f6c : fetch_word Asan.M.loaded_segments (0x49f6c : word) = Some W_49f6c.
Proof. vm_refl. Qed.
Lemma D_49f6c : decode_any W_49f6c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f70 : bv 32 := 0x00ac3023.
Lemma F_49f70 : fetch_word Asan.M.loaded_segments (0x49f70 : word) = Some W_49f70.
Proof. vm_refl. Qed.
Lemma D_49f70 : decode_any W_49f70 = Some (Store SZ8 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f74 : bv 32 := 0x000c3423.
Lemma F_49f74 : fetch_word Asan.M.loaded_segments (0x49f74 : word) = Some W_49f74.
Proof. vm_refl. Qed.
Lemma D_49f74 : decode_any W_49f74 = Some (Store SZ8 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f78 : bv 32 := 0x7102b0ef.
Lemma F_49f78 : fetch_word Asan.M.loaded_segments (0x49f78 : word) = Some W_49f78.
Proof. vm_refl. Qed.
Lemma D_49f78 : decode_any W_49f78 = Some (Jal 1 177936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f7c : bv 32 := 0x00050593.
Lemma F_49f7c : fetch_word Asan.M.loaded_segments (0x49f7c : word) = Some W_49f7c.
Proof. vm_refl. Qed.
Lemma D_49f7c : decode_any W_49f7c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f80 : bv 32 := 0x00061517.
Lemma F_49f80 : fetch_word Asan.M.loaded_segments (0x49f80 : word) = Some W_49f80.
Proof. vm_refl. Qed.
Lemma D_49f80 : decode_any W_49f80 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f84 : bv 32 := 0xef053503.
Lemma F_49f84 : fetch_word Asan.M.loaded_segments (0x49f84 : word) = Some W_49f84.
Proof. vm_refl. Qed.
Lemma D_49f84 : decode_any W_49f84 = Some (Load SZ8 true 10 10 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f88 : bv 32 := 0x02154703.
Lemma F_49f88 : fetch_word Asan.M.loaded_segments (0x49f88 : word) = Some W_49f88.
Proof. vm_refl. Qed.
Lemma D_49f88 : decode_any W_49f88 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f8c : bv 32 := 0x008b34a3.
Lemma F_49f8c : fetch_word Asan.M.loaded_segments (0x49f8c : word) = Some W_49f8c.
Proof. vm_refl. Qed.
Lemma D_49f8c : decode_any W_49f8c = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f90 : bv 32 := 0x80040513.
Lemma F_49f90 : fetch_word Asan.M.loaded_segments (0x49f90 : word) = Some W_49f90.
Proof. vm_refl. Qed.
Lemma D_49f90 : decode_any W_49f90 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f94 : bv 32 := 0xf9850513.
Lemma F_49f94 : fetch_word Asan.M.loaded_segments (0x49f94 : word) = Some W_49f94.
Proof. vm_refl. Qed.
Lemma D_49f94 : decode_any W_49f94 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f98 : bv 32 := 0x0ff00793.
Lemma F_49f98 : fetch_word Asan.M.loaded_segments (0x49f98 : word) = Some W_49f98.
Proof. vm_refl. Qed.
Lemma D_49f98 : decode_any W_49f98 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49f9c : bv 32 := 0x00040613.
Lemma F_49f9c : fetch_word Asan.M.loaded_segments (0x49f9c : word) = Some W_49f9c.
Proof. vm_refl. Qed.
Lemma D_49f9c : decode_any W_49f9c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fa0 : bv 32 := 0x00000693.
Lemma F_49fa0 : fetch_word Asan.M.loaded_segments (0x49fa0 : word) = Some W_49fa0.
Proof. vm_refl. Qed.
Lemma D_49fa0 : decode_any W_49fa0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fa4 : bv 32 := 0x435120ef.
Lemma F_49fa4 : fetch_word Asan.M.loaded_segments (0x49fa4 : word) = Some W_49fa4.
Proof. vm_refl. Qed.
Lemma D_49fa4 : decode_any W_49fa4 = Some (Jal 1 76852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fa8 : bv 32 := 0x80040513.
Lemma F_49fa8 : fetch_word Asan.M.loaded_segments (0x49fa8 : word) = Some W_49fa8.
Proof. vm_refl. Qed.
Lemma D_49fa8 : decode_any W_49fa8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fac : bv 32 := 0xf9850513.
Lemma F_49fac : fetch_word Asan.M.loaded_segments (0x49fac : word) = Some W_49fac.
Proof. vm_refl. Qed.
Lemma D_49fac : decode_any W_49fac = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fb0 : bv 32 := 0x745130ef.
Lemma F_49fb0 : fetch_word Asan.M.loaded_segments (0x49fb0 : word) = Some W_49fb0.
Proof. vm_refl. Qed.
Lemma D_49fb0 : decode_any W_49fb0 = Some (Jal 1 81732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fb4 : bv 32 := 0x00040b13.
Lemma F_49fb4 : fetch_word Asan.M.loaded_segments (0x49fb4 : word) = Some W_49fb4.
Proof. vm_refl. Qed.
Lemma D_49fb4 : decode_any W_49fb4 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fb8 : bv 32 := 0xce051ee3.
Lemma F_49fb8 : fetch_word Asan.M.loaded_segments (0x49fb8 : word) = Some W_49fb8.
Proof. vm_refl. Qed.
Lemma D_49fb8 : decode_any W_49fb8 = Some (Branch BC_NE 10 0 7420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fbc : bv 32 := 0x0d00006f.
Lemma F_49fbc : fetch_word Asan.M.loaded_segments (0x49fbc : word) = Some W_49fbc.
Proof. vm_refl. Qed.
Lemma D_49fbc : decode_any W_49fbc = Some (Jal 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fc0 : bv 32 := 0x00058683.
Lemma F_49fc0 : fetch_word Asan.M.loaded_segments (0x49fc0 : word) = Some W_49fc0.
Proof. vm_refl. Qed.
Lemma D_49fc0 : decode_any W_49fc0 = Some (Load SZ1 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fc4 : bv 32 := 0x00767613.
Lemma F_49fc4 : fetch_word Asan.M.loaded_segments (0x49fc4 : word) = Some W_49fc4.
Proof. vm_refl. Qed.
Lemma D_49fc4 : decode_any W_49fc4 = Some (OpImm ALU_AND 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fc8 : bv 32 := 0x00d03733.
Lemma F_49fc8 : fetch_word Asan.M.loaded_segments (0x49fc8 : word) = Some W_49fc8.
Proof. vm_refl. Qed.
Lemma D_49fc8 : decode_any W_49fc8 = Some (Op ALU_SLTU 14 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fcc : bv 32 := 0x00d62633.
Lemma F_49fcc : fetch_word Asan.M.loaded_segments (0x49fcc : word) = Some W_49fcc.
Proof. vm_refl. Qed.
Lemma D_49fcc : decode_any W_49fcc = Some (Op ALU_SLT 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fd0 : bv 32 := 0x00164613.
Lemma F_49fd0 : fetch_word Asan.M.loaded_segments (0x49fd0 : word) = Some W_49fd0.
Proof. vm_refl. Qed.
Lemma D_49fd0 : decode_any W_49fd0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fd4 : bv 32 := 0x00c77633.
Lemma F_49fd4 : fetch_word Asan.M.loaded_segments (0x49fd4 : word) = Some W_49fd4.
Proof. vm_refl. Qed.
Lemma D_49fd4 : decode_any W_49fd4 = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fd8 : bv 32 := 0x00b57a63.
Lemma F_49fd8 : fetch_word Asan.M.loaded_segments (0x49fd8 : word) = Some W_49fd8.
Proof. vm_refl. Qed.
Lemma D_49fd8 : decode_any W_49fd8 = Some (Branch BC_GEU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fdc : bv 32 := 0x00054683.
Lemma F_49fdc : fetch_word Asan.M.loaded_segments (0x49fdc : word) = Some W_49fdc.
Proof. vm_refl. Qed.
Lemma D_49fdc : decode_any W_49fdc = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fe0 : bv 32 := 0x00150513.
Lemma F_49fe0 : fetch_word Asan.M.loaded_segments (0x49fe0 : word) = Some W_49fe0.
Proof. vm_refl. Qed.
Lemma D_49fe0 : decode_any W_49fe0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fe4 : bv 32 := 0x00c6e633.
Lemma F_49fe4 : fetch_word Asan.M.loaded_segments (0x49fe4 : word) = Some W_49fe4.
Proof. vm_refl. Qed.
Lemma D_49fe4 : decode_any W_49fe4 = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fe8 : bv 32 := 0xfeb51ae3.
Lemma F_49fe8 : fetch_word Asan.M.loaded_segments (0x49fe8 : word) = Some W_49fe8.
Proof. vm_refl. Qed.
Lemma D_49fe8 : decode_any W_49fe8 = Some (Branch BC_NE 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49fec : bv 32 := 0x0ff67513.
Lemma F_49fec : fetch_word Asan.M.loaded_segments (0x49fec : word) = Some W_49fec.
Proof. vm_refl. Qed.
Lemma D_49fec : decode_any W_49fec = Some (OpImm ALU_AND 10 12 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ff0 : bv 32 := 0xd0050ae3.
Lemma F_49ff0 : fetch_word Asan.M.loaded_segments (0x49ff0 : word) = Some W_49ff0.
Proof. vm_refl. Qed.
Lemma D_49ff0 : decode_any W_49ff0 = Some (Branch BC_EQ 10 0 7444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ff4 : bv 32 := 0x00098513.
Lemma F_49ff4 : fetch_word Asan.M.loaded_segments (0x49ff4 : word) = Some W_49ff4.
Proof. vm_refl. Qed.
Lemma D_49ff4 : decode_any W_49ff4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ff8 : bv 32 := 0x00048593.
Lemma F_49ff8 : fetch_word Asan.M.loaded_segments (0x49ff8 : word) = Some W_49ff8.
Proof. vm_refl. Qed.
Lemma D_49ff8 : decode_any W_49ff8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_49ffc : bv 32 := 0x1b10c0ef.
Lemma F_49ffc : fetch_word Asan.M.loaded_segments (0x49ffc : word) = Some W_49ffc.
Proof. vm_refl. Qed.
Lemma D_49ffc : decode_any W_49ffc = Some (Jal 1 51632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a000 : bv 32 := 0xd00502e3.
Lemma F_4a000 : fetch_word Asan.M.loaded_segments (0x4a000 : word) = Some W_4a000.
Proof. vm_refl. Qed.
Lemma D_4a000 : decode_any W_4a000 = Some (Branch BC_EQ 10 0 7428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a004 : bv 32 := 0x00050a13.
Lemma F_4a004 : fetch_word Asan.M.loaded_segments (0x4a004 : word) = Some W_4a004.
Proof. vm_refl. Qed.
Lemma D_4a004 : decode_any W_4a004 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a008 : bv 32 := 0xfffd5517.
Lemma F_4a008 : fetch_word Asan.M.loaded_segments (0x4a008 : word) = Some W_4a008.
Proof. vm_refl. Qed.
Lemma D_4a008 : decode_any W_4a008 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a00c : bv 32 := 0x7a950513.
Lemma F_4a00c : fetch_word Asan.M.loaded_segments (0x4a00c : word) = Some W_4a00c.
Proof. vm_refl. Qed.
Lemma D_4a00c : decode_any W_4a00c = Some (OpImm ALU_ADD 10 10 1961, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a010 : bv 32 := 0x375130ef.
Lemma F_4a010 : fetch_word Asan.M.loaded_segments (0x4a010 : word) = Some W_4a010.
Proof. vm_refl. Qed.
Lemma D_4a010 : decode_any W_4a010 = Some (Jal 1 80756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a014 : bv 32 := 0xce0518e3.
Lemma F_4a014 : fetch_word Asan.M.loaded_segments (0x4a014 : word) = Some W_4a014.
Proof. vm_refl. Qed.
Lemma D_4a014 : decode_any W_4a014 = Some (Branch BC_NE 10 0 7408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a018 : bv 32 := 0x3d5130ef.
Lemma F_4a018 : fetch_word Asan.M.loaded_segments (0x4a018 : word) = Some W_4a018.
Proof. vm_refl. Qed.
Lemma D_4a018 : decode_any W_4a018 = Some (Jal 1 80852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a01c : bv 32 := 0x0a050463.
Lemma F_4a01c : fetch_word Asan.M.loaded_segments (0x4a01c : word) = Some W_4a01c.
Proof. vm_refl. Qed.
Lemma D_4a01c : decode_any W_4a01c = Some (Branch BC_EQ 10 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a020 : bv 32 := 0x80040513.
Lemma F_4a020 : fetch_word Asan.M.loaded_segments (0x4a020 : word) = Some W_4a020.
Proof. vm_refl. Qed.
Lemma D_4a020 : decode_any W_4a020 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a024 : bv 32 := 0xfa850513.
Lemma F_4a024 : fetch_word Asan.M.loaded_segments (0x4a024 : word) = Some W_4a024.
Proof. vm_refl. Qed.
Lemma D_4a024 : decode_any W_4a024 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a028 : bv 32 := 0x80040593.
Lemma F_4a028 : fetch_word Asan.M.loaded_segments (0x4a028 : word) = Some W_4a028.
Proof. vm_refl. Qed.
Lemma D_4a028 : decode_any W_4a028 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a02c : bv 32 := 0xf9858593.
Lemma F_4a02c : fetch_word Asan.M.loaded_segments (0x4a02c : word) = Some W_4a02c.
Proof. vm_refl. Qed.
Lemma D_4a02c : decode_any W_4a02c = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a030 : bv 32 := 0x7ff58a93.
Lemma F_4a030 : fetch_word Asan.M.loaded_segments (0x4a030 : word) = Some W_4a030.
Proof. vm_refl. Qed.
Lemma D_4a030 : decode_any W_4a030 = Some (OpImm ALU_ADD 21 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a034 : bv 32 := 0x000ab4a3.
Lemma F_4a034 : fetch_word Asan.M.loaded_segments (0x4a034 : word) = Some W_4a034.
Proof. vm_refl. Qed.
Lemma D_4a034 : decode_any W_4a034 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a038 : bv 32 := 0x00ac3023.
Lemma F_4a038 : fetch_word Asan.M.loaded_segments (0x4a038 : word) = Some W_4a038.
Proof. vm_refl. Qed.
Lemma D_4a038 : decode_any W_4a038 = Some (Store SZ8 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a03c : bv 32 := 0x000c3423.
Lemma F_4a03c : fetch_word Asan.M.loaded_segments (0x4a03c : word) = Some W_4a03c.
Proof. vm_refl. Qed.
Lemma D_4a03c : decode_any W_4a03c = Some (Store SZ8 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a040 : bv 32 := 0x6482b0ef.
Lemma F_4a040 : fetch_word Asan.M.loaded_segments (0x4a040 : word) = Some W_4a040.
Proof. vm_refl. Qed.
Lemma D_4a040 : decode_any W_4a040 = Some (Jal 1 177736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a044 : bv 32 := 0x00050593.
Lemma F_4a044 : fetch_word Asan.M.loaded_segments (0x4a044 : word) = Some W_4a044.
Proof. vm_refl. Qed.
Lemma D_4a044 : decode_any W_4a044 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a048 : bv 32 := 0x00061517.
Lemma F_4a048 : fetch_word Asan.M.loaded_segments (0x4a048 : word) = Some W_4a048.
Proof. vm_refl. Qed.
Lemma D_4a048 : decode_any W_4a048 = Some (Auipc 10 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a04c : bv 32 := 0xe2853503.
Lemma F_4a04c : fetch_word Asan.M.loaded_segments (0x4a04c : word) = Some W_4a04c.
Proof. vm_refl. Qed.
Lemma D_4a04c : decode_any W_4a04c = Some (Load SZ8 true 10 10 3624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a050 : bv 32 := 0x02154703.
Lemma F_4a050 : fetch_word Asan.M.loaded_segments (0x4a050 : word) = Some W_4a050.
Proof. vm_refl. Qed.
Lemma D_4a050 : decode_any W_4a050 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a054 : bv 32 := 0x008ab4a3.
Lemma F_4a054 : fetch_word Asan.M.loaded_segments (0x4a054 : word) = Some W_4a054.
Proof. vm_refl. Qed.
Lemma D_4a054 : decode_any W_4a054 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a058 : bv 32 := 0x80040513.
Lemma F_4a058 : fetch_word Asan.M.loaded_segments (0x4a058 : word) = Some W_4a058.
Proof. vm_refl. Qed.
Lemma D_4a058 : decode_any W_4a058 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a05c : bv 32 := 0xf9850513.
Lemma F_4a05c : fetch_word Asan.M.loaded_segments (0x4a05c : word) = Some W_4a05c.
Proof. vm_refl. Qed.
Lemma D_4a05c : decode_any W_4a05c = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a060 : bv 32 := 0x0ff00793.
Lemma F_4a060 : fetch_word Asan.M.loaded_segments (0x4a060 : word) = Some W_4a060.
Proof. vm_refl. Qed.
Lemma D_4a060 : decode_any W_4a060 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a064 : bv 32 := 0x00040613.
Lemma F_4a064 : fetch_word Asan.M.loaded_segments (0x4a064 : word) = Some W_4a064.
Proof. vm_refl. Qed.
Lemma D_4a064 : decode_any W_4a064 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a068 : bv 32 := 0x00000693.
Lemma F_4a068 : fetch_word Asan.M.loaded_segments (0x4a068 : word) = Some W_4a068.
Proof. vm_refl. Qed.
Lemma D_4a068 : decode_any W_4a068 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a06c : bv 32 := 0x36d120ef.
Lemma F_4a06c : fetch_word Asan.M.loaded_segments (0x4a06c : word) = Some W_4a06c.
Proof. vm_refl. Qed.
Lemma D_4a06c : decode_any W_4a06c = Some (Jal 1 76652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a070 : bv 32 := 0x80040513.
Lemma F_4a070 : fetch_word Asan.M.loaded_segments (0x4a070 : word) = Some W_4a070.
Proof. vm_refl. Qed.
Lemma D_4a070 : decode_any W_4a070 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a074 : bv 32 := 0xf9850513.
Lemma F_4a074 : fetch_word Asan.M.loaded_segments (0x4a074 : word) = Some W_4a074.
Proof. vm_refl. Qed.
Lemma D_4a074 : decode_any W_4a074 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a078 : bv 32 := 0x67d130ef.
Lemma F_4a078 : fetch_word Asan.M.loaded_segments (0x4a078 : word) = Some W_4a078.
Proof. vm_refl. Qed.
Lemma D_4a078 : decode_any W_4a078 = Some (Jal 1 81532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a07c : bv 32 := 0x00040a93.
Lemma F_4a07c : fetch_word Asan.M.loaded_segments (0x4a07c : word) = Some W_4a07c.
Proof. vm_refl. Qed.
Lemma D_4a07c : decode_any W_4a07c = Some (OpImm ALU_ADD 21 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a080 : bv 32 := 0xc80512e3.
Lemma F_4a080 : fetch_word Asan.M.loaded_segments (0x4a080 : word) = Some W_4a080.
Proof. vm_refl. Qed.
Lemma D_4a080 : decode_any W_4a080 = Some (Branch BC_NE 10 0 7300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a084 : bv 32 := 0x0440006f.
Lemma F_4a084 : fetch_word Asan.M.loaded_segments (0x4a084 : word) = Some W_4a084.
Proof. vm_refl. Qed.
Lemma D_4a084 : decode_any W_4a084 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a088 : bv 32 := 0x00040b13.
Lemma F_4a088 : fetch_word Asan.M.loaded_segments (0x4a088 : word) = Some W_4a088.
Proof. vm_refl. Qed.
Lemma D_4a088 : decode_any W_4a088 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a08c : bv 32 := 0x5fc2b0ef.
Lemma F_4a08c : fetch_word Asan.M.loaded_segments (0x4a08c : word) = Some W_4a08c.
Proof. vm_refl. Qed.
Lemma D_4a08c : decode_any W_4a08c = Some (Jal 1 177660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a090 : bv 32 := 0xfffc6597.
Lemma F_4a090 : fetch_word Asan.M.loaded_segments (0x4a090 : word) = Some W_4a090.
Proof. vm_refl. Qed.
Lemma D_4a090 : decode_any W_4a090 = Some (Auipc 11 1048518, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a094 : bv 32 := 0x3685b583.
Lemma F_4a094 : fetch_word Asan.M.loaded_segments (0x4a094 : word) = Some W_4a094.
Proof. vm_refl. Qed.
Lemma D_4a094 : decode_any W_4a094 = Some (Load SZ8 true 11 11 872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a098 : bv 32 := 0x00bc3023.
Lemma F_4a098 : fetch_word Asan.M.loaded_segments (0x4a098 : word) = Some W_4a098.
Proof. vm_refl. Qed.
Lemma D_4a098 : decode_any W_4a098 = Some (Store SZ8 24 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a09c : bv 32 := 0x80040613.
Lemma F_4a09c : fetch_word Asan.M.loaded_segments (0x4a09c : word) = Some W_4a09c.
Proof. vm_refl. Qed.
Lemma D_4a09c : decode_any W_4a09c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0a0 : bv 32 := 0xf9860613.
Lemma F_4a0a0 : fetch_word Asan.M.loaded_segments (0x4a0a0 : word) = Some W_4a0a0.
Proof. vm_refl. Qed.
Lemma D_4a0a0 : decode_any W_4a0a0 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0a4 : bv 32 := 0x000b0593.
Lemma F_4a0a4 : fetch_word Asan.M.loaded_segments (0x4a0a4 : word) = Some W_4a0a4.
Proof. vm_refl. Qed.
Lemma D_4a0a4 : decode_any W_4a0a4 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0a8 : bv 32 := 0x000a8693.
Lemma F_4a0a8 : fetch_word Asan.M.loaded_segments (0x4a0a8 : word) = Some W_4a0a8.
Proof. vm_refl. Qed.
Lemma D_4a0a8 : decode_any W_4a0a8 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0ac : bv 32 := 0x00000713.
Lemma F_4a0ac : fetch_word Asan.M.loaded_segments (0x4a0ac : word) = Some W_4a0ac.
Proof. vm_refl. Qed.
Lemma D_4a0ac : decode_any W_4a0ac = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0b0 : bv 32 := 0x000a0793.
Lemma F_4a0b0 : fetch_word Asan.M.loaded_segments (0x4a0b0 : word) = Some W_4a0b0.
Proof. vm_refl. Qed.
Lemma D_4a0b0 : decode_any W_4a0b0 = Some (OpImm ALU_ADD 15 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0b4 : bv 32 := 0x00000813.
Lemma F_4a0b4 : fetch_word Asan.M.loaded_segments (0x4a0b4 : word) = Some W_4a0b4.
Proof. vm_refl. Qed.
Lemma D_4a0b4 : decode_any W_4a0b4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0b8 : bv 32 := 0x00000893.
Lemma F_4a0b8 : fetch_word Asan.M.loaded_segments (0x4a0b8 : word) = Some W_4a0b8.
Proof. vm_refl. Qed.
Lemma D_4a0b8 : decode_any W_4a0b8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0bc : bv 32 := 0x62d0f0ef.
Lemma F_4a0bc : fetch_word Asan.M.loaded_segments (0x4a0bc : word) = Some W_4a0bc.
Proof. vm_refl. Qed.
Lemma D_4a0bc : decode_any W_4a0bc = Some (Jal 1 65068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0c0 : bv 32 := 0xbf5ff06f.
Lemma F_4a0c0 : fetch_word Asan.M.loaded_segments (0x4a0c0 : word) = Some W_4a0c0.
Proof. vm_refl. Qed.
Lemma D_4a0c0 : decode_any W_4a0c0 = Some (Jal 0 2096116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0c4 : bv 32 := 0x00040a93.
Lemma F_4a0c4 : fetch_word Asan.M.loaded_segments (0x4a0c4 : word) = Some W_4a0c4.
Proof. vm_refl. Qed.
Lemma D_4a0c4 : decode_any W_4a0c4 = Some (OpImm ALU_ADD 21 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0c8 : bv 32 := 0x5c02b0ef.
Lemma F_4a0c8 : fetch_word Asan.M.loaded_segments (0x4a0c8 : word) = Some W_4a0c8.
Proof. vm_refl. Qed.
Lemma D_4a0c8 : decode_any W_4a0c8 = Some (Jal 1 177600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0cc : bv 32 := 0xfffc6597.
Lemma F_4a0cc : fetch_word Asan.M.loaded_segments (0x4a0cc : word) = Some W_4a0cc.
Proof. vm_refl. Qed.
Lemma D_4a0cc : decode_any W_4a0cc = Some (Auipc 11 1048518, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0d0 : bv 32 := 0x32c5b583.
Lemma F_4a0d0 : fetch_word Asan.M.loaded_segments (0x4a0d0 : word) = Some W_4a0d0.
Proof. vm_refl. Qed.
Lemma D_4a0d0 : decode_any W_4a0d0 = Some (Load SZ8 true 11 11 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0d4 : bv 32 := 0x00bc3023.
Lemma F_4a0d4 : fetch_word Asan.M.loaded_segments (0x4a0d4 : word) = Some W_4a0d4.
Proof. vm_refl. Qed.
Lemma D_4a0d4 : decode_any W_4a0d4 = Some (Store SZ8 24 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0d8 : bv 32 := 0x80040613.
Lemma F_4a0d8 : fetch_word Asan.M.loaded_segments (0x4a0d8 : word) = Some W_4a0d8.
Proof. vm_refl. Qed.
Lemma D_4a0d8 : decode_any W_4a0d8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0dc : bv 32 := 0xf9860613.
Lemma F_4a0dc : fetch_word Asan.M.loaded_segments (0x4a0dc : word) = Some W_4a0dc.
Proof. vm_refl. Qed.
Lemma D_4a0dc : decode_any W_4a0dc = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0e0 : bv 32 := 0x00100713.
Lemma F_4a0e0 : fetch_word Asan.M.loaded_segments (0x4a0e0 : word) = Some W_4a0e0.
Proof. vm_refl. Qed.
Lemma D_4a0e0 : decode_any W_4a0e0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0e4 : bv 32 := 0x000a8593.
Lemma F_4a0e4 : fetch_word Asan.M.loaded_segments (0x4a0e4 : word) = Some W_4a0e4.
Proof. vm_refl. Qed.
Lemma D_4a0e4 : decode_any W_4a0e4 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0e8 : bv 32 := 0x000a0693.
Lemma F_4a0e8 : fetch_word Asan.M.loaded_segments (0x4a0e8 : word) = Some W_4a0e8.
Proof. vm_refl. Qed.
Lemma D_4a0e8 : decode_any W_4a0e8 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0ec : bv 32 := 0x00048793.
Lemma F_4a0ec : fetch_word Asan.M.loaded_segments (0x4a0ec : word) = Some W_4a0ec.
Proof. vm_refl. Qed.
Lemma D_4a0ec : decode_any W_4a0ec = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0f0 : bv 32 := 0x00000813.
Lemma F_4a0f0 : fetch_word Asan.M.loaded_segments (0x4a0f0 : word) = Some W_4a0f0.
Proof. vm_refl. Qed.
Lemma D_4a0f0 : decode_any W_4a0f0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0f4 : bv 32 := 0x00000893.
Lemma F_4a0f4 : fetch_word Asan.M.loaded_segments (0x4a0f4 : word) = Some W_4a0f4.
Proof. vm_refl. Qed.
Lemma D_4a0f4 : decode_any W_4a0f4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0f8 : bv 32 := 0x5f10f0ef.
Lemma F_4a0f8 : fetch_word Asan.M.loaded_segments (0x4a0f8 : word) = Some W_4a0f8.
Proof. vm_refl. Qed.
Lemma D_4a0f8 : decode_any W_4a0f8 = Some (Jal 1 65008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4a0fc : bv 32 := 0xc09ff06f.
Lemma F_4a0fc : fetch_word Asan.M.loaded_segments (0x4a0fc : word) = Some W_4a0fc.
Proof. vm_refl. Qed.
Lemma D_4a0fc : decode_any W_4a0fc = Some (Jal 0 2096136, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_5bafc : bv 32 := 0xff010113.
Lemma F_5bafc : fetch_word Asan.M.loaded_segments (0x5bafc : word) = Some W_5bafc.
Proof. vm_refl. Qed.
Lemma D_5bafc : decode_any W_5bafc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb00 : bv 32 := 0x00113423.
Lemma F_5bb00 : fetch_word Asan.M.loaded_segments (0x5bb00 : word) = Some W_5bb00.
Proof. vm_refl. Qed.
Lemma D_5bb00 : decode_any W_5bb00 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb04 : bv 32 := 0x00813023.
Lemma F_5bb04 : fetch_word Asan.M.loaded_segments (0x5bb04 : word) = Some W_5bb04.
Proof. vm_refl. Qed.
Lemma D_5bb04 : decode_any W_5bb04 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb08 : bv 32 := 0x00058517.
Lemma F_5bb08 : fetch_word Asan.M.loaded_segments (0x5bb08 : word) = Some W_5bb08.
Proof. vm_refl. Qed.
Lemma D_5bb08 : decode_any W_5bb08 = Some (Auipc 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb0c : bv 32 := 0x7d050413.
Lemma F_5bb0c : fetch_word Asan.M.loaded_segments (0x5bb0c : word) = Some W_5bb0c.
Proof. vm_refl. Qed.
Lemma D_5bb0c : decode_any W_5bb0c = Some (OpImm ALU_ADD 8 10 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb10 : bv 32 := 0x00040503.
Lemma F_5bb10 : fetch_word Asan.M.loaded_segments (0x5bb10 : word) = Some W_5bb10.
Proof. vm_refl. Qed.
Lemma D_5bb10 : decode_any W_5bb10 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb14 : bv 32 := 0x00100593.
Lemma F_5bb14 : fetch_word Asan.M.loaded_segments (0x5bb14 : word) = Some W_5bb14.
Proof. vm_refl. Qed.
Lemma D_5bb14 : decode_any W_5bb14 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb18 : bv 32 := 0x0230000f.
Lemma F_5bb18 : fetch_word Asan.M.loaded_segments (0x5bb18 : word) = Some W_5bb18.
Proof. vm_refl. Qed.
Lemma D_5bb18 : decode_any W_5bb18 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb1c : bv 32 := 0x00b51a63.
Lemma F_5bb1c : fetch_word Asan.M.loaded_segments (0x5bb1c : word) = Some W_5bb1c.
Proof. vm_refl. Qed.
Lemma D_5bb1c : decode_any W_5bb1c = Some (Branch BC_NE 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb20 : bv 32 := 0x00813083.
Lemma F_5bb20 : fetch_word Asan.M.loaded_segments (0x5bb20 : word) = Some W_5bb20.
Proof. vm_refl. Qed.
Lemma D_5bb20 : decode_any W_5bb20 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb24 : bv 32 := 0x00013403.
Lemma F_5bb24 : fetch_word Asan.M.loaded_segments (0x5bb24 : word) = Some W_5bb24.
Proof. vm_refl. Qed.
Lemma D_5bb24 : decode_any W_5bb24 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb28 : bv 32 := 0x01010113.
Lemma F_5bb28 : fetch_word Asan.M.loaded_segments (0x5bb28 : word) = Some W_5bb28.
Proof. vm_refl. Qed.
Lemma D_5bb28 : decode_any W_5bb28 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bb2c : bv 32 := 0x00008067.
Lemma F_5bb2c : fetch_word Asan.M.loaded_segments (0x5bb2c : word) = Some W_5bb2c.
Proof. vm_refl. Qed.
Lemma D_5bb2c : decode_any W_5bb2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
