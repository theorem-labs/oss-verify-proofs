(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_659d4 : bv 32 := 0xf7010113.
Lemma F_659d4 : fetch_word Asan.M.loaded_segments (0x65a24 : word) = Some W_659d4.
Proof. vm_refl. Qed.
Lemma D_659d4 : decode_any W_659d4 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659d8 : bv 32 := 0x08113423.
Lemma F_659d8 : fetch_word Asan.M.loaded_segments (0x65a28 : word) = Some W_659d8.
Proof. vm_refl. Qed.
Lemma D_659d8 : decode_any W_659d8 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659dc : bv 32 := 0x08813023.
Lemma F_659dc : fetch_word Asan.M.loaded_segments (0x65a2c : word) = Some W_659dc.
Proof. vm_refl. Qed.
Lemma D_659dc : decode_any W_659dc = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659e0 : bv 32 := 0x06913c23.
Lemma F_659e0 : fetch_word Asan.M.loaded_segments (0x65a30 : word) = Some W_659e0.
Proof. vm_refl. Qed.
Lemma D_659e0 : decode_any W_659e0 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659e4 : bv 32 := 0x07213823.
Lemma F_659e4 : fetch_word Asan.M.loaded_segments (0x65a34 : word) = Some W_659e4.
Proof. vm_refl. Qed.
Lemma D_659e4 : decode_any W_659e4 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659e8 : bv 32 := 0x07313423.
Lemma F_659e8 : fetch_word Asan.M.loaded_segments (0x65a38 : word) = Some W_659e8.
Proof. vm_refl. Qed.
Lemma D_659e8 : decode_any W_659e8 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659ec : bv 32 := 0x07413023.
Lemma F_659ec : fetch_word Asan.M.loaded_segments (0x65a3c : word) = Some W_659ec.
Proof. vm_refl. Qed.
Lemma D_659ec : decode_any W_659ec = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659f0 : bv 32 := 0x05513c23.
Lemma F_659f0 : fetch_word Asan.M.loaded_segments (0x65a40 : word) = Some W_659f0.
Proof. vm_refl. Qed.
Lemma D_659f0 : decode_any W_659f0 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659f4 : bv 32 := 0x05613823.
Lemma F_659f4 : fetch_word Asan.M.loaded_segments (0x65a44 : word) = Some W_659f4.
Proof. vm_refl. Qed.
Lemma D_659f4 : decode_any W_659f4 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659f8 : bv 32 := 0x05713423.
Lemma F_659f8 : fetch_word Asan.M.loaded_segments (0x65a48 : word) = Some W_659f8.
Proof. vm_refl. Qed.
Lemma D_659f8 : decode_any W_659f8 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_659fc : bv 32 := 0x05813023.
Lemma F_659fc : fetch_word Asan.M.loaded_segments (0x65a4c : word) = Some W_659fc.
Proof. vm_refl. Qed.
Lemma D_659fc : decode_any W_659fc = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a00 : bv 32 := 0x03913c23.
Lemma F_65a00 : fetch_word Asan.M.loaded_segments (0x65a50 : word) = Some W_65a00.
Proof. vm_refl. Qed.
Lemma D_65a00 : decode_any W_65a00 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a04 : bv 32 := 0x03a13823.
Lemma F_65a04 : fetch_word Asan.M.loaded_segments (0x65a54 : word) = Some W_65a04.
Proof. vm_refl. Qed.
Lemma D_65a04 : decode_any W_65a04 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a08 : bv 32 := 0x03b13423.
Lemma F_65a08 : fetch_word Asan.M.loaded_segments (0x65a58 : word) = Some W_65a08.
Proof. vm_refl. Qed.
Lemma D_65a08 : decode_any W_65a08 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a0c : bv 32 := 0x00058493.
Lemma F_65a0c : fetch_word Asan.M.loaded_segments (0x65a5c : word) = Some W_65a0c.
Proof. vm_refl. Qed.
Lemma D_65a0c : decode_any W_65a0c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a10 : bv 32 := 0x00050c93.
Lemma F_65a10 : fetch_word Asan.M.loaded_segments (0x65a60 : word) = Some W_65a10.
Proof. vm_refl. Qed.
Lemma D_65a10 : decode_any W_65a10 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a14 : bv 32 := 0x42c260ef.
Lemma F_65a14 : fetch_word Asan.M.loaded_segments (0x65a64 : word) = Some W_65a14.
Proof. vm_refl. Qed.
Lemma D_65a14 : decode_any W_65a14 = Some (Jal 1 156716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a18 : bv 32 := 0x26050463.
Lemma F_65a18 : fetch_word Asan.M.loaded_segments (0x65a68 : word) = Some W_65a18.
Proof. vm_refl. Qed.
Lemma D_65a18 : decode_any W_65a18 = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a1c : bv 32 := 0x00050913.
Lemma F_65a1c : fetch_word Asan.M.loaded_segments (0x65a6c : word) = Some W_65a1c.
Proof. vm_refl. Qed.
Lemma D_65a1c : decode_any W_65a1c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a20 : bv 32 := 0x5e4260ef.
Lemma F_65a20 : fetch_word Asan.M.loaded_segments (0x65a70 : word) = Some W_65a20.
Proof. vm_refl. Qed.
Lemma D_65a20 : decode_any W_65a20 = Some (Jal 1 157156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a24 : bv 32 := 0x00050993.
Lemma F_65a24 : fetch_word Asan.M.loaded_segments (0x65a74 : word) = Some W_65a24.
Proof. vm_refl. Qed.
Lemma D_65a24 : decode_any W_65a24 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a28 : bv 32 := 0x00090513.
Lemma F_65a28 : fetch_word Asan.M.loaded_segments (0x65a78 : word) = Some W_65a28.
Proof. vm_refl. Qed.
Lemma D_65a28 : decode_any W_65a28 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a2c : bv 32 := 0x630260ef.
Lemma F_65a2c : fetch_word Asan.M.loaded_segments (0x65a7c : word) = Some W_65a2c.
Proof. vm_refl. Qed.
Lemma D_65a2c : decode_any W_65a2c = Some (Jal 1 157232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a30 : bv 32 := 0x2499e863.
Lemma F_65a30 : fetch_word Asan.M.loaded_segments (0x65a80 : word) = Some W_65a30.
Proof. vm_refl. Qed.
Lemma D_65a30 : decode_any W_65a30 = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a34 : bv 32 := 0x00050913.
Lemma F_65a34 : fetch_word Asan.M.loaded_segments (0x65a84 : word) = Some W_65a34.
Proof. vm_refl. Qed.
Lemma D_65a34 : decode_any W_65a34 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a38 : bv 32 := 0x24a4e463.
Lemma F_65a38 : fetch_word Asan.M.loaded_segments (0x65a88 : word) = Some W_65a38.
Proof. vm_refl. Qed.
Lemma D_65a38 : decode_any W_65a38 = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a3c : bv 32 := 0x00000d13.
Lemma F_65a3c : fetch_word Asan.M.loaded_segments (0x65a8c : word) = Some W_65a3c.
Proof. vm_refl. Qed.
Lemma D_65a3c : decode_any W_65a3c = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a40 : bv 32 := 0x00001437.
Lemma F_65a40 : fetch_word Asan.M.loaded_segments (0x65a90 : word) = Some W_65a40.
Proof. vm_refl. Qed.
Lemma D_65a40 : decode_any W_65a40 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a44 : bv 32 := 0x000fb517.
Lemma F_65a44 : fetch_word Asan.M.loaded_segments (0x65a94 : word) = Some W_65a44.
Proof. vm_refl. Qed.
Lemma D_65a44 : decode_any W_65a44 = Some (Auipc 10 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a48 : bv 32 := 0x000fb597.
Lemma F_65a48 : fetch_word Asan.M.loaded_segments (0x65a98 : word) = Some W_65a48.
Proof. vm_refl. Qed.
Lemma D_65a48 : decode_any W_65a48 = Some (Auipc 11 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a4c : bv 32 := 0x000fb617.
Lemma F_65a4c : fetch_word Asan.M.loaded_segments (0x65a9c : word) = Some W_65a4c.
Proof. vm_refl. Qed.
Lemma D_65a4c : decode_any W_65a4c = Some (Auipc 12 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a50 : bv 32 := 0x000fb697.
Lemma F_65a50 : fetch_word Asan.M.loaded_segments (0x65aa0 : word) = Some W_65a50.
Proof. vm_refl. Qed.
Lemma D_65a50 : decode_any W_65a50 = Some (Auipc 13 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a54 : bv 32 := 0x000fb717.
Lemma F_65a54 : fetch_word Asan.M.loaded_segments (0x65aa4 : word) = Some W_65a54.
Proof. vm_refl. Qed.
Lemma D_65a54 : decode_any W_65a54 = Some (Auipc 14 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a58 : bv 32 := 0xfffab797.
Lemma F_65a58 : fetch_word Asan.M.loaded_segments (0x65aa8 : word) = Some W_65a58.
Proof. vm_refl. Qed.
Lemma D_65a58 : decode_any W_65a58 = Some (Auipc 15 1048491, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a5c : bv 32 := 0x008c8433.
Lemma F_65a5c : fetch_word Asan.M.loaded_segments (0x65aac : word) = Some W_65a5c.
Proof. vm_refl. Qed.
Lemma D_65a5c : decode_any W_65a5c = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a60 : bv 32 := 0x18453b03.
Lemma F_65a60 : fetch_word Asan.M.loaded_segments (0x65ab0 : word) = Some W_65a60.
Proof. vm_refl. Qed.
Lemma D_65a60 : decode_any W_65a60 = Some (Load SZ8 true 22 10 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a64 : bv 32 := 0x1885b503.
Lemma F_65a64 : fetch_word Asan.M.loaded_segments (0x65ab4 : word) = Some W_65a64.
Proof. vm_refl. Qed.
Lemma D_65a64 : decode_any W_65a64 = Some (Load SZ8 true 10 11 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a68 : bv 32 := 0x00a13c23.
Lemma F_65a68 : fetch_word Asan.M.loaded_segments (0x65ab8 : word) = Some W_65a68.
Proof. vm_refl. Qed.
Lemma D_65a68 : decode_any W_65a68 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a6c : bv 32 := 0x18c63503.
Lemma F_65a6c : fetch_word Asan.M.loaded_segments (0x65abc : word) = Some W_65a6c.
Proof. vm_refl. Qed.
Lemma D_65a6c : decode_any W_65a6c = Some (Load SZ8 true 10 12 396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a70 : bv 32 := 0x00a13823.
Lemma F_65a70 : fetch_word Asan.M.loaded_segments (0x65ac0 : word) = Some W_65a70.
Proof. vm_refl. Qed.
Lemma D_65a70 : decode_any W_65a70 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a74 : bv 32 := 0x1906b503.
Lemma F_65a74 : fetch_word Asan.M.loaded_segments (0x65ac4 : word) = Some W_65a74.
Proof. vm_refl. Qed.
Lemma D_65a74 : decode_any W_65a74 = Some (Load SZ8 true 10 13 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a78 : bv 32 := 0x00a13423.
Lemma F_65a78 : fetch_word Asan.M.loaded_segments (0x65ac8 : word) = Some W_65a78.
Proof. vm_refl. Qed.
Lemma D_65a78 : decode_any W_65a78 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a7c : bv 32 := 0x16c73503.
Lemma F_65a7c : fetch_word Asan.M.loaded_segments (0x65acc : word) = Some W_65a7c.
Proof. vm_refl. Qed.
Lemma D_65a7c : decode_any W_65a7c = Some (Load SZ8 true 10 14 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a80 : bv 32 := 0x00a13023.
Lemma F_65a80 : fetch_word Asan.M.loaded_segments (0x65ad0 : word) = Some W_65a80.
Proof. vm_refl. Qed.
Lemma D_65a80 : decode_any W_65a80 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a84 : bv 32 := 0x8f07bb83.
Lemma F_65a84 : fetch_word Asan.M.loaded_segments (0x65ad4 : word) = Some W_65a84.
Proof. vm_refl. Qed.
Lemma D_65a84 : decode_any W_65a84 = Some (Load SZ8 true 23 15 2288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a88 : bv 32 := 0x00100393.
Lemma F_65a88 : fetch_word Asan.M.loaded_segments (0x65ad8 : word) = Some W_65a88.
Proof. vm_refl. Qed.
Lemma D_65a88 : decode_any W_65a88 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a8c : bv 32 := 0x00600e13.
Lemma F_65a8c : fetch_word Asan.M.loaded_segments (0x65adc : word) = Some W_65a8c.
Proof. vm_refl. Qed.
Lemma D_65a8c : decode_any W_65a8c = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a90 : bv 32 := 0x00000a13.
Lemma F_65a90 : fetch_word Asan.M.loaded_segments (0x65ae0 : word) = Some W_65a90.
Proof. vm_refl. Qed.
Lemma D_65a90 : decode_any W_65a90 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a94 : bv 32 := 0x0100006f.
Lemma F_65a94 : fetch_word Asan.M.loaded_segments (0x65ae4 : word) = Some W_65a94.
Proof. vm_refl. Qed.
Lemma D_65a94 : decode_any W_65a94 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a98 : bv 32 := 0x001a0a13.
Lemma F_65a98 : fetch_word Asan.M.loaded_segments (0x65ae8 : word) = Some W_65a98.
Proof. vm_refl. Qed.
Lemma D_65a98 : decode_any W_65a98 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65a9c : bv 32 := 0x00b00513.
Lemma F_65a9c : fetch_word Asan.M.loaded_segments (0x65aec : word) = Some W_65a9c.
Proof. vm_refl. Qed.
Lemma D_65a9c : decode_any W_65a9c = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65aa0 : bv 32 := 0x1caa0e63.
Lemma F_65aa0 : fetch_word Asan.M.loaded_segments (0x65af0 : word) = Some W_65aa0.
Proof. vm_refl. Qed.
Lemma D_65aa0 : decode_any W_65aa0 = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65aa4 : bv 32 := 0x00000d93.
Lemma F_65aa4 : fetch_word Asan.M.loaded_segments (0x65af4 : word) = Some W_65aa4.
Proof. vm_refl. Qed.
Lemma D_65aa4 : decode_any W_65aa4 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65aa8 : bv 32 := 0x058cb503.
Lemma F_65aa8 : fetch_word Asan.M.loaded_segments (0x65af8 : word) = Some W_65aa8.
Proof. vm_refl. Qed.
Lemma D_65aa8 : decode_any W_65aa8 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65aac : bv 32 := 0x00a00593.
Lemma F_65aac : fetch_word Asan.M.loaded_segments (0x65afc : word) = Some W_65aac.
Proof. vm_refl. Qed.
Lemma D_65aac : decode_any W_65aac = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ab0 : bv 32 := 0x414585bb.
Lemma F_65ab0 : fetch_word Asan.M.loaded_segments (0x65b00 : word) = Some W_65ab0.
Proof. vm_refl. Qed.
Lemma D_65ab0 : decode_any W_65ab0 = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ab4 : bv 32 := 0x006a0a93.
Lemma F_65ab4 : fetch_word Asan.M.loaded_segments (0x65b04 : word) = Some W_65ab4.
Proof. vm_refl. Qed.
Lemma D_65ab4 : decode_any W_65ab4 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ab8 : bv 32 := 0xfff00613.
Lemma F_65ab8 : fetch_word Asan.M.loaded_segments (0x65b08 : word) = Some W_65ab8.
Proof. vm_refl. Qed.
Lemma D_65ab8 : decode_any W_65ab8 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65abc : bv 32 := 0x00b615b3.
Lemma F_65abc : fetch_word Asan.M.loaded_segments (0x65b0c : word) = Some W_65abc.
Proof. vm_refl. Qed.
Lemma D_65abc : decode_any W_65abc = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ac0 : bv 32 := 0x3ff5f593.
Lemma F_65ac0 : fetch_word Asan.M.loaded_segments (0x65b10 : word) = Some W_65ac0.
Proof. vm_refl. Qed.
Lemma D_65ac0 : decode_any W_65ac0 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ac4 : bv 32 := 0xff150613.
Lemma F_65ac4 : fetch_word Asan.M.loaded_segments (0x65b14 : word) = Some W_65ac4.
Proof. vm_refl. Qed.
Lemma D_65ac4 : decode_any W_65ac4 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ac8 : bv 32 := 0x414509b3.
Lemma F_65ac8 : fetch_word Asan.M.loaded_segments (0x65b18 : word) = Some W_65ac8.
Proof. vm_refl. Qed.
Lemma D_65ac8 : decode_any W_65ac8 = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65acc : bv 32 := 0x00c59c33.
Lemma F_65acc : fetch_word Asan.M.loaded_segments (0x65b1c : word) = Some W_65acc.
Proof. vm_refl. Qed.
Lemma D_65acc : decode_any W_65acc = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ad0 : bv 32 := 0xffa98993.
Lemma F_65ad0 : fetch_word Asan.M.loaded_segments (0x65b20 : word) = Some W_65ad0.
Proof. vm_refl. Qed.
Lemma D_65ad0 : decode_any W_65ad0 = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ad4 : bv 32 := 0x01840c33.
Lemma F_65ad4 : fetch_word Asan.M.loaded_segments (0x65b24 : word) = Some W_65ad4.
Proof. vm_refl. Qed.
Lemma D_65ad4 : decode_any W_65ad4 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ad8 : bv 32 := 0x04000513.
Lemma F_65ad8 : fetch_word Asan.M.loaded_segments (0x65b28 : word) = Some W_65ad8.
Proof. vm_refl. Qed.
Lemma D_65ad8 : decode_any W_65ad8 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65adc : bv 32 := 0x01451533.
Lemma F_65adc : fetch_word Asan.M.loaded_segments (0x65b2c : word) = Some W_65adc.
Proof. vm_refl. Qed.
Lemma D_65adc : decode_any W_65adc = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ae0 : bv 32 := 0x02a13023.
Lemma F_65ae0 : fetch_word Asan.M.loaded_segments (0x65b30 : word) = Some W_65ae0.
Proof. vm_refl. Qed.
Lemma D_65ae0 : decode_any W_65ae0 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ae4 : bv 32 := 0x0240006f.
Lemma F_65ae4 : fetch_word Asan.M.loaded_segments (0x65b34 : word) = Some W_65ae4.
Proof. vm_refl. Qed.
Lemma D_65ae4 : decode_any W_65ae4 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65afc : bv 32 := 0x001d8d93.
Lemma F_65afc : fetch_word Asan.M.loaded_segments (0x65b4c : word) = Some W_65afc.
Proof. vm_refl. Qed.
Lemma D_65afc : decode_any W_65afc = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b00 : bv 32 := 0x013dd533.
Lemma F_65b00 : fetch_word Asan.M.loaded_segments (0x65b50 : word) = Some W_65b00.
Proof. vm_refl. Qed.
Lemma D_65b00 : decode_any W_65b00 = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b04 : bv 32 := 0xf8051ae3.
Lemma F_65b04 : fetch_word Asan.M.loaded_segments (0x65b54 : word) = Some W_65b04.
Proof. vm_refl. Qed.
Lemma D_65b04 : decode_any W_65b04 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b08 : bv 32 := 0x01bc05b3.
Lemma F_65b08 : fetch_word Asan.M.loaded_segments (0x65b58 : word) = Some W_65b08.
Proof. vm_refl. Qed.
Lemma D_65b08 : decode_any W_65b08 = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b0c : bv 32 := 0x0005c503.
Lemma F_65b0c : fetch_word Asan.M.loaded_segments (0x65b5c : word) = Some W_65b0c.
Proof. vm_refl. Qed.
Lemma D_65b0c : decode_any W_65b0c = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b10 : bv 32 := 0xfe0506e3.
Lemma F_65b10 : fetch_word Asan.M.loaded_segments (0x65b60 : word) = Some W_65b10.
Proof. vm_refl. Qed.
Lemma D_65b10 : decode_any W_65b10 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b14 : bv 32 := 0x058cb503.
Lemma F_65b14 : fetch_word Asan.M.loaded_segments (0x65b64 : word) = Some W_65b14.
Proof. vm_refl. Qed.
Lemma D_65b14 : decode_any W_65b14 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b18 : bv 32 := 0xffb50613.
Lemma F_65b18 : fetch_word Asan.M.loaded_segments (0x65b68 : word) = Some W_65b18.
Proof. vm_refl. Qed.
Lemma D_65b18 : decode_any W_65b18 = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b1c : bv 32 := 0x00aa1533.
Lemma F_65b1c : fetch_word Asan.M.loaded_segments (0x65b6c : word) = Some W_65b1c.
Proof. vm_refl. Qed.
Lemma D_65b1c : decode_any W_65b1c = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b20 : bv 32 := 0x00c39633.
Lemma F_65b20 : fetch_word Asan.M.loaded_segments (0x65b70 : word) = Some W_65b20.
Proof. vm_refl. Qed.
Lemma D_65b20 : decode_any W_65b20 = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b24 : bv 32 := 0x00a40533.
Lemma F_65b24 : fetch_word Asan.M.loaded_segments (0x65b74 : word) = Some W_65b24.
Proof. vm_refl. Qed.
Lemma D_65b24 : decode_any W_65b24 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b28 : bv 32 := 0x00c50533.
Lemma F_65b28 : fetch_word Asan.M.loaded_segments (0x65b78 : word) = Some W_65b28.
Proof. vm_refl. Qed.
Lemma D_65b28 : decode_any W_65b28 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b2c : bv 32 := 0x015d9633.
Lemma F_65b2c : fetch_word Asan.M.loaded_segments (0x65b7c : word) = Some W_65b2c.
Proof. vm_refl. Qed.
Lemma D_65b2c : decode_any W_65b2c = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b30 : bv 32 := 0x00c50533.
Lemma F_65b30 : fetch_word Asan.M.loaded_segments (0x65b80 : word) = Some W_65b30.
Proof. vm_refl. Qed.
Lemma D_65b30 : decode_any W_65b30 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b34 : bv 32 := 0x01853603.
Lemma F_65b34 : fetch_word Asan.M.loaded_segments (0x65b84 : word) = Some W_65b34.
Proof. vm_refl. Qed.
Lemma D_65b34 : decode_any W_65b34 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b38 : bv 32 := 0xfcc972e3.
Lemma F_65b38 : fetch_word Asan.M.loaded_segments (0x65b88 : word) = Some W_65b38.
Proof. vm_refl. Qed.
Lemma D_65b38 : decode_any W_65b38 = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b3c : bv 32 := 0xfc9670e3.
Lemma F_65b3c : fetch_word Asan.M.loaded_segments (0x65b8c : word) = Some W_65b3c.
Proof. vm_refl. Qed.
Lemma D_65b3c : decode_any W_65b3c = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b40 : bv 32 := 0x01a58023.
Lemma F_65b40 : fetch_word Asan.M.loaded_segments (0x65b90 : word) = Some W_65b40.
Proof. vm_refl. Qed.
Lemma D_65b40 : decode_any W_65b40 = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b44 : bv 32 := 0x000b3583.
Lemma F_65b44 : fetch_word Asan.M.loaded_segments (0x65b94 : word) = Some W_65b44.
Proof. vm_refl. Qed.
Lemma D_65b44 : decode_any W_65b44 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b48 : bv 32 := 0xfff58613.
Lemma F_65b48 : fetch_word Asan.M.loaded_segments (0x65b98 : word) = Some W_65b48.
Proof. vm_refl. Qed.
Lemma D_65b48 : decode_any W_65b48 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b4c : bv 32 := 0x00c5b6b3.
Lemma F_65b4c : fetch_word Asan.M.loaded_segments (0x65b9c : word) = Some W_65b4c.
Proof. vm_refl. Qed.
Lemma D_65b4c : decode_any W_65b4c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b50 : bv 32 := 0xfff68693.
Lemma F_65b50 : fetch_word Asan.M.loaded_segments (0x65ba0 : word) = Some W_65b50.
Proof. vm_refl. Qed.
Lemma D_65b50 : decode_any W_65b50 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b54 : bv 32 := 0x00c6f6b3.
Lemma F_65b54 : fetch_word Asan.M.loaded_segments (0x65ba4 : word) = Some W_65b54.
Proof. vm_refl. Qed.
Lemma D_65b54 : decode_any W_65b54 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b58 : bv 32 := 0x02a6fc63.
Lemma F_65b58 : fetch_word Asan.M.loaded_segments (0x65ba8 : word) = Some W_65b58.
Proof. vm_refl. Qed.
Lemma D_65b58 : decode_any W_65b58 = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b5c : bv 32 := 0x01813683.
Lemma F_65b5c : fetch_word Asan.M.loaded_segments (0x65bac : word) = Some W_65b5c.
Proof. vm_refl. Qed.
Lemma D_65b5c : decode_any W_65b5c = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b60 : bv 32 := 0x0006b803.
Lemma F_65b60 : fetch_word Asan.M.loaded_segments (0x65bb0 : word) = Some W_65b60.
Proof. vm_refl. Qed.
Lemma D_65b60 : decode_any W_65b60 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b64 : bv 32 := 0x01013683.
Lemma F_65b64 : fetch_word Asan.M.loaded_segments (0x65bb4 : word) = Some W_65b64.
Proof. vm_refl. Qed.
Lemma D_65b64 : decode_any W_65b64 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b68 : bv 32 := 0x0006b683.
Lemma F_65b68 : fetch_word Asan.M.loaded_segments (0x65bb8 : word) = Some W_65b68.
Proof. vm_refl. Qed.
Lemma D_65b68 : decode_any W_65b68 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b6c : bv 32 := 0xfff80793.
Lemma F_65b6c : fetch_word Asan.M.loaded_segments (0x65bbc : word) = Some W_65b6c.
Proof. vm_refl. Qed.
Lemma D_65b6c : decode_any W_65b6c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b70 : bv 32 := 0x00a7f463.
Lemma F_65b70 : fetch_word Asan.M.loaded_segments (0x65bc0 : word) = Some W_65b70.
Proof. vm_refl. Qed.
Lemma D_65b70 : decode_any W_65b70 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b78 : bv 32 := 0x00813703.
Lemma F_65b78 : fetch_word Asan.M.loaded_segments (0x65bc8 : word) = Some W_65b78.
Proof. vm_refl. Qed.
Lemma D_65b78 : decode_any W_65b78 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b7c : bv 32 := 0x00073283.
Lemma F_65b7c : fetch_word Asan.M.loaded_segments (0x65bcc : word) = Some W_65b7c.
Proof. vm_refl. Qed.
Lemma D_65b7c : decode_any W_65b7c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b80 : bv 32 := 0x0032d713.
Lemma F_65b80 : fetch_word Asan.M.loaded_segments (0x65bd0 : word) = Some W_65b80.
Proof. vm_refl. Qed.
Lemma D_65b80 : decode_any W_65b80 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b84 : bv 32 := 0x00b708b3.
Lemma F_65b84 : fetch_word Asan.M.loaded_segments (0x65bd4 : word) = Some W_65b84.
Proof. vm_refl. Qed.
Lemma D_65b84 : decode_any W_65b84 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b88 : bv 32 := 0x02a2e863.
Lemma F_65b88 : fetch_word Asan.M.loaded_segments (0x65bd8 : word) = Some W_65b88.
Proof. vm_refl. Qed.
Lemma D_65b88 : decode_any W_65b88 = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b8c : bv 32 := 0x02a8f663.
Lemma F_65b8c : fetch_word Asan.M.loaded_segments (0x65bdc : word) = Some W_65b8c.
Proof. vm_refl. Qed.
Lemma D_65b8c : decode_any W_65b8c = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b90 : bv 32 := 0xf54e6ce3.
Lemma F_65b90 : fetch_word Asan.M.loaded_segments (0x65be0 : word) = Some W_65b90.
Proof. vm_refl. Qed.
Lemma D_65b90 : decode_any W_65b90 = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b94 : bv 32 := 0x00355513.
Lemma F_65b94 : fetch_word Asan.M.loaded_segments (0x65be4 : word) = Some W_65b94.
Proof. vm_refl. Qed.
Lemma D_65b94 : decode_any W_65b94 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b98 : bv 32 := 0x00a585b3.
Lemma F_65b98 : fetch_word Asan.M.loaded_segments (0x65be8 : word) = Some W_65b98.
Proof. vm_refl. Qed.
Lemma D_65b98 : decode_any W_65b98 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65b9c : bv 32 := 0x00100513.
Lemma F_65b9c : fetch_word Asan.M.loaded_segments (0x65bec : word) = Some W_65b9c.
Proof. vm_refl. Qed.
Lemma D_65b9c : decode_any W_65b9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ba0 : bv 32 := 0x0175b023.
Lemma F_65ba0 : fetch_word Asan.M.loaded_segments (0x65bf0 : word) = Some W_65ba0.
Proof. vm_refl. Qed.
Lemma D_65ba0 : decode_any W_65ba0 = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ba4 : bv 32 := 0x01455633.
Lemma F_65ba4 : fetch_word Asan.M.loaded_segments (0x65bf4 : word) = Some W_65ba4.
Proof. vm_refl. Qed.
Lemma D_65ba4 : decode_any W_65ba4 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ba8 : bv 32 := 0x00858593.
Lemma F_65ba8 : fetch_word Asan.M.loaded_segments (0x65bf8 : word) = Some W_65ba8.
Proof. vm_refl. Qed.
Lemma D_65ba8 : decode_any W_65ba8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65bac : bv 32 := 0x00150513.
Lemma F_65bac : fetch_word Asan.M.loaded_segments (0x65bfc : word) = Some W_65bac.
Proof. vm_refl. Qed.
Lemma D_65bac : decode_any W_65bac = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65bb0 : bv 32 := 0xfe0608e3.
Lemma F_65bb0 : fetch_word Asan.M.loaded_segments (0x65c00 : word) = Some W_65bb0.
Proof. vm_refl. Qed.
Lemma D_65bb0 : decode_any W_65bb0 = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65bb4 : bv 32 := 0xf49ff06f.
Lemma F_65bb4 : fetch_word Asan.M.loaded_segments (0x65c04 : word) = Some W_65bb4.
Proof. vm_refl. Qed.
Lemma D_65bb4 : decode_any W_65bb4 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c7c : bv 32 := 0x060c8023.
Lemma F_65c7c : fetch_word Asan.M.loaded_segments (0x65ccc : word) = Some W_65c7c.
Proof. vm_refl. Qed.
Lemma D_65c7c : decode_any W_65c7c = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c80 : bv 32 := 0x08813083.
Lemma F_65c80 : fetch_word Asan.M.loaded_segments (0x65cd0 : word) = Some W_65c80.
Proof. vm_refl. Qed.
Lemma D_65c80 : decode_any W_65c80 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c84 : bv 32 := 0x08013403.
Lemma F_65c84 : fetch_word Asan.M.loaded_segments (0x65cd4 : word) = Some W_65c84.
Proof. vm_refl. Qed.
Lemma D_65c84 : decode_any W_65c84 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c88 : bv 32 := 0x07813483.
Lemma F_65c88 : fetch_word Asan.M.loaded_segments (0x65cd8 : word) = Some W_65c88.
Proof. vm_refl. Qed.
Lemma D_65c88 : decode_any W_65c88 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c8c : bv 32 := 0x07013903.
Lemma F_65c8c : fetch_word Asan.M.loaded_segments (0x65cdc : word) = Some W_65c8c.
Proof. vm_refl. Qed.
Lemma D_65c8c : decode_any W_65c8c = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c90 : bv 32 := 0x06813983.
Lemma F_65c90 : fetch_word Asan.M.loaded_segments (0x65ce0 : word) = Some W_65c90.
Proof. vm_refl. Qed.
Lemma D_65c90 : decode_any W_65c90 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c94 : bv 32 := 0x06013a03.
Lemma F_65c94 : fetch_word Asan.M.loaded_segments (0x65ce4 : word) = Some W_65c94.
Proof. vm_refl. Qed.
Lemma D_65c94 : decode_any W_65c94 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c98 : bv 32 := 0x05813a83.
Lemma F_65c98 : fetch_word Asan.M.loaded_segments (0x65ce8 : word) = Some W_65c98.
Proof. vm_refl. Qed.
Lemma D_65c98 : decode_any W_65c98 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c9c : bv 32 := 0x05013b03.
Lemma F_65c9c : fetch_word Asan.M.loaded_segments (0x65cec : word) = Some W_65c9c.
Proof. vm_refl. Qed.
Lemma D_65c9c : decode_any W_65c9c = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ca0 : bv 32 := 0x04813b83.
Lemma F_65ca0 : fetch_word Asan.M.loaded_segments (0x65cf0 : word) = Some W_65ca0.
Proof. vm_refl. Qed.
Lemma D_65ca0 : decode_any W_65ca0 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ca4 : bv 32 := 0x04013c03.
Lemma F_65ca4 : fetch_word Asan.M.loaded_segments (0x65cf4 : word) = Some W_65ca4.
Proof. vm_refl. Qed.
Lemma D_65ca4 : decode_any W_65ca4 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ca8 : bv 32 := 0x03813c83.
Lemma F_65ca8 : fetch_word Asan.M.loaded_segments (0x65cf8 : word) = Some W_65ca8.
Proof. vm_refl. Qed.
Lemma D_65ca8 : decode_any W_65ca8 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cac : bv 32 := 0x03013d03.
Lemma F_65cac : fetch_word Asan.M.loaded_segments (0x65cfc : word) = Some W_65cac.
Proof. vm_refl. Qed.
Lemma D_65cac : decode_any W_65cac = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cb0 : bv 32 := 0x02813d83.
Lemma F_65cb0 : fetch_word Asan.M.loaded_segments (0x65d00 : word) = Some W_65cb0.
Proof. vm_refl. Qed.
Lemma D_65cb0 : decode_any W_65cb0 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cb4 : bv 32 := 0x09010113.
Lemma F_65cb4 : fetch_word Asan.M.loaded_segments (0x65d04 : word) = Some W_65cb4.
Proof. vm_refl. Qed.
Lemma D_65cb4 : decode_any W_65cb4 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cb8 : bv 32 := 0x00008067.
Lemma F_65cb8 : fetch_word Asan.M.loaded_segments (0x65d08 : word) = Some W_65cb8.
Proof. vm_refl. Qed.
Lemma D_65cb8 : decode_any W_65cb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cbc : bv 32 := 0x00100593.
Lemma F_65cbc : fetch_word Asan.M.loaded_segments (0x65d0c : word) = Some W_65cbc.
Proof. vm_refl. Qed.
Lemma D_65cbc : decode_any W_65cbc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cc0 : bv 32 := 0x06b50023.
Lemma F_65cc0 : fetch_word Asan.M.loaded_segments (0x65d10 : word) = Some W_65cc0.
Proof. vm_refl. Qed.
Lemma D_65cc0 : decode_any W_65cc0 = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cc4 : bv 32 := 0x00008067.
Lemma F_65cc4 : fetch_word Asan.M.loaded_segments (0x65d14 : word) = Some W_65cc4.
Proof. vm_refl. Qed.
Lemma D_65cc4 : decode_any W_65cc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e20 : bv 32 := 0xfe010113.
Lemma F_65e20 : fetch_word Asan.M.loaded_segments (0x65e70 : word) = Some W_65e20.
Proof. vm_refl. Qed.
Lemma D_65e20 : decode_any W_65e20 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e24 : bv 32 := 0x00113c23.
Lemma F_65e24 : fetch_word Asan.M.loaded_segments (0x65e74 : word) = Some W_65e24.
Proof. vm_refl. Qed.
Lemma D_65e24 : decode_any W_65e24 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e28 : bv 32 := 0x00813823.
Lemma F_65e28 : fetch_word Asan.M.loaded_segments (0x65e78 : word) = Some W_65e28.
Proof. vm_refl. Qed.
Lemma D_65e28 : decode_any W_65e28 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e2c : bv 32 := 0x00913423.
Lemma F_65e2c : fetch_word Asan.M.loaded_segments (0x65e7c : word) = Some W_65e2c.
Proof. vm_refl. Qed.
Lemma D_65e2c : decode_any W_65e2c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e30 : bv 32 := 0x01213023.
Lemma F_65e30 : fetch_word Asan.M.loaded_segments (0x65e80 : word) = Some W_65e30.
Proof. vm_refl. Qed.
Lemma D_65e30 : decode_any W_65e30 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e34 : bv 32 := 0x02010413.
Lemma F_65e34 : fetch_word Asan.M.loaded_segments (0x65e84 : word) = Some W_65e34.
Proof. vm_refl. Qed.
Lemma D_65e34 : decode_any W_65e34 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e38 : bv 32 := 0x000fc517.
Lemma F_65e38 : fetch_word Asan.M.loaded_segments (0x65e88 : word) = Some W_65e38.
Proof. vm_refl. Qed.
Lemma D_65e38 : decode_any W_65e38 = Some (Auipc 10 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e3c : bv 32 := 0xbb050513.
Lemma F_65e3c : fetch_word Asan.M.loaded_segments (0x65e8c : word) = Some W_65e3c.
Proof. vm_refl. Qed.
Lemma D_65e3c : decode_any W_65e3c = Some (OpImm ALU_ADD 10 10 2992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e40 : bv 32 := 0x30d050ef.
Lemma F_65e40 : fetch_word Asan.M.loaded_segments (0x65e90 : word) = Some W_65e40.
Proof. vm_refl. Qed.
Lemma D_65e40 : decode_any W_65e40 = Some (Jal 1 23308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e44 : bv 32 := 0x00053483.
Lemma F_65e44 : fetch_word Asan.M.loaded_segments (0x65e94 : word) = Some W_65e44.
Proof. vm_refl. Qed.
Lemma D_65e44 : decode_any W_65e44 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e48 : bv 32 := 0x08048063.
Lemma F_65e48 : fetch_word Asan.M.loaded_segments (0x65e98 : word) = Some W_65e48.
Proof. vm_refl. Qed.
Lemma D_65e48 : decode_any W_65e48 = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e4c : bv 32 := 0x0604c503.
Lemma F_65e4c : fetch_word Asan.M.loaded_segments (0x65e9c : word) = Some W_65e4c.
Proof. vm_refl. Qed.
Lemma D_65e4c : decode_any W_65e4c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e50 : bv 32 := 0x0584b903.
Lemma F_65e50 : fetch_word Asan.M.loaded_segments (0x65ea0 : word) = Some W_65e50.
Proof. vm_refl. Qed.
Lemma D_65e50 : decode_any W_65e50 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e54 : bv 32 := 0x00050863.
Lemma F_65e54 : fetch_word Asan.M.loaded_segments (0x65ea4 : word) = Some W_65e54.
Proof. vm_refl. Qed.
Lemma D_65e54 : decode_any W_65e54 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e58 : bv 32 := 0x00048513.
Lemma F_65e58 : fetch_word Asan.M.loaded_segments (0x65ea8 : word) = Some W_65e58.
Proof. vm_refl. Qed.
Lemma D_65e58 : decode_any W_65e58 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e5c : bv 32 := 0x00040593.
Lemma F_65e5c : fetch_word Asan.M.loaded_segments (0x65eac : word) = Some W_65e5c.
Proof. vm_refl. Qed.
Lemma D_65e5c : decode_any W_65e5c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e60 : bv 32 := 0xb75ff0ef.
Lemma F_65e60 : fetch_word Asan.M.loaded_segments (0x65eb0 : word) = Some W_65e60.
Proof. vm_refl. Qed.
Lemma D_65e60 : decode_any W_65e60 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e64 : bv 32 := 0xffa90593.
Lemma F_65e64 : fetch_word Asan.M.loaded_segments (0x65eb4 : word) = Some W_65e64.
Proof. vm_refl. Qed.
Lemma D_65e64 : decode_any W_65e64 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e68 : bv 32 := 0x00100513.
Lemma F_65e68 : fetch_word Asan.M.loaded_segments (0x65eb8 : word) = Some W_65e68.
Proof. vm_refl. Qed.
Lemma D_65e68 : decode_any W_65e68 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e6c : bv 32 := 0x00b51533.
Lemma F_65e6c : fetch_word Asan.M.loaded_segments (0x65ebc : word) = Some W_65e6c.
Proof. vm_refl. Qed.
Lemma D_65e6c : decode_any W_65e6c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e70 : bv 32 := 0x0005061b.
Lemma F_65e70 : fetch_word Asan.M.loaded_segments (0x65ec0 : word) = Some W_65e70.
Proof. vm_refl. Qed.
Lemma D_65e70 : decode_any W_65e70 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e74 : bv 32 := 0x06c05a63.
Lemma F_65e74 : fetch_word Asan.M.loaded_segments (0x65ec4 : word) = Some W_65e74.
Proof. vm_refl. Qed.
Lemma D_65e74 : decode_any W_65e74 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e78 : bv 32 := 0x000016b7.
Lemma F_65e78 : fetch_word Asan.M.loaded_segments (0x65ec8 : word) = Some W_65e78.
Proof. vm_refl. Qed.
Lemma D_65e78 : decode_any W_65e78 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e7c : bv 32 := 0xfff00713.
Lemma F_65e7c : fetch_word Asan.M.loaded_segments (0x65ecc : word) = Some W_65e7c.
Proof. vm_refl. Qed.
Lemma D_65e7c : decode_any W_65e7c = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e80 : bv 32 := 0x0004b603.
Lemma F_65e80 : fetch_word Asan.M.loaded_segments (0x65ed0 : word) = Some W_65e80.
Proof. vm_refl. Qed.
Lemma D_65e80 : decode_any W_65e80 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e84 : bv 32 := 0x00b71733.
Lemma F_65e84 : fetch_word Asan.M.loaded_segments (0x65ed4 : word) = Some W_65e84.
Proof. vm_refl. Qed.
Lemma D_65e84 : decode_any W_65e84 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e88 : bv 32 := 0xfff50793.
Lemma F_65e88 : fetch_word Asan.M.loaded_segments (0x65ed8 : word) = Some W_65e88.
Proof. vm_refl. Qed.
Lemma D_65e88 : decode_any W_65e88 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e8c : bv 32 := 0x00d485b3.
Lemma F_65e8c : fetch_word Asan.M.loaded_segments (0x65edc : word) = Some W_65e8c.
Proof. vm_refl. Qed.
Lemma D_65e8c : decode_any W_65e8c = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e90 : bv 32 := 0xfff74693.
Lemma F_65e90 : fetch_word Asan.M.loaded_segments (0x65ee0 : word) = Some W_65e90.
Proof. vm_refl. Qed.
Lemma D_65e90 : decode_any W_65e90 = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e94 : bv 32 := 0x02079793.
Lemma F_65e94 : fetch_word Asan.M.loaded_segments (0x65ee4 : word) = Some W_65e94.
Proof. vm_refl. Qed.
Lemma D_65e94 : decode_any W_65e94 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e98 : bv 32 := 0x0207d793.
Lemma F_65e98 : fetch_word Asan.M.loaded_segments (0x65ee8 : word) = Some W_65e98.
Proof. vm_refl. Qed.
Lemma D_65e98 : decode_any W_65e98 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e9c : bv 32 := 0x00f60733.
Lemma F_65e9c : fetch_word Asan.M.loaded_segments (0x65eec : word) = Some W_65e9c.
Proof. vm_refl. Qed.
Lemma D_65e9c : decode_any W_65e9c = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ea0 : bv 32 := 0x00170713.
Lemma F_65ea0 : fetch_word Asan.M.loaded_segments (0x65ef0 : word) = Some W_65ea0.
Proof. vm_refl. Qed.
Lemma D_65ea0 : decode_any W_65ea0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ea4 : bv 32 := 0x00d67833.
Lemma F_65ea4 : fetch_word Asan.M.loaded_segments (0x65ef4 : word) = Some W_65ea4.
Proof. vm_refl. Qed.
Lemma D_65ea4 : decode_any W_65ea4 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ea8 : bv 32 := 0x010587b3.
Lemma F_65ea8 : fetch_word Asan.M.loaded_segments (0x65ef8 : word) = Some W_65ea8.
Proof. vm_refl. Qed.
Lemma D_65ea8 : decode_any W_65ea8 = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65eac : bv 32 := 0x0007c883.
Lemma F_65eac : fetch_word Asan.M.loaded_segments (0x65efc : word) = Some W_65eac.
Proof. vm_refl. Qed.
Lemma D_65eac : decode_any W_65eac = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65eb0 : bv 32 := 0x06088663.
Lemma F_65eb0 : fetch_word Asan.M.loaded_segments (0x65f00 : word) = Some W_65eb0.
Proof. vm_refl. Qed.
Lemma D_65eb0 : decode_any W_65eb0 = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65eb4 : bv 32 := 0xfff5051b.
Lemma F_65eb4 : fetch_word Asan.M.loaded_segments (0x65f04 : word) = Some W_65eb4.
Proof. vm_refl. Qed.
Lemma D_65eb4 : decode_any W_65eb4 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65eb8 : bv 32 := 0x00160613.
Lemma F_65eb8 : fetch_word Asan.M.loaded_segments (0x65f08 : word) = Some W_65eb8.
Proof. vm_refl. Qed.
Lemma D_65eb8 : decode_any W_65eb8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ebc : bv 32 := 0xfe0514e3.
Lemma F_65ebc : fetch_word Asan.M.loaded_segments (0x65f0c : word) = Some W_65ebc.
Proof. vm_refl. Qed.
Lemma D_65ebc : decode_any W_65ebc = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f1c : bv 32 := 0x00160613.
Lemma F_65f1c : fetch_word Asan.M.loaded_segments (0x65f6c : word) = Some W_65f1c.
Proof. vm_refl. Qed.
Lemma D_65f1c : decode_any W_65f1c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f20 : bv 32 := 0x00100513.
Lemma F_65f20 : fetch_word Asan.M.loaded_segments (0x65f70 : word) = Some W_65f20.
Proof. vm_refl. Qed.
Lemma D_65f20 : decode_any W_65f20 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f24 : bv 32 := 0xffb90913.
Lemma F_65f24 : fetch_word Asan.M.loaded_segments (0x65f74 : word) = Some W_65f24.
Proof. vm_refl. Qed.
Lemma D_65f24 : decode_any W_65f24 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f28 : bv 32 := 0x00681813.
Lemma F_65f28 : fetch_word Asan.M.loaded_segments (0x65f78 : word) = Some W_65f28.
Proof. vm_refl. Qed.
Lemma D_65f28 : decode_any W_65f28 = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f2c : bv 32 := 0x00c4b023.
Lemma F_65f2c : fetch_word Asan.M.loaded_segments (0x65f7c : word) = Some W_65f2c.
Proof. vm_refl. Qed.
Lemma D_65f2c : decode_any W_65f2c = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f30 : bv 32 := 0x00a78023.
Lemma F_65f30 : fetch_word Asan.M.loaded_segments (0x65f80 : word) = Some W_65f30.
Proof. vm_refl. Qed.
Lemma D_65f30 : decode_any W_65f30 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f34 : bv 32 := 0x01251533.
Lemma F_65f34 : fetch_word Asan.M.loaded_segments (0x65f84 : word) = Some W_65f34.
Proof. vm_refl. Qed.
Lemma D_65f34 : decode_any W_65f34 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f38 : bv 32 := 0x00a58533.
Lemma F_65f38 : fetch_word Asan.M.loaded_segments (0x65f88 : word) = Some W_65f38.
Proof. vm_refl. Qed.
Lemma D_65f38 : decode_any W_65f38 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f3c : bv 32 := 0x010504b3.
Lemma F_65f3c : fetch_word Asan.M.loaded_segments (0x65f8c : word) = Some W_65f3c.
Proof. vm_refl. Qed.
Lemma D_65f3c : decode_any W_65f3c = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f40 : bv 32 := 0x0084bc23.
Lemma F_65f40 : fetch_word Asan.M.loaded_segments (0x65f90 : word) = Some W_65f40.
Proof. vm_refl. Qed.
Lemma D_65f40 : decode_any W_65f40 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f44 : bv 32 := 0x02f4bc23.
Lemma F_65f44 : fetch_word Asan.M.loaded_segments (0x65f94 : word) = Some W_65f44.
Proof. vm_refl. Qed.
Lemma D_65f44 : decode_any W_65f44 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f48 : bv 32 := 0x00048513.
Lemma F_65f48 : fetch_word Asan.M.loaded_segments (0x65f98 : word) = Some W_65f48.
Proof. vm_refl. Qed.
Lemma D_65f48 : decode_any W_65f48 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f4c : bv 32 := 0x1ad000ef.
Lemma F_65f4c : fetch_word Asan.M.loaded_segments (0x65f9c : word) = Some W_65f4c.
Proof. vm_refl. Qed.
Lemma D_65f4c : decode_any W_65f4c = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f50 : bv 32 := 0x00050593.
Lemma F_65f50 : fetch_word Asan.M.loaded_segments (0x65fa0 : word) = Some W_65f50.
Proof. vm_refl. Qed.
Lemma D_65f50 : decode_any W_65f50 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f54 : bv 32 := 0x00048513.
Lemma F_65f54 : fetch_word Asan.M.loaded_segments (0x65fa4 : word) = Some W_65f54.
Proof. vm_refl. Qed.
Lemma D_65f54 : decode_any W_65f54 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f58 : bv 32 := 0x00000613.
Lemma F_65f58 : fetch_word Asan.M.loaded_segments (0x65fa8 : word) = Some W_65f58.
Proof. vm_refl. Qed.
Lemma D_65f58 : decode_any W_65f58 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f5c : bv 32 := 0x0005b023.
Lemma F_65f5c : fetch_word Asan.M.loaded_segments (0x65fac : word) = Some W_65f5c.
Proof. vm_refl. Qed.
Lemma D_65f5c : decode_any W_65f5c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f60 : bv 32 := 0x01813083.
Lemma F_65f60 : fetch_word Asan.M.loaded_segments (0x65fb0 : word) = Some W_65f60.
Proof. vm_refl. Qed.
Lemma D_65f60 : decode_any W_65f60 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f64 : bv 32 := 0x01013403.
Lemma F_65f64 : fetch_word Asan.M.loaded_segments (0x65fb4 : word) = Some W_65f64.
Proof. vm_refl. Qed.
Lemma D_65f64 : decode_any W_65f64 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f68 : bv 32 := 0x00813483.
Lemma F_65f68 : fetch_word Asan.M.loaded_segments (0x65fb8 : word) = Some W_65f68.
Proof. vm_refl. Qed.
Lemma D_65f68 : decode_any W_65f68 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f6c : bv 32 := 0x00013903.
Lemma F_65f6c : fetch_word Asan.M.loaded_segments (0x65fbc : word) = Some W_65f6c.
Proof. vm_refl. Qed.
Lemma D_65f6c : decode_any W_65f6c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f70 : bv 32 := 0x02010113.
Lemma F_65f70 : fetch_word Asan.M.loaded_segments (0x65fc0 : word) = Some W_65f70.
Proof. vm_refl. Qed.
Lemma D_65f70 : decode_any W_65f70 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f74 : bv 32 := 0x00008067.
Lemma F_65f74 : fetch_word Asan.M.loaded_segments (0x65fc4 : word) = Some W_65f74.
Proof. vm_refl. Qed.
Lemma D_65f74 : decode_any W_65f74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f94 : bv 32 := 0xfe010113.
Lemma F_65f94 : fetch_word Asan.M.loaded_segments (0x65fe4 : word) = Some W_65f94.
Proof. vm_refl. Qed.
Lemma D_65f94 : decode_any W_65f94 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f98 : bv 32 := 0x00113c23.
Lemma F_65f98 : fetch_word Asan.M.loaded_segments (0x65fe8 : word) = Some W_65f98.
Proof. vm_refl. Qed.
Lemma D_65f98 : decode_any W_65f98 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65f9c : bv 32 := 0x00813823.
Lemma F_65f9c : fetch_word Asan.M.loaded_segments (0x65fec : word) = Some W_65f9c.
Proof. vm_refl. Qed.
Lemma D_65f9c : decode_any W_65f9c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fa0 : bv 32 := 0x00913423.
Lemma F_65fa0 : fetch_word Asan.M.loaded_segments (0x65ff0 : word) = Some W_65fa0.
Proof. vm_refl. Qed.
Lemma D_65fa0 : decode_any W_65fa0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fa4 : bv 32 := 0x01213023.
Lemma F_65fa4 : fetch_word Asan.M.loaded_segments (0x65ff4 : word) = Some W_65fa4.
Proof. vm_refl. Qed.
Lemma D_65fa4 : decode_any W_65fa4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fa8 : bv 32 := 0x02010413.
Lemma F_65fa8 : fetch_word Asan.M.loaded_segments (0x65ff8 : word) = Some W_65fa8.
Proof. vm_refl. Qed.
Lemma D_65fa8 : decode_any W_65fa8 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fac : bv 32 := 0x000fc517.
Lemma F_65fac : fetch_word Asan.M.loaded_segments (0x65ffc : word) = Some W_65fac.
Proof. vm_refl. Qed.
Lemma D_65fac : decode_any W_65fac = Some (Auipc 10 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fb0 : bv 32 := 0xa3c50513.
Lemma F_65fb0 : fetch_word Asan.M.loaded_segments (0x66000 : word) = Some W_65fb0.
Proof. vm_refl. Qed.
Lemma D_65fb0 : decode_any W_65fb0 = Some (OpImm ALU_ADD 10 10 2620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fb4 : bv 32 := 0x199050ef.
Lemma F_65fb4 : fetch_word Asan.M.loaded_segments (0x66004 : word) = Some W_65fb4.
Proof. vm_refl. Qed.
Lemma D_65fb4 : decode_any W_65fb4 = Some (Jal 1 22936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fb8 : bv 32 := 0x00053483.
Lemma F_65fb8 : fetch_word Asan.M.loaded_segments (0x66008 : word) = Some W_65fb8.
Proof. vm_refl. Qed.
Lemma D_65fb8 : decode_any W_65fb8 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fbc : bv 32 := 0x08048863.
Lemma F_65fbc : fetch_word Asan.M.loaded_segments (0x6600c : word) = Some W_65fbc.
Proof. vm_refl. Qed.
Lemma D_65fbc : decode_any W_65fbc = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fc0 : bv 32 := 0x0604c503.
Lemma F_65fc0 : fetch_word Asan.M.loaded_segments (0x66010 : word) = Some W_65fc0.
Proof. vm_refl. Qed.
Lemma D_65fc0 : decode_any W_65fc0 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fc4 : bv 32 := 0x0584b903.
Lemma F_65fc4 : fetch_word Asan.M.loaded_segments (0x66014 : word) = Some W_65fc4.
Proof. vm_refl. Qed.
Lemma D_65fc4 : decode_any W_65fc4 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fc8 : bv 32 := 0x00050863.
Lemma F_65fc8 : fetch_word Asan.M.loaded_segments (0x66018 : word) = Some W_65fc8.
Proof. vm_refl. Qed.
Lemma D_65fc8 : decode_any W_65fc8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fcc : bv 32 := 0x00048513.
Lemma F_65fcc : fetch_word Asan.M.loaded_segments (0x6601c : word) = Some W_65fcc.
Proof. vm_refl. Qed.
Lemma D_65fcc : decode_any W_65fcc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fd0 : bv 32 := 0x00040593.
Lemma F_65fd0 : fetch_word Asan.M.loaded_segments (0x66020 : word) = Some W_65fd0.
Proof. vm_refl. Qed.
Lemma D_65fd0 : decode_any W_65fd0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fd4 : bv 32 := 0xa01ff0ef.
Lemma F_65fd4 : fetch_word Asan.M.loaded_segments (0x66024 : word) = Some W_65fd4.
Proof. vm_refl. Qed.
Lemma D_65fd4 : decode_any W_65fd4 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fd8 : bv 32 := 0xff990593.
Lemma F_65fd8 : fetch_word Asan.M.loaded_segments (0x66028 : word) = Some W_65fd8.
Proof. vm_refl. Qed.
Lemma D_65fd8 : decode_any W_65fd8 = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fdc : bv 32 := 0x00100513.
Lemma F_65fdc : fetch_word Asan.M.loaded_segments (0x6602c : word) = Some W_65fdc.
Proof. vm_refl. Qed.
Lemma D_65fdc : decode_any W_65fdc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fe0 : bv 32 := 0x00b51533.
Lemma F_65fe0 : fetch_word Asan.M.loaded_segments (0x66030 : word) = Some W_65fe0.
Proof. vm_refl. Qed.
Lemma D_65fe0 : decode_any W_65fe0 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fe4 : bv 32 := 0x0005061b.
Lemma F_65fe4 : fetch_word Asan.M.loaded_segments (0x66034 : word) = Some W_65fe4.
Proof. vm_refl. Qed.
Lemma D_65fe4 : decode_any W_65fe4 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fe8 : bv 32 := 0x08c05263.
Lemma F_65fe8 : fetch_word Asan.M.loaded_segments (0x66038 : word) = Some W_65fe8.
Proof. vm_refl. Qed.
Lemma D_65fe8 : decode_any W_65fe8 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65fec : bv 32 := 0x000016b7.
Lemma F_65fec : fetch_word Asan.M.loaded_segments (0x6603c : word) = Some W_65fec.
Proof. vm_refl. Qed.
Lemma D_65fec : decode_any W_65fec = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ff0 : bv 32 := 0xff190613.
Lemma F_65ff0 : fetch_word Asan.M.loaded_segments (0x66040 : word) = Some W_65ff0.
Proof. vm_refl. Qed.
Lemma D_65ff0 : decode_any W_65ff0 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ff4 : bv 32 := 0x20000713.
Lemma F_65ff4 : fetch_word Asan.M.loaded_segments (0x66044 : word) = Some W_65ff4.
Proof. vm_refl. Qed.
Lemma D_65ff4 : decode_any W_65ff4 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ff8 : bv 32 := 0xfff00793.
Lemma F_65ff8 : fetch_word Asan.M.loaded_segments (0x66048 : word) = Some W_65ff8.
Proof. vm_refl. Qed.
Lemma D_65ff8 : decode_any W_65ff8 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ffc : bv 32 := 0x00c71733.
Lemma F_65ffc : fetch_word Asan.M.loaded_segments (0x6604c : word) = Some W_65ffc.
Proof. vm_refl. Qed.
Lemma D_65ffc : decode_any W_65ffc = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

