(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_649d0 : bv 32 := 0xf7010113.
Lemma F_649d0 : fetch_word AsanUbsan.M.loaded_segments (0x64a18 : word) = Some W_649d0.
Proof. vm_refl. Qed.
Lemma D_649d0 : decode_any W_649d0 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_649d4 : bv 32 := 0x08113423.
Lemma F_649d4 : fetch_word AsanUbsan.M.loaded_segments (0x64a1c : word) = Some W_649d4.
Proof. vm_refl. Qed.
Lemma D_649d4 : decode_any W_649d4 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_649d8 : bv 32 := 0x08813023.
Lemma F_649d8 : fetch_word AsanUbsan.M.loaded_segments (0x64a20 : word) = Some W_649d8.
Proof. vm_refl. Qed.
Lemma D_649d8 : decode_any W_649d8 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_649dc : bv 32 := 0x06913c23.
Lemma F_649dc : fetch_word AsanUbsan.M.loaded_segments (0x64a24 : word) = Some W_649dc.
Proof. vm_refl. Qed.
Lemma D_649dc : decode_any W_649dc = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_649e0 : bv 32 := 0x07213823.
Lemma F_649e0 : fetch_word AsanUbsan.M.loaded_segments (0x64a28 : word) = Some W_649e0.
Proof. vm_refl. Qed.
Lemma D_649e0 : decode_any W_649e0 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_649e4 : bv 32 := 0x07313423.
Lemma F_649e4 : fetch_word AsanUbsan.M.loaded_segments (0x64a2c : word) = Some W_649e4.
Proof. vm_refl. Qed.
Lemma D_649e4 : decode_any W_649e4 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_649e8 : bv 32 := 0x07413023.
Lemma F_649e8 : fetch_word AsanUbsan.M.loaded_segments (0x64a30 : word) = Some W_649e8.
Proof. vm_refl. Qed.
Lemma D_649e8 : decode_any W_649e8 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_649ec : bv 32 := 0x05513c23.
Lemma F_649ec : fetch_word AsanUbsan.M.loaded_segments (0x64a34 : word) = Some W_649ec.
Proof. vm_refl. Qed.
Lemma D_649ec : decode_any W_649ec = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f0 : bv 32 := 0x05613823.
Lemma F_649f0 : fetch_word AsanUbsan.M.loaded_segments (0x64a38 : word) = Some W_649f0.
Proof. vm_refl. Qed.
Lemma D_649f0 : decode_any W_649f0 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f4 : bv 32 := 0x05713423.
Lemma F_649f4 : fetch_word AsanUbsan.M.loaded_segments (0x64a3c : word) = Some W_649f4.
Proof. vm_refl. Qed.
Lemma D_649f4 : decode_any W_649f4 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f8 : bv 32 := 0x05813023.
Lemma F_649f8 : fetch_word AsanUbsan.M.loaded_segments (0x64a40 : word) = Some W_649f8.
Proof. vm_refl. Qed.
Lemma D_649f8 : decode_any W_649f8 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_649fc : bv 32 := 0x03913c23.
Lemma F_649fc : fetch_word AsanUbsan.M.loaded_segments (0x64a44 : word) = Some W_649fc.
Proof. vm_refl. Qed.
Lemma D_649fc : decode_any W_649fc = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a00 : bv 32 := 0x03a13823.
Lemma F_64a00 : fetch_word AsanUbsan.M.loaded_segments (0x64a48 : word) = Some W_64a00.
Proof. vm_refl. Qed.
Lemma D_64a00 : decode_any W_64a00 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a04 : bv 32 := 0x03b13423.
Lemma F_64a04 : fetch_word AsanUbsan.M.loaded_segments (0x64a4c : word) = Some W_64a04.
Proof. vm_refl. Qed.
Lemma D_64a04 : decode_any W_64a04 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a08 : bv 32 := 0x00058493.
Lemma F_64a08 : fetch_word AsanUbsan.M.loaded_segments (0x64a50 : word) = Some W_64a08.
Proof. vm_refl. Qed.
Lemma D_64a08 : decode_any W_64a08 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a0c : bv 32 := 0x00050c93.
Lemma F_64a0c : fetch_word AsanUbsan.M.loaded_segments (0x64a54 : word) = Some W_64a0c.
Proof. vm_refl. Qed.
Lemma D_64a0c : decode_any W_64a0c = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a10 : bv 32 := 0x42c260ef.
Lemma F_64a10 : fetch_word AsanUbsan.M.loaded_segments (0x64a58 : word) = Some W_64a10.
Proof. vm_refl. Qed.
Lemma D_64a10 : decode_any W_64a10 = Some (Jal 1 156716, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a14 : bv 32 := 0x26050463.
Lemma F_64a14 : fetch_word AsanUbsan.M.loaded_segments (0x64a5c : word) = Some W_64a14.
Proof. vm_refl. Qed.
Lemma D_64a14 : decode_any W_64a14 = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a18 : bv 32 := 0x00050913.
Lemma F_64a18 : fetch_word AsanUbsan.M.loaded_segments (0x64a60 : word) = Some W_64a18.
Proof. vm_refl. Qed.
Lemma D_64a18 : decode_any W_64a18 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a1c : bv 32 := 0x5e4260ef.
Lemma F_64a1c : fetch_word AsanUbsan.M.loaded_segments (0x64a64 : word) = Some W_64a1c.
Proof. vm_refl. Qed.
Lemma D_64a1c : decode_any W_64a1c = Some (Jal 1 157156, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a20 : bv 32 := 0x00050993.
Lemma F_64a20 : fetch_word AsanUbsan.M.loaded_segments (0x64a68 : word) = Some W_64a20.
Proof. vm_refl. Qed.
Lemma D_64a20 : decode_any W_64a20 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a24 : bv 32 := 0x00090513.
Lemma F_64a24 : fetch_word AsanUbsan.M.loaded_segments (0x64a6c : word) = Some W_64a24.
Proof. vm_refl. Qed.
Lemma D_64a24 : decode_any W_64a24 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a28 : bv 32 := 0x630260ef.
Lemma F_64a28 : fetch_word AsanUbsan.M.loaded_segments (0x64a70 : word) = Some W_64a28.
Proof. vm_refl. Qed.
Lemma D_64a28 : decode_any W_64a28 = Some (Jal 1 157232, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a2c : bv 32 := 0x2499e863.
Lemma F_64a2c : fetch_word AsanUbsan.M.loaded_segments (0x64a74 : word) = Some W_64a2c.
Proof. vm_refl. Qed.
Lemma D_64a2c : decode_any W_64a2c = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a30 : bv 32 := 0x00050913.
Lemma F_64a30 : fetch_word AsanUbsan.M.loaded_segments (0x64a78 : word) = Some W_64a30.
Proof. vm_refl. Qed.
Lemma D_64a30 : decode_any W_64a30 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a34 : bv 32 := 0x24a4e463.
Lemma F_64a34 : fetch_word AsanUbsan.M.loaded_segments (0x64a7c : word) = Some W_64a34.
Proof. vm_refl. Qed.
Lemma D_64a34 : decode_any W_64a34 = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a38 : bv 32 := 0x00000d13.
Lemma F_64a38 : fetch_word AsanUbsan.M.loaded_segments (0x64a80 : word) = Some W_64a38.
Proof. vm_refl. Qed.
Lemma D_64a38 : decode_any W_64a38 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a3c : bv 32 := 0x00001437.
Lemma F_64a3c : fetch_word AsanUbsan.M.loaded_segments (0x64a84 : word) = Some W_64a3c.
Proof. vm_refl. Qed.
Lemma D_64a3c : decode_any W_64a3c = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a40 : bv 32 := 0x000f0517.
Lemma F_64a40 : fetch_word AsanUbsan.M.loaded_segments (0x64a88 : word) = Some W_64a40.
Proof. vm_refl. Qed.
Lemma D_64a40 : decode_any W_64a40 = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a44 : bv 32 := 0x000f0597.
Lemma F_64a44 : fetch_word AsanUbsan.M.loaded_segments (0x64a8c : word) = Some W_64a44.
Proof. vm_refl. Qed.
Lemma D_64a44 : decode_any W_64a44 = Some (Auipc 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a48 : bv 32 := 0x000f0617.
Lemma F_64a48 : fetch_word AsanUbsan.M.loaded_segments (0x64a90 : word) = Some W_64a48.
Proof. vm_refl. Qed.
Lemma D_64a48 : decode_any W_64a48 = Some (Auipc 12 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a4c : bv 32 := 0x000f0697.
Lemma F_64a4c : fetch_word AsanUbsan.M.loaded_segments (0x64a94 : word) = Some W_64a4c.
Proof. vm_refl. Qed.
Lemma D_64a4c : decode_any W_64a4c = Some (Auipc 13 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a50 : bv 32 := 0x000f0717.
Lemma F_64a50 : fetch_word AsanUbsan.M.loaded_segments (0x64a98 : word) = Some W_64a50.
Proof. vm_refl. Qed.
Lemma D_64a50 : decode_any W_64a50 = Some (Auipc 14 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a54 : bv 32 := 0xfffac797.
Lemma F_64a54 : fetch_word AsanUbsan.M.loaded_segments (0x64a9c : word) = Some W_64a54.
Proof. vm_refl. Qed.
Lemma D_64a54 : decode_any W_64a54 = Some (Auipc 15 1048492, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a58 : bv 32 := 0x008c8433.
Lemma F_64a58 : fetch_word AsanUbsan.M.loaded_segments (0x64aa0 : word) = Some W_64a58.
Proof. vm_refl. Qed.
Lemma D_64a58 : decode_any W_64a58 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a5c : bv 32 := 0xa7853b03.
Lemma F_64a5c : fetch_word AsanUbsan.M.loaded_segments (0x64aa4 : word) = Some W_64a5c.
Proof. vm_refl. Qed.
Lemma D_64a5c : decode_any W_64a5c = Some (Load SZ8 true 22 10 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a60 : bv 32 := 0xa7c5b503.
Lemma F_64a60 : fetch_word AsanUbsan.M.loaded_segments (0x64aa8 : word) = Some W_64a60.
Proof. vm_refl. Qed.
Lemma D_64a60 : decode_any W_64a60 = Some (Load SZ8 true 10 11 2684, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a64 : bv 32 := 0x00a13c23.
Lemma F_64a64 : fetch_word AsanUbsan.M.loaded_segments (0x64aac : word) = Some W_64a64.
Proof. vm_refl. Qed.
Lemma D_64a64 : decode_any W_64a64 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a68 : bv 32 := 0xa8063503.
Lemma F_64a68 : fetch_word AsanUbsan.M.loaded_segments (0x64ab0 : word) = Some W_64a68.
Proof. vm_refl. Qed.
Lemma D_64a68 : decode_any W_64a68 = Some (Load SZ8 true 10 12 2688, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a6c : bv 32 := 0x00a13823.
Lemma F_64a6c : fetch_word AsanUbsan.M.loaded_segments (0x64ab4 : word) = Some W_64a6c.
Proof. vm_refl. Qed.
Lemma D_64a6c : decode_any W_64a6c = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a70 : bv 32 := 0xa846b503.
Lemma F_64a70 : fetch_word AsanUbsan.M.loaded_segments (0x64ab8 : word) = Some W_64a70.
Proof. vm_refl. Qed.
Lemma D_64a70 : decode_any W_64a70 = Some (Load SZ8 true 10 13 2692, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a74 : bv 32 := 0x00a13423.
Lemma F_64a74 : fetch_word AsanUbsan.M.loaded_segments (0x64abc : word) = Some W_64a74.
Proof. vm_refl. Qed.
Lemma D_64a74 : decode_any W_64a74 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a78 : bv 32 := 0xa6073503.
Lemma F_64a78 : fetch_word AsanUbsan.M.loaded_segments (0x64ac0 : word) = Some W_64a78.
Proof. vm_refl. Qed.
Lemma D_64a78 : decode_any W_64a78 = Some (Load SZ8 true 10 14 2656, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a7c : bv 32 := 0x00a13023.
Lemma F_64a7c : fetch_word AsanUbsan.M.loaded_segments (0x64ac4 : word) = Some W_64a7c.
Proof. vm_refl. Qed.
Lemma D_64a7c : decode_any W_64a7c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a80 : bv 32 := 0x90c7bb83.
Lemma F_64a80 : fetch_word AsanUbsan.M.loaded_segments (0x64ac8 : word) = Some W_64a80.
Proof. vm_refl. Qed.
Lemma D_64a80 : decode_any W_64a80 = Some (Load SZ8 true 23 15 2316, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a84 : bv 32 := 0x00100393.
Lemma F_64a84 : fetch_word AsanUbsan.M.loaded_segments (0x64acc : word) = Some W_64a84.
Proof. vm_refl. Qed.
Lemma D_64a84 : decode_any W_64a84 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a88 : bv 32 := 0x00600e13.
Lemma F_64a88 : fetch_word AsanUbsan.M.loaded_segments (0x64ad0 : word) = Some W_64a88.
Proof. vm_refl. Qed.
Lemma D_64a88 : decode_any W_64a88 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a8c : bv 32 := 0x00000a13.
Lemma F_64a8c : fetch_word AsanUbsan.M.loaded_segments (0x64ad4 : word) = Some W_64a8c.
Proof. vm_refl. Qed.
Lemma D_64a8c : decode_any W_64a8c = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a90 : bv 32 := 0x0100006f.
Lemma F_64a90 : fetch_word AsanUbsan.M.loaded_segments (0x64ad8 : word) = Some W_64a90.
Proof. vm_refl. Qed.
Lemma D_64a90 : decode_any W_64a90 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a94 : bv 32 := 0x001a0a13.
Lemma F_64a94 : fetch_word AsanUbsan.M.loaded_segments (0x64adc : word) = Some W_64a94.
Proof. vm_refl. Qed.
Lemma D_64a94 : decode_any W_64a94 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a98 : bv 32 := 0x00b00513.
Lemma F_64a98 : fetch_word AsanUbsan.M.loaded_segments (0x64ae0 : word) = Some W_64a98.
Proof. vm_refl. Qed.
Lemma D_64a98 : decode_any W_64a98 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a9c : bv 32 := 0x1caa0e63.
Lemma F_64a9c : fetch_word AsanUbsan.M.loaded_segments (0x64ae4 : word) = Some W_64a9c.
Proof. vm_refl. Qed.
Lemma D_64a9c : decode_any W_64a9c = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa0 : bv 32 := 0x00000d93.
Lemma F_64aa0 : fetch_word AsanUbsan.M.loaded_segments (0x64ae8 : word) = Some W_64aa0.
Proof. vm_refl. Qed.
Lemma D_64aa0 : decode_any W_64aa0 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa4 : bv 32 := 0x058cb503.
Lemma F_64aa4 : fetch_word AsanUbsan.M.loaded_segments (0x64aec : word) = Some W_64aa4.
Proof. vm_refl. Qed.
Lemma D_64aa4 : decode_any W_64aa4 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa8 : bv 32 := 0x00a00593.
Lemma F_64aa8 : fetch_word AsanUbsan.M.loaded_segments (0x64af0 : word) = Some W_64aa8.
Proof. vm_refl. Qed.
Lemma D_64aa8 : decode_any W_64aa8 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aac : bv 32 := 0x414585bb.
Lemma F_64aac : fetch_word AsanUbsan.M.loaded_segments (0x64af4 : word) = Some W_64aac.
Proof. vm_refl. Qed.
Lemma D_64aac : decode_any W_64aac = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab0 : bv 32 := 0x006a0a93.
Lemma F_64ab0 : fetch_word AsanUbsan.M.loaded_segments (0x64af8 : word) = Some W_64ab0.
Proof. vm_refl. Qed.
Lemma D_64ab0 : decode_any W_64ab0 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab4 : bv 32 := 0xfff00613.
Lemma F_64ab4 : fetch_word AsanUbsan.M.loaded_segments (0x64afc : word) = Some W_64ab4.
Proof. vm_refl. Qed.
Lemma D_64ab4 : decode_any W_64ab4 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab8 : bv 32 := 0x00b615b3.
Lemma F_64ab8 : fetch_word AsanUbsan.M.loaded_segments (0x64b00 : word) = Some W_64ab8.
Proof. vm_refl. Qed.
Lemma D_64ab8 : decode_any W_64ab8 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64abc : bv 32 := 0x3ff5f593.
Lemma F_64abc : fetch_word AsanUbsan.M.loaded_segments (0x64b04 : word) = Some W_64abc.
Proof. vm_refl. Qed.
Lemma D_64abc : decode_any W_64abc = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac0 : bv 32 := 0xff150613.
Lemma F_64ac0 : fetch_word AsanUbsan.M.loaded_segments (0x64b08 : word) = Some W_64ac0.
Proof. vm_refl. Qed.
Lemma D_64ac0 : decode_any W_64ac0 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac4 : bv 32 := 0x414509b3.
Lemma F_64ac4 : fetch_word AsanUbsan.M.loaded_segments (0x64b0c : word) = Some W_64ac4.
Proof. vm_refl. Qed.
Lemma D_64ac4 : decode_any W_64ac4 = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac8 : bv 32 := 0x00c59c33.
Lemma F_64ac8 : fetch_word AsanUbsan.M.loaded_segments (0x64b10 : word) = Some W_64ac8.
Proof. vm_refl. Qed.
Lemma D_64ac8 : decode_any W_64ac8 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64acc : bv 32 := 0xffa98993.
Lemma F_64acc : fetch_word AsanUbsan.M.loaded_segments (0x64b14 : word) = Some W_64acc.
Proof. vm_refl. Qed.
Lemma D_64acc : decode_any W_64acc = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad0 : bv 32 := 0x01840c33.
Lemma F_64ad0 : fetch_word AsanUbsan.M.loaded_segments (0x64b18 : word) = Some W_64ad0.
Proof. vm_refl. Qed.
Lemma D_64ad0 : decode_any W_64ad0 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad4 : bv 32 := 0x04000513.
Lemma F_64ad4 : fetch_word AsanUbsan.M.loaded_segments (0x64b1c : word) = Some W_64ad4.
Proof. vm_refl. Qed.
Lemma D_64ad4 : decode_any W_64ad4 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad8 : bv 32 := 0x01451533.
Lemma F_64ad8 : fetch_word AsanUbsan.M.loaded_segments (0x64b20 : word) = Some W_64ad8.
Proof. vm_refl. Qed.
Lemma D_64ad8 : decode_any W_64ad8 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64adc : bv 32 := 0x02a13023.
Lemma F_64adc : fetch_word AsanUbsan.M.loaded_segments (0x64b24 : word) = Some W_64adc.
Proof. vm_refl. Qed.
Lemma D_64adc : decode_any W_64adc = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae0 : bv 32 := 0x0240006f.
Lemma F_64ae0 : fetch_word AsanUbsan.M.loaded_segments (0x64b28 : word) = Some W_64ae0.
Proof. vm_refl. Qed.
Lemma D_64ae0 : decode_any W_64ae0 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_64af8 : bv 32 := 0x001d8d93.
Lemma F_64af8 : fetch_word AsanUbsan.M.loaded_segments (0x64b40 : word) = Some W_64af8.
Proof. vm_refl. Qed.
Lemma D_64af8 : decode_any W_64af8 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64afc : bv 32 := 0x013dd533.
Lemma F_64afc : fetch_word AsanUbsan.M.loaded_segments (0x64b44 : word) = Some W_64afc.
Proof. vm_refl. Qed.
Lemma D_64afc : decode_any W_64afc = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b00 : bv 32 := 0xf8051ae3.
Lemma F_64b00 : fetch_word AsanUbsan.M.loaded_segments (0x64b48 : word) = Some W_64b00.
Proof. vm_refl. Qed.
Lemma D_64b00 : decode_any W_64b00 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b04 : bv 32 := 0x01bc05b3.
Lemma F_64b04 : fetch_word AsanUbsan.M.loaded_segments (0x64b4c : word) = Some W_64b04.
Proof. vm_refl. Qed.
Lemma D_64b04 : decode_any W_64b04 = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b08 : bv 32 := 0x0005c503.
Lemma F_64b08 : fetch_word AsanUbsan.M.loaded_segments (0x64b50 : word) = Some W_64b08.
Proof. vm_refl. Qed.
Lemma D_64b08 : decode_any W_64b08 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b0c : bv 32 := 0xfe0506e3.
Lemma F_64b0c : fetch_word AsanUbsan.M.loaded_segments (0x64b54 : word) = Some W_64b0c.
Proof. vm_refl. Qed.
Lemma D_64b0c : decode_any W_64b0c = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b10 : bv 32 := 0x058cb503.
Lemma F_64b10 : fetch_word AsanUbsan.M.loaded_segments (0x64b58 : word) = Some W_64b10.
Proof. vm_refl. Qed.
Lemma D_64b10 : decode_any W_64b10 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b14 : bv 32 := 0xffb50613.
Lemma F_64b14 : fetch_word AsanUbsan.M.loaded_segments (0x64b5c : word) = Some W_64b14.
Proof. vm_refl. Qed.
Lemma D_64b14 : decode_any W_64b14 = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b18 : bv 32 := 0x00aa1533.
Lemma F_64b18 : fetch_word AsanUbsan.M.loaded_segments (0x64b60 : word) = Some W_64b18.
Proof. vm_refl. Qed.
Lemma D_64b18 : decode_any W_64b18 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b1c : bv 32 := 0x00c39633.
Lemma F_64b1c : fetch_word AsanUbsan.M.loaded_segments (0x64b64 : word) = Some W_64b1c.
Proof. vm_refl. Qed.
Lemma D_64b1c : decode_any W_64b1c = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b20 : bv 32 := 0x00a40533.
Lemma F_64b20 : fetch_word AsanUbsan.M.loaded_segments (0x64b68 : word) = Some W_64b20.
Proof. vm_refl. Qed.
Lemma D_64b20 : decode_any W_64b20 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b24 : bv 32 := 0x00c50533.
Lemma F_64b24 : fetch_word AsanUbsan.M.loaded_segments (0x64b6c : word) = Some W_64b24.
Proof. vm_refl. Qed.
Lemma D_64b24 : decode_any W_64b24 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b28 : bv 32 := 0x015d9633.
Lemma F_64b28 : fetch_word AsanUbsan.M.loaded_segments (0x64b70 : word) = Some W_64b28.
Proof. vm_refl. Qed.
Lemma D_64b28 : decode_any W_64b28 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b2c : bv 32 := 0x00c50533.
Lemma F_64b2c : fetch_word AsanUbsan.M.loaded_segments (0x64b74 : word) = Some W_64b2c.
Proof. vm_refl. Qed.
Lemma D_64b2c : decode_any W_64b2c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b30 : bv 32 := 0x01853603.
Lemma F_64b30 : fetch_word AsanUbsan.M.loaded_segments (0x64b78 : word) = Some W_64b30.
Proof. vm_refl. Qed.
Lemma D_64b30 : decode_any W_64b30 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b34 : bv 32 := 0xfcc972e3.
Lemma F_64b34 : fetch_word AsanUbsan.M.loaded_segments (0x64b7c : word) = Some W_64b34.
Proof. vm_refl. Qed.
Lemma D_64b34 : decode_any W_64b34 = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b38 : bv 32 := 0xfc9670e3.
Lemma F_64b38 : fetch_word AsanUbsan.M.loaded_segments (0x64b80 : word) = Some W_64b38.
Proof. vm_refl. Qed.
Lemma D_64b38 : decode_any W_64b38 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b3c : bv 32 := 0x01a58023.
Lemma F_64b3c : fetch_word AsanUbsan.M.loaded_segments (0x64b84 : word) = Some W_64b3c.
Proof. vm_refl. Qed.
Lemma D_64b3c : decode_any W_64b3c = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b40 : bv 32 := 0x000b3583.
Lemma F_64b40 : fetch_word AsanUbsan.M.loaded_segments (0x64b88 : word) = Some W_64b40.
Proof. vm_refl. Qed.
Lemma D_64b40 : decode_any W_64b40 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b44 : bv 32 := 0xfff58613.
Lemma F_64b44 : fetch_word AsanUbsan.M.loaded_segments (0x64b8c : word) = Some W_64b44.
Proof. vm_refl. Qed.
Lemma D_64b44 : decode_any W_64b44 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b48 : bv 32 := 0x00c5b6b3.
Lemma F_64b48 : fetch_word AsanUbsan.M.loaded_segments (0x64b90 : word) = Some W_64b48.
Proof. vm_refl. Qed.
Lemma D_64b48 : decode_any W_64b48 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b4c : bv 32 := 0xfff68693.
Lemma F_64b4c : fetch_word AsanUbsan.M.loaded_segments (0x64b94 : word) = Some W_64b4c.
Proof. vm_refl. Qed.
Lemma D_64b4c : decode_any W_64b4c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b50 : bv 32 := 0x00c6f6b3.
Lemma F_64b50 : fetch_word AsanUbsan.M.loaded_segments (0x64b98 : word) = Some W_64b50.
Proof. vm_refl. Qed.
Lemma D_64b50 : decode_any W_64b50 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b54 : bv 32 := 0x02a6fc63.
Lemma F_64b54 : fetch_word AsanUbsan.M.loaded_segments (0x64b9c : word) = Some W_64b54.
Proof. vm_refl. Qed.
Lemma D_64b54 : decode_any W_64b54 = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b58 : bv 32 := 0x01813683.
Lemma F_64b58 : fetch_word AsanUbsan.M.loaded_segments (0x64ba0 : word) = Some W_64b58.
Proof. vm_refl. Qed.
Lemma D_64b58 : decode_any W_64b58 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b5c : bv 32 := 0x0006b803.
Lemma F_64b5c : fetch_word AsanUbsan.M.loaded_segments (0x64ba4 : word) = Some W_64b5c.
Proof. vm_refl. Qed.
Lemma D_64b5c : decode_any W_64b5c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b60 : bv 32 := 0x01013683.
Lemma F_64b60 : fetch_word AsanUbsan.M.loaded_segments (0x64ba8 : word) = Some W_64b60.
Proof. vm_refl. Qed.
Lemma D_64b60 : decode_any W_64b60 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b64 : bv 32 := 0x0006b683.
Lemma F_64b64 : fetch_word AsanUbsan.M.loaded_segments (0x64bac : word) = Some W_64b64.
Proof. vm_refl. Qed.
Lemma D_64b64 : decode_any W_64b64 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b68 : bv 32 := 0xfff80793.
Lemma F_64b68 : fetch_word AsanUbsan.M.loaded_segments (0x64bb0 : word) = Some W_64b68.
Proof. vm_refl. Qed.
Lemma D_64b68 : decode_any W_64b68 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b6c : bv 32 := 0x00a7f463.
Lemma F_64b6c : fetch_word AsanUbsan.M.loaded_segments (0x64bb4 : word) = Some W_64b6c.
Proof. vm_refl. Qed.
Lemma D_64b6c : decode_any W_64b6c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b74 : bv 32 := 0x00813703.
Lemma F_64b74 : fetch_word AsanUbsan.M.loaded_segments (0x64bbc : word) = Some W_64b74.
Proof. vm_refl. Qed.
Lemma D_64b74 : decode_any W_64b74 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b78 : bv 32 := 0x00073283.
Lemma F_64b78 : fetch_word AsanUbsan.M.loaded_segments (0x64bc0 : word) = Some W_64b78.
Proof. vm_refl. Qed.
Lemma D_64b78 : decode_any W_64b78 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b7c : bv 32 := 0x0032d713.
Lemma F_64b7c : fetch_word AsanUbsan.M.loaded_segments (0x64bc4 : word) = Some W_64b7c.
Proof. vm_refl. Qed.
Lemma D_64b7c : decode_any W_64b7c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b80 : bv 32 := 0x00b708b3.
Lemma F_64b80 : fetch_word AsanUbsan.M.loaded_segments (0x64bc8 : word) = Some W_64b80.
Proof. vm_refl. Qed.
Lemma D_64b80 : decode_any W_64b80 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b84 : bv 32 := 0x02a2e863.
Lemma F_64b84 : fetch_word AsanUbsan.M.loaded_segments (0x64bcc : word) = Some W_64b84.
Proof. vm_refl. Qed.
Lemma D_64b84 : decode_any W_64b84 = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b88 : bv 32 := 0x02a8f663.
Lemma F_64b88 : fetch_word AsanUbsan.M.loaded_segments (0x64bd0 : word) = Some W_64b88.
Proof. vm_refl. Qed.
Lemma D_64b88 : decode_any W_64b88 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b8c : bv 32 := 0xf54e6ce3.
Lemma F_64b8c : fetch_word AsanUbsan.M.loaded_segments (0x64bd4 : word) = Some W_64b8c.
Proof. vm_refl. Qed.
Lemma D_64b8c : decode_any W_64b8c = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b90 : bv 32 := 0x00355513.
Lemma F_64b90 : fetch_word AsanUbsan.M.loaded_segments (0x64bd8 : word) = Some W_64b90.
Proof. vm_refl. Qed.
Lemma D_64b90 : decode_any W_64b90 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b94 : bv 32 := 0x00a585b3.
Lemma F_64b94 : fetch_word AsanUbsan.M.loaded_segments (0x64bdc : word) = Some W_64b94.
Proof. vm_refl. Qed.
Lemma D_64b94 : decode_any W_64b94 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b98 : bv 32 := 0x00100513.
Lemma F_64b98 : fetch_word AsanUbsan.M.loaded_segments (0x64be0 : word) = Some W_64b98.
Proof. vm_refl. Qed.
Lemma D_64b98 : decode_any W_64b98 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b9c : bv 32 := 0x0175b023.
Lemma F_64b9c : fetch_word AsanUbsan.M.loaded_segments (0x64be4 : word) = Some W_64b9c.
Proof. vm_refl. Qed.
Lemma D_64b9c : decode_any W_64b9c = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba0 : bv 32 := 0x01455633.
Lemma F_64ba0 : fetch_word AsanUbsan.M.loaded_segments (0x64be8 : word) = Some W_64ba0.
Proof. vm_refl. Qed.
Lemma D_64ba0 : decode_any W_64ba0 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba4 : bv 32 := 0x00858593.
Lemma F_64ba4 : fetch_word AsanUbsan.M.loaded_segments (0x64bec : word) = Some W_64ba4.
Proof. vm_refl. Qed.
Lemma D_64ba4 : decode_any W_64ba4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba8 : bv 32 := 0x00150513.
Lemma F_64ba8 : fetch_word AsanUbsan.M.loaded_segments (0x64bf0 : word) = Some W_64ba8.
Proof. vm_refl. Qed.
Lemma D_64ba8 : decode_any W_64ba8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bac : bv 32 := 0xfe0608e3.
Lemma F_64bac : fetch_word AsanUbsan.M.loaded_segments (0x64bf4 : word) = Some W_64bac.
Proof. vm_refl. Qed.
Lemma D_64bac : decode_any W_64bac = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bb0 : bv 32 := 0xf49ff06f.
Lemma F_64bb0 : fetch_word AsanUbsan.M.loaded_segments (0x64bf8 : word) = Some W_64bb0.
Proof. vm_refl. Qed.
Lemma D_64bb0 : decode_any W_64bb0 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c78 : bv 32 := 0x060c8023.
Lemma F_64c78 : fetch_word AsanUbsan.M.loaded_segments (0x64cc0 : word) = Some W_64c78.
Proof. vm_refl. Qed.
Lemma D_64c78 : decode_any W_64c78 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c7c : bv 32 := 0x08813083.
Lemma F_64c7c : fetch_word AsanUbsan.M.loaded_segments (0x64cc4 : word) = Some W_64c7c.
Proof. vm_refl. Qed.
Lemma D_64c7c : decode_any W_64c7c = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c80 : bv 32 := 0x08013403.
Lemma F_64c80 : fetch_word AsanUbsan.M.loaded_segments (0x64cc8 : word) = Some W_64c80.
Proof. vm_refl. Qed.
Lemma D_64c80 : decode_any W_64c80 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c84 : bv 32 := 0x07813483.
Lemma F_64c84 : fetch_word AsanUbsan.M.loaded_segments (0x64ccc : word) = Some W_64c84.
Proof. vm_refl. Qed.
Lemma D_64c84 : decode_any W_64c84 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c88 : bv 32 := 0x07013903.
Lemma F_64c88 : fetch_word AsanUbsan.M.loaded_segments (0x64cd0 : word) = Some W_64c88.
Proof. vm_refl. Qed.
Lemma D_64c88 : decode_any W_64c88 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c8c : bv 32 := 0x06813983.
Lemma F_64c8c : fetch_word AsanUbsan.M.loaded_segments (0x64cd4 : word) = Some W_64c8c.
Proof. vm_refl. Qed.
Lemma D_64c8c : decode_any W_64c8c = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c90 : bv 32 := 0x06013a03.
Lemma F_64c90 : fetch_word AsanUbsan.M.loaded_segments (0x64cd8 : word) = Some W_64c90.
Proof. vm_refl. Qed.
Lemma D_64c90 : decode_any W_64c90 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c94 : bv 32 := 0x05813a83.
Lemma F_64c94 : fetch_word AsanUbsan.M.loaded_segments (0x64cdc : word) = Some W_64c94.
Proof. vm_refl. Qed.
Lemma D_64c94 : decode_any W_64c94 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c98 : bv 32 := 0x05013b03.
Lemma F_64c98 : fetch_word AsanUbsan.M.loaded_segments (0x64ce0 : word) = Some W_64c98.
Proof. vm_refl. Qed.
Lemma D_64c98 : decode_any W_64c98 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c9c : bv 32 := 0x04813b83.
Lemma F_64c9c : fetch_word AsanUbsan.M.loaded_segments (0x64ce4 : word) = Some W_64c9c.
Proof. vm_refl. Qed.
Lemma D_64c9c : decode_any W_64c9c = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ca0 : bv 32 := 0x04013c03.
Lemma F_64ca0 : fetch_word AsanUbsan.M.loaded_segments (0x64ce8 : word) = Some W_64ca0.
Proof. vm_refl. Qed.
Lemma D_64ca0 : decode_any W_64ca0 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ca4 : bv 32 := 0x03813c83.
Lemma F_64ca4 : fetch_word AsanUbsan.M.loaded_segments (0x64cec : word) = Some W_64ca4.
Proof. vm_refl. Qed.
Lemma D_64ca4 : decode_any W_64ca4 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ca8 : bv 32 := 0x03013d03.
Lemma F_64ca8 : fetch_word AsanUbsan.M.loaded_segments (0x64cf0 : word) = Some W_64ca8.
Proof. vm_refl. Qed.
Lemma D_64ca8 : decode_any W_64ca8 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cac : bv 32 := 0x02813d83.
Lemma F_64cac : fetch_word AsanUbsan.M.loaded_segments (0x64cf4 : word) = Some W_64cac.
Proof. vm_refl. Qed.
Lemma D_64cac : decode_any W_64cac = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cb0 : bv 32 := 0x09010113.
Lemma F_64cb0 : fetch_word AsanUbsan.M.loaded_segments (0x64cf8 : word) = Some W_64cb0.
Proof. vm_refl. Qed.
Lemma D_64cb0 : decode_any W_64cb0 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cb4 : bv 32 := 0x00008067.
Lemma F_64cb4 : fetch_word AsanUbsan.M.loaded_segments (0x64cfc : word) = Some W_64cb4.
Proof. vm_refl. Qed.
Lemma D_64cb4 : decode_any W_64cb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cb8 : bv 32 := 0x00100593.
Lemma F_64cb8 : fetch_word AsanUbsan.M.loaded_segments (0x64d00 : word) = Some W_64cb8.
Proof. vm_refl. Qed.
Lemma D_64cb8 : decode_any W_64cb8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cbc : bv 32 := 0x06b50023.
Lemma F_64cbc : fetch_word AsanUbsan.M.loaded_segments (0x64d04 : word) = Some W_64cbc.
Proof. vm_refl. Qed.
Lemma D_64cbc : decode_any W_64cbc = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cc0 : bv 32 := 0x00008067.
Lemma F_64cc0 : fetch_word AsanUbsan.M.loaded_segments (0x64d08 : word) = Some W_64cc0.
Proof. vm_refl. Qed.
Lemma D_64cc0 : decode_any W_64cc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e1c : bv 32 := 0xfe010113.
Lemma F_64e1c : fetch_word AsanUbsan.M.loaded_segments (0x64e64 : word) = Some W_64e1c.
Proof. vm_refl. Qed.
Lemma D_64e1c : decode_any W_64e1c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e20 : bv 32 := 0x00113c23.
Lemma F_64e20 : fetch_word AsanUbsan.M.loaded_segments (0x64e68 : word) = Some W_64e20.
Proof. vm_refl. Qed.
Lemma D_64e20 : decode_any W_64e20 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e24 : bv 32 := 0x00813823.
Lemma F_64e24 : fetch_word AsanUbsan.M.loaded_segments (0x64e6c : word) = Some W_64e24.
Proof. vm_refl. Qed.
Lemma D_64e24 : decode_any W_64e24 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e28 : bv 32 := 0x00913423.
Lemma F_64e28 : fetch_word AsanUbsan.M.loaded_segments (0x64e70 : word) = Some W_64e28.
Proof. vm_refl. Qed.
Lemma D_64e28 : decode_any W_64e28 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e2c : bv 32 := 0x01213023.
Lemma F_64e2c : fetch_word AsanUbsan.M.loaded_segments (0x64e74 : word) = Some W_64e2c.
Proof. vm_refl. Qed.
Lemma D_64e2c : decode_any W_64e2c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e30 : bv 32 := 0x02010413.
Lemma F_64e30 : fetch_word AsanUbsan.M.loaded_segments (0x64e78 : word) = Some W_64e30.
Proof. vm_refl. Qed.
Lemma D_64e30 : decode_any W_64e30 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e34 : bv 32 := 0x000f0517.
Lemma F_64e34 : fetch_word AsanUbsan.M.loaded_segments (0x64e7c : word) = Some W_64e34.
Proof. vm_refl. Qed.
Lemma D_64e34 : decode_any W_64e34 = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e38 : bv 32 := 0x49450513.
Lemma F_64e38 : fetch_word AsanUbsan.M.loaded_segments (0x64e80 : word) = Some W_64e38.
Proof. vm_refl. Qed.
Lemma D_64e38 : decode_any W_64e38 = Some (OpImm ALU_ADD 10 10 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e3c : bv 32 := 0x30d050ef.
Lemma F_64e3c : fetch_word AsanUbsan.M.loaded_segments (0x64e84 : word) = Some W_64e3c.
Proof. vm_refl. Qed.
Lemma D_64e3c : decode_any W_64e3c = Some (Jal 1 23308, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e40 : bv 32 := 0x00053483.
Lemma F_64e40 : fetch_word AsanUbsan.M.loaded_segments (0x64e88 : word) = Some W_64e40.
Proof. vm_refl. Qed.
Lemma D_64e40 : decode_any W_64e40 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e44 : bv 32 := 0x08048063.
Lemma F_64e44 : fetch_word AsanUbsan.M.loaded_segments (0x64e8c : word) = Some W_64e44.
Proof. vm_refl. Qed.
Lemma D_64e44 : decode_any W_64e44 = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e48 : bv 32 := 0x0604c503.
Lemma F_64e48 : fetch_word AsanUbsan.M.loaded_segments (0x64e90 : word) = Some W_64e48.
Proof. vm_refl. Qed.
Lemma D_64e48 : decode_any W_64e48 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e4c : bv 32 := 0x0584b903.
Lemma F_64e4c : fetch_word AsanUbsan.M.loaded_segments (0x64e94 : word) = Some W_64e4c.
Proof. vm_refl. Qed.
Lemma D_64e4c : decode_any W_64e4c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e50 : bv 32 := 0x00050863.
Lemma F_64e50 : fetch_word AsanUbsan.M.loaded_segments (0x64e98 : word) = Some W_64e50.
Proof. vm_refl. Qed.
Lemma D_64e50 : decode_any W_64e50 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e54 : bv 32 := 0x00048513.
Lemma F_64e54 : fetch_word AsanUbsan.M.loaded_segments (0x64e9c : word) = Some W_64e54.
Proof. vm_refl. Qed.
Lemma D_64e54 : decode_any W_64e54 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e58 : bv 32 := 0x00040593.
Lemma F_64e58 : fetch_word AsanUbsan.M.loaded_segments (0x64ea0 : word) = Some W_64e58.
Proof. vm_refl. Qed.
Lemma D_64e58 : decode_any W_64e58 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e5c : bv 32 := 0xb75ff0ef.
Lemma F_64e5c : fetch_word AsanUbsan.M.loaded_segments (0x64ea4 : word) = Some W_64e5c.
Proof. vm_refl. Qed.
Lemma D_64e5c : decode_any W_64e5c = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e60 : bv 32 := 0xffa90593.
Lemma F_64e60 : fetch_word AsanUbsan.M.loaded_segments (0x64ea8 : word) = Some W_64e60.
Proof. vm_refl. Qed.
Lemma D_64e60 : decode_any W_64e60 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e64 : bv 32 := 0x00100513.
Lemma F_64e64 : fetch_word AsanUbsan.M.loaded_segments (0x64eac : word) = Some W_64e64.
Proof. vm_refl. Qed.
Lemma D_64e64 : decode_any W_64e64 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e68 : bv 32 := 0x00b51533.
Lemma F_64e68 : fetch_word AsanUbsan.M.loaded_segments (0x64eb0 : word) = Some W_64e68.
Proof. vm_refl. Qed.
Lemma D_64e68 : decode_any W_64e68 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e6c : bv 32 := 0x0005061b.
Lemma F_64e6c : fetch_word AsanUbsan.M.loaded_segments (0x64eb4 : word) = Some W_64e6c.
Proof. vm_refl. Qed.
Lemma D_64e6c : decode_any W_64e6c = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e70 : bv 32 := 0x06c05a63.
Lemma F_64e70 : fetch_word AsanUbsan.M.loaded_segments (0x64eb8 : word) = Some W_64e70.
Proof. vm_refl. Qed.
Lemma D_64e70 : decode_any W_64e70 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e74 : bv 32 := 0x000016b7.
Lemma F_64e74 : fetch_word AsanUbsan.M.loaded_segments (0x64ebc : word) = Some W_64e74.
Proof. vm_refl. Qed.
Lemma D_64e74 : decode_any W_64e74 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e78 : bv 32 := 0xfff00713.
Lemma F_64e78 : fetch_word AsanUbsan.M.loaded_segments (0x64ec0 : word) = Some W_64e78.
Proof. vm_refl. Qed.
Lemma D_64e78 : decode_any W_64e78 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e7c : bv 32 := 0x0004b603.
Lemma F_64e7c : fetch_word AsanUbsan.M.loaded_segments (0x64ec4 : word) = Some W_64e7c.
Proof. vm_refl. Qed.
Lemma D_64e7c : decode_any W_64e7c = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e80 : bv 32 := 0x00b71733.
Lemma F_64e80 : fetch_word AsanUbsan.M.loaded_segments (0x64ec8 : word) = Some W_64e80.
Proof. vm_refl. Qed.
Lemma D_64e80 : decode_any W_64e80 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e84 : bv 32 := 0xfff50793.
Lemma F_64e84 : fetch_word AsanUbsan.M.loaded_segments (0x64ecc : word) = Some W_64e84.
Proof. vm_refl. Qed.
Lemma D_64e84 : decode_any W_64e84 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e88 : bv 32 := 0x00d485b3.
Lemma F_64e88 : fetch_word AsanUbsan.M.loaded_segments (0x64ed0 : word) = Some W_64e88.
Proof. vm_refl. Qed.
Lemma D_64e88 : decode_any W_64e88 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e8c : bv 32 := 0xfff74693.
Lemma F_64e8c : fetch_word AsanUbsan.M.loaded_segments (0x64ed4 : word) = Some W_64e8c.
Proof. vm_refl. Qed.
Lemma D_64e8c : decode_any W_64e8c = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e90 : bv 32 := 0x02079793.
Lemma F_64e90 : fetch_word AsanUbsan.M.loaded_segments (0x64ed8 : word) = Some W_64e90.
Proof. vm_refl. Qed.
Lemma D_64e90 : decode_any W_64e90 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e94 : bv 32 := 0x0207d793.
Lemma F_64e94 : fetch_word AsanUbsan.M.loaded_segments (0x64edc : word) = Some W_64e94.
Proof. vm_refl. Qed.
Lemma D_64e94 : decode_any W_64e94 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e98 : bv 32 := 0x00f60733.
Lemma F_64e98 : fetch_word AsanUbsan.M.loaded_segments (0x64ee0 : word) = Some W_64e98.
Proof. vm_refl. Qed.
Lemma D_64e98 : decode_any W_64e98 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e9c : bv 32 := 0x00170713.
Lemma F_64e9c : fetch_word AsanUbsan.M.loaded_segments (0x64ee4 : word) = Some W_64e9c.
Proof. vm_refl. Qed.
Lemma D_64e9c : decode_any W_64e9c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea0 : bv 32 := 0x00d67833.
Lemma F_64ea0 : fetch_word AsanUbsan.M.loaded_segments (0x64ee8 : word) = Some W_64ea0.
Proof. vm_refl. Qed.
Lemma D_64ea0 : decode_any W_64ea0 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea4 : bv 32 := 0x010587b3.
Lemma F_64ea4 : fetch_word AsanUbsan.M.loaded_segments (0x64eec : word) = Some W_64ea4.
Proof. vm_refl. Qed.
Lemma D_64ea4 : decode_any W_64ea4 = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea8 : bv 32 := 0x0007c883.
Lemma F_64ea8 : fetch_word AsanUbsan.M.loaded_segments (0x64ef0 : word) = Some W_64ea8.
Proof. vm_refl. Qed.
Lemma D_64ea8 : decode_any W_64ea8 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eac : bv 32 := 0x06088663.
Lemma F_64eac : fetch_word AsanUbsan.M.loaded_segments (0x64ef4 : word) = Some W_64eac.
Proof. vm_refl. Qed.
Lemma D_64eac : decode_any W_64eac = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb0 : bv 32 := 0xfff5051b.
Lemma F_64eb0 : fetch_word AsanUbsan.M.loaded_segments (0x64ef8 : word) = Some W_64eb0.
Proof. vm_refl. Qed.
Lemma D_64eb0 : decode_any W_64eb0 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb4 : bv 32 := 0x00160613.
Lemma F_64eb4 : fetch_word AsanUbsan.M.loaded_segments (0x64efc : word) = Some W_64eb4.
Proof. vm_refl. Qed.
Lemma D_64eb4 : decode_any W_64eb4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb8 : bv 32 := 0xfe0514e3.
Lemma F_64eb8 : fetch_word AsanUbsan.M.loaded_segments (0x64f00 : word) = Some W_64eb8.
Proof. vm_refl. Qed.
Lemma D_64eb8 : decode_any W_64eb8 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f18 : bv 32 := 0x00160613.
Lemma F_64f18 : fetch_word AsanUbsan.M.loaded_segments (0x64f60 : word) = Some W_64f18.
Proof. vm_refl. Qed.
Lemma D_64f18 : decode_any W_64f18 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f1c : bv 32 := 0x00100513.
Lemma F_64f1c : fetch_word AsanUbsan.M.loaded_segments (0x64f64 : word) = Some W_64f1c.
Proof. vm_refl. Qed.
Lemma D_64f1c : decode_any W_64f1c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f20 : bv 32 := 0xffb90913.
Lemma F_64f20 : fetch_word AsanUbsan.M.loaded_segments (0x64f68 : word) = Some W_64f20.
Proof. vm_refl. Qed.
Lemma D_64f20 : decode_any W_64f20 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f24 : bv 32 := 0x00681813.
Lemma F_64f24 : fetch_word AsanUbsan.M.loaded_segments (0x64f6c : word) = Some W_64f24.
Proof. vm_refl. Qed.
Lemma D_64f24 : decode_any W_64f24 = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f28 : bv 32 := 0x00c4b023.
Lemma F_64f28 : fetch_word AsanUbsan.M.loaded_segments (0x64f70 : word) = Some W_64f28.
Proof. vm_refl. Qed.
Lemma D_64f28 : decode_any W_64f28 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f2c : bv 32 := 0x00a78023.
Lemma F_64f2c : fetch_word AsanUbsan.M.loaded_segments (0x64f74 : word) = Some W_64f2c.
Proof. vm_refl. Qed.
Lemma D_64f2c : decode_any W_64f2c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f30 : bv 32 := 0x01251533.
Lemma F_64f30 : fetch_word AsanUbsan.M.loaded_segments (0x64f78 : word) = Some W_64f30.
Proof. vm_refl. Qed.
Lemma D_64f30 : decode_any W_64f30 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f34 : bv 32 := 0x00a58533.
Lemma F_64f34 : fetch_word AsanUbsan.M.loaded_segments (0x64f7c : word) = Some W_64f34.
Proof. vm_refl. Qed.
Lemma D_64f34 : decode_any W_64f34 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f38 : bv 32 := 0x010504b3.
Lemma F_64f38 : fetch_word AsanUbsan.M.loaded_segments (0x64f80 : word) = Some W_64f38.
Proof. vm_refl. Qed.
Lemma D_64f38 : decode_any W_64f38 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f3c : bv 32 := 0x0084bc23.
Lemma F_64f3c : fetch_word AsanUbsan.M.loaded_segments (0x64f84 : word) = Some W_64f3c.
Proof. vm_refl. Qed.
Lemma D_64f3c : decode_any W_64f3c = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f40 : bv 32 := 0x02f4bc23.
Lemma F_64f40 : fetch_word AsanUbsan.M.loaded_segments (0x64f88 : word) = Some W_64f40.
Proof. vm_refl. Qed.
Lemma D_64f40 : decode_any W_64f40 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f44 : bv 32 := 0x00048513.
Lemma F_64f44 : fetch_word AsanUbsan.M.loaded_segments (0x64f8c : word) = Some W_64f44.
Proof. vm_refl. Qed.
Lemma D_64f44 : decode_any W_64f44 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f48 : bv 32 := 0x1ad000ef.
Lemma F_64f48 : fetch_word AsanUbsan.M.loaded_segments (0x64f90 : word) = Some W_64f48.
Proof. vm_refl. Qed.
Lemma D_64f48 : decode_any W_64f48 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f4c : bv 32 := 0x00050593.
Lemma F_64f4c : fetch_word AsanUbsan.M.loaded_segments (0x64f94 : word) = Some W_64f4c.
Proof. vm_refl. Qed.
Lemma D_64f4c : decode_any W_64f4c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f50 : bv 32 := 0x00048513.
Lemma F_64f50 : fetch_word AsanUbsan.M.loaded_segments (0x64f98 : word) = Some W_64f50.
Proof. vm_refl. Qed.
Lemma D_64f50 : decode_any W_64f50 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f54 : bv 32 := 0x00000613.
Lemma F_64f54 : fetch_word AsanUbsan.M.loaded_segments (0x64f9c : word) = Some W_64f54.
Proof. vm_refl. Qed.
Lemma D_64f54 : decode_any W_64f54 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f58 : bv 32 := 0x0005b023.
Lemma F_64f58 : fetch_word AsanUbsan.M.loaded_segments (0x64fa0 : word) = Some W_64f58.
Proof. vm_refl. Qed.
Lemma D_64f58 : decode_any W_64f58 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f5c : bv 32 := 0x01813083.
Lemma F_64f5c : fetch_word AsanUbsan.M.loaded_segments (0x64fa4 : word) = Some W_64f5c.
Proof. vm_refl. Qed.
Lemma D_64f5c : decode_any W_64f5c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f60 : bv 32 := 0x01013403.
Lemma F_64f60 : fetch_word AsanUbsan.M.loaded_segments (0x64fa8 : word) = Some W_64f60.
Proof. vm_refl. Qed.
Lemma D_64f60 : decode_any W_64f60 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f64 : bv 32 := 0x00813483.
Lemma F_64f64 : fetch_word AsanUbsan.M.loaded_segments (0x64fac : word) = Some W_64f64.
Proof. vm_refl. Qed.
Lemma D_64f64 : decode_any W_64f64 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f68 : bv 32 := 0x00013903.
Lemma F_64f68 : fetch_word AsanUbsan.M.loaded_segments (0x64fb0 : word) = Some W_64f68.
Proof. vm_refl. Qed.
Lemma D_64f68 : decode_any W_64f68 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f6c : bv 32 := 0x02010113.
Lemma F_64f6c : fetch_word AsanUbsan.M.loaded_segments (0x64fb4 : word) = Some W_64f6c.
Proof. vm_refl. Qed.
Lemma D_64f6c : decode_any W_64f6c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f70 : bv 32 := 0x00008067.
Lemma F_64f70 : fetch_word AsanUbsan.M.loaded_segments (0x64fb8 : word) = Some W_64f70.
Proof. vm_refl. Qed.
Lemma D_64f70 : decode_any W_64f70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f90 : bv 32 := 0xfe010113.
Lemma F_64f90 : fetch_word AsanUbsan.M.loaded_segments (0x64fd8 : word) = Some W_64f90.
Proof. vm_refl. Qed.
Lemma D_64f90 : decode_any W_64f90 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f94 : bv 32 := 0x00113c23.
Lemma F_64f94 : fetch_word AsanUbsan.M.loaded_segments (0x64fdc : word) = Some W_64f94.
Proof. vm_refl. Qed.
Lemma D_64f94 : decode_any W_64f94 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f98 : bv 32 := 0x00813823.
Lemma F_64f98 : fetch_word AsanUbsan.M.loaded_segments (0x64fe0 : word) = Some W_64f98.
Proof. vm_refl. Qed.
Lemma D_64f98 : decode_any W_64f98 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f9c : bv 32 := 0x00913423.
Lemma F_64f9c : fetch_word AsanUbsan.M.loaded_segments (0x64fe4 : word) = Some W_64f9c.
Proof. vm_refl. Qed.
Lemma D_64f9c : decode_any W_64f9c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa0 : bv 32 := 0x01213023.
Lemma F_64fa0 : fetch_word AsanUbsan.M.loaded_segments (0x64fe8 : word) = Some W_64fa0.
Proof. vm_refl. Qed.
Lemma D_64fa0 : decode_any W_64fa0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa4 : bv 32 := 0x02010413.
Lemma F_64fa4 : fetch_word AsanUbsan.M.loaded_segments (0x64fec : word) = Some W_64fa4.
Proof. vm_refl. Qed.
Lemma D_64fa4 : decode_any W_64fa4 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa8 : bv 32 := 0x000f0517.
Lemma F_64fa8 : fetch_word AsanUbsan.M.loaded_segments (0x64ff0 : word) = Some W_64fa8.
Proof. vm_refl. Qed.
Lemma D_64fa8 : decode_any W_64fa8 = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fac : bv 32 := 0x32050513.
Lemma F_64fac : fetch_word AsanUbsan.M.loaded_segments (0x64ff4 : word) = Some W_64fac.
Proof. vm_refl. Qed.
Lemma D_64fac : decode_any W_64fac = Some (OpImm ALU_ADD 10 10 800, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb0 : bv 32 := 0x199050ef.
Lemma F_64fb0 : fetch_word AsanUbsan.M.loaded_segments (0x64ff8 : word) = Some W_64fb0.
Proof. vm_refl. Qed.
Lemma D_64fb0 : decode_any W_64fb0 = Some (Jal 1 22936, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb4 : bv 32 := 0x00053483.
Lemma F_64fb4 : fetch_word AsanUbsan.M.loaded_segments (0x64ffc : word) = Some W_64fb4.
Proof. vm_refl. Qed.
Lemma D_64fb4 : decode_any W_64fb4 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb8 : bv 32 := 0x08048863.
Lemma F_64fb8 : fetch_word AsanUbsan.M.loaded_segments (0x65000 : word) = Some W_64fb8.
Proof. vm_refl. Qed.
Lemma D_64fb8 : decode_any W_64fb8 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fbc : bv 32 := 0x0604c503.
Lemma F_64fbc : fetch_word AsanUbsan.M.loaded_segments (0x65004 : word) = Some W_64fbc.
Proof. vm_refl. Qed.
Lemma D_64fbc : decode_any W_64fbc = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc0 : bv 32 := 0x0584b903.
Lemma F_64fc0 : fetch_word AsanUbsan.M.loaded_segments (0x65008 : word) = Some W_64fc0.
Proof. vm_refl. Qed.
Lemma D_64fc0 : decode_any W_64fc0 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc4 : bv 32 := 0x00050863.
Lemma F_64fc4 : fetch_word AsanUbsan.M.loaded_segments (0x6500c : word) = Some W_64fc4.
Proof. vm_refl. Qed.
Lemma D_64fc4 : decode_any W_64fc4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc8 : bv 32 := 0x00048513.
Lemma F_64fc8 : fetch_word AsanUbsan.M.loaded_segments (0x65010 : word) = Some W_64fc8.
Proof. vm_refl. Qed.
Lemma D_64fc8 : decode_any W_64fc8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fcc : bv 32 := 0x00040593.
Lemma F_64fcc : fetch_word AsanUbsan.M.loaded_segments (0x65014 : word) = Some W_64fcc.
Proof. vm_refl. Qed.
Lemma D_64fcc : decode_any W_64fcc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fd0 : bv 32 := 0xa01ff0ef.
Lemma F_64fd0 : fetch_word AsanUbsan.M.loaded_segments (0x65018 : word) = Some W_64fd0.
Proof. vm_refl. Qed.
Lemma D_64fd0 : decode_any W_64fd0 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fd4 : bv 32 := 0xff990593.
Lemma F_64fd4 : fetch_word AsanUbsan.M.loaded_segments (0x6501c : word) = Some W_64fd4.
Proof. vm_refl. Qed.
Lemma D_64fd4 : decode_any W_64fd4 = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fd8 : bv 32 := 0x00100513.
Lemma F_64fd8 : fetch_word AsanUbsan.M.loaded_segments (0x65020 : word) = Some W_64fd8.
Proof. vm_refl. Qed.
Lemma D_64fd8 : decode_any W_64fd8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fdc : bv 32 := 0x00b51533.
Lemma F_64fdc : fetch_word AsanUbsan.M.loaded_segments (0x65024 : word) = Some W_64fdc.
Proof. vm_refl. Qed.
Lemma D_64fdc : decode_any W_64fdc = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fe0 : bv 32 := 0x0005061b.
Lemma F_64fe0 : fetch_word AsanUbsan.M.loaded_segments (0x65028 : word) = Some W_64fe0.
Proof. vm_refl. Qed.
Lemma D_64fe0 : decode_any W_64fe0 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fe4 : bv 32 := 0x08c05263.
Lemma F_64fe4 : fetch_word AsanUbsan.M.loaded_segments (0x6502c : word) = Some W_64fe4.
Proof. vm_refl. Qed.
Lemma D_64fe4 : decode_any W_64fe4 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fe8 : bv 32 := 0x000016b7.
Lemma F_64fe8 : fetch_word AsanUbsan.M.loaded_segments (0x65030 : word) = Some W_64fe8.
Proof. vm_refl. Qed.
Lemma D_64fe8 : decode_any W_64fe8 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fec : bv 32 := 0xff190613.
Lemma F_64fec : fetch_word AsanUbsan.M.loaded_segments (0x65034 : word) = Some W_64fec.
Proof. vm_refl. Qed.
Lemma D_64fec : decode_any W_64fec = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ff0 : bv 32 := 0x20000713.
Lemma F_64ff0 : fetch_word AsanUbsan.M.loaded_segments (0x65038 : word) = Some W_64ff0.
Proof. vm_refl. Qed.
Lemma D_64ff0 : decode_any W_64ff0 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ff4 : bv 32 := 0xfff00793.
Lemma F_64ff4 : fetch_word AsanUbsan.M.loaded_segments (0x6503c : word) = Some W_64ff4.
Proof. vm_refl. Qed.
Lemma D_64ff4 : decode_any W_64ff4 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ff8 : bv 32 := 0x00c71733.
Lemma F_64ff8 : fetch_word AsanUbsan.M.loaded_segments (0x65040 : word) = Some W_64ff8.
Proof. vm_refl. Qed.
Lemma D_64ff8 : decode_any W_64ff8 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ffc : bv 32 := 0x0084b603.
Lemma F_64ffc : fetch_word AsanUbsan.M.loaded_segments (0x65044 : word) = Some W_64ffc.
Proof. vm_refl. Qed.
Lemma D_64ffc : decode_any W_64ffc = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

