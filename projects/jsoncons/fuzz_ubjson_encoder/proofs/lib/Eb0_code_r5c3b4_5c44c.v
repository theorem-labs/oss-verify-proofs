(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_579ac : bv 32 := 0x000eb517.
Lemma F_579ac : fetch_word AsanUbsan.M.loaded_segments (0x579fc : word) = Some W_579ac.
Proof. vm_refl. Qed.
Lemma D_579ac : decode_any W_579ac = Some (Auipc 10 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_579b0 : bv 32 := 0x0bc53503.
Lemma F_579b0 : fetch_word AsanUbsan.M.loaded_segments (0x57a00 : word) = Some W_579b0.
Proof. vm_refl. Qed.
Lemma D_579b0 : decode_any W_579b0 = Some (Load SZ8 true 10 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_579b4 : bv 32 := 0x06a76463.
Lemma F_579b4 : fetch_word AsanUbsan.M.loaded_segments (0x57a04 : word) = Some W_579b4.
Proof. vm_refl. Qed.
Lemma D_579b4 : decode_any W_579b4 = Some (Branch BC_LTU 14 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_579b8 : bv 32 := 0x00100593.
Lemma F_579b8 : fetch_word AsanUbsan.M.loaded_segments (0x57a08 : word) = Some W_579b8.
Proof. vm_refl. Qed.
Lemma D_579b8 : decode_any W_579b8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_579bc : bv 32 := 0x02559593.
Lemma F_579bc : fetch_word AsanUbsan.M.loaded_segments (0x57a0c : word) = Some W_579bc.
Proof. vm_refl. Qed.
Lemma D_579bc : decode_any W_579bc = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_579c0 : bv 32 := 0x00b50533.
Lemma F_579c0 : fetch_word AsanUbsan.M.loaded_segments (0x57a10 : word) = Some W_579c0.
Proof. vm_refl. Qed.
Lemma D_579c0 : decode_any W_579c0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_579c4 : bv 32 := 0x04a77c63.
Lemma F_579c4 : fetch_word AsanUbsan.M.loaded_segments (0x57a14 : word) = Some W_579c4.
Proof. vm_refl. Qed.
Lemma D_579c4 : decode_any W_579c4 = Some (Branch BC_GEU 14 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_579c8 : bv 32 := 0x000e6517.
Lemma F_579c8 : fetch_word AsanUbsan.M.loaded_segments (0x57a18 : word) = Some W_579c8.
Proof. vm_refl. Qed.
Lemma D_579c8 : decode_any W_579c8 = Some (Auipc 10 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_579cc : bv 32 := 0xea853583.
Lemma F_579cc : fetch_word AsanUbsan.M.loaded_segments (0x57a1c : word) = Some W_579cc.
Proof. vm_refl. Qed.
Lemma D_579cc : decode_any W_579cc = Some (Load SZ8 true 11 10 3752, 4%Z).
Proof. vm_refl. Qed.

Definition W_579d0 : bv 32 := 0x0305a683.
Lemma F_579d0 : fetch_word AsanUbsan.M.loaded_segments (0x57a20 : word) = Some W_579d0.
Proof. vm_refl. Qed.
Lemma D_579d0 : decode_any W_579d0 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_579d4 : bv 32 := 0x04d05463.
Lemma F_579d4 : fetch_word AsanUbsan.M.loaded_segments (0x57a24 : word) = Some W_579d4.
Proof. vm_refl. Qed.
Lemma D_579d4 : decode_any W_579d4 = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_579d8 : bv 32 := 0x00275503.
Lemma F_579d8 : fetch_word AsanUbsan.M.loaded_segments (0x57a28 : word) = Some W_579d8.
Proof. vm_refl. Qed.
Lemma D_579d8 : decode_any W_579d8 = Some (Load SZ2 false 10 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_579dc : bv 32 := 0x00476603.
Lemma F_579dc : fetch_word AsanUbsan.M.loaded_segments (0x57a2c : word) = Some W_579dc.
Proof. vm_refl. Qed.
Lemma D_579dc : decode_any W_579dc = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_579e0 : bv 32 := 0x02051513.
Lemma F_579e0 : fetch_word AsanUbsan.M.loaded_segments (0x57a30 : word) = Some W_579e0.
Proof. vm_refl. Qed.
Lemma D_579e0 : decode_any W_579e0 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_579e4 : bv 32 := 0x00c56633.
Lemma F_579e4 : fetch_word AsanUbsan.M.loaded_segments (0x57a34 : word) = Some W_579e4.
Proof. vm_refl. Qed.
Lemma D_579e4 : decode_any W_579e4 = Some (Op ALU_OR 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_579e8 : bv 32 := 0x00800513.
Lemma F_579e8 : fetch_word AsanUbsan.M.loaded_segments (0x57a38 : word) = Some W_579e8.
Proof. vm_refl. Qed.
Lemma D_579e8 : decode_any W_579e8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_579ec : bv 32 := 0x02a66863.
Lemma F_579ec : fetch_word AsanUbsan.M.loaded_segments (0x57a3c : word) = Some W_579ec.
Proof. vm_refl. Qed.
Lemma D_579ec : decode_any W_579ec = Some (Branch BC_LTU 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_579f0 : bv 32 := 0xff860613.
Lemma F_579f0 : fetch_word AsanUbsan.M.loaded_segments (0x57a40 : word) = Some W_579f0.
Proof. vm_refl. Qed.
Lemma D_579f0 : decode_any W_579f0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_579f4 : bv 32 := 0x00070913.
Lemma F_579f4 : fetch_word AsanUbsan.M.loaded_segments (0x57a44 : word) = Some W_579f4.
Proof. vm_refl. Qed.
Lemma D_579f4 : decode_any W_579f4 = Some (OpImm ALU_ADD 18 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_579f8 : bv 32 := 0x01870513.
Lemma F_579f8 : fetch_word AsanUbsan.M.loaded_segments (0x57a48 : word) = Some W_579f8.
Proof. vm_refl. Qed.
Lemma D_579f8 : decode_any W_579f8 = Some (OpImm ALU_ADD 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_579fc : bv 32 := 0x00d66463.
Lemma F_579fc : fetch_word AsanUbsan.M.loaded_segments (0x57a4c : word) = Some W_579fc.
Proof. vm_refl. Qed.
Lemma D_579fc : decode_any W_579fc = Some (Branch BC_LTU 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a00 : bv 32 := 0x00068613.
Lemma F_57a00 : fetch_word AsanUbsan.M.loaded_segments (0x57a50 : word) = Some W_57a00.
Proof. vm_refl. Qed.
Lemma D_57a00 : decode_any W_57a00 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a04 : bv 32 := 0x000e6697.
Lemma F_57a04 : fetch_word AsanUbsan.M.loaded_segments (0x57a54 : word) = Some W_57a04.
Proof. vm_refl. Qed.
Lemma D_57a04 : decode_any W_57a04 = Some (Auipc 13 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a08 : bv 32 := 0xe946b683.
Lemma F_57a08 : fetch_word AsanUbsan.M.loaded_segments (0x57a58 : word) = Some W_57a08.
Proof. vm_refl. Qed.
Lemma D_57a08 : decode_any W_57a08 = Some (Load SZ8 true 13 13 3732, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a0c : bv 32 := 0x0006b683.
Lemma F_57a0c : fetch_word AsanUbsan.M.loaded_segments (0x57a5c : word) = Some W_57a0c.
Proof. vm_refl. Qed.
Lemma D_57a0c : decode_any W_57a0c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a10 : bv 32 := 0x0385a583.
Lemma F_57a10 : fetch_word AsanUbsan.M.loaded_segments (0x57a60 : word) = Some W_57a10.
Proof. vm_refl. Qed.
Lemma D_57a10 : decode_any W_57a10 = Some (Load SZ4 true 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a14 : bv 32 := 0x000680e7.
Lemma F_57a14 : fetch_word AsanUbsan.M.loaded_segments (0x57a64 : word) = Some W_57a14.
Proof. vm_refl. Qed.
Lemma D_57a14 : decode_any W_57a14 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a18 : bv 32 := 0x00090713.
Lemma F_57a18 : fetch_word AsanUbsan.M.loaded_segments (0x57a68 : word) = Some W_57a18.
Proof. vm_refl. Qed.
Lemma D_57a18 : decode_any W_57a18 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a1c : bv 32 := 0x00010513.
Lemma F_57a1c : fetch_word AsanUbsan.M.loaded_segments (0x57a6c : word) = Some W_57a1c.
Proof. vm_refl. Qed.
Lemma D_57a1c : decode_any W_57a1c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a20 : bv 32 := 0x00070593.
Lemma F_57a20 : fetch_word AsanUbsan.M.loaded_segments (0x57a70 : word) = Some W_57a20.
Proof. vm_refl. Qed.
Lemma D_57a20 : decode_any W_57a20 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a24 : bv 32 := 0xe91fd0ef.
Lemma F_57a24 : fetch_word AsanUbsan.M.loaded_segments (0x57a74 : word) = Some W_57a24.
Proof. vm_refl. Qed.
Lemma D_57a24 : decode_any W_57a24 = Some (Jal 1 2088592, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a28 : bv 32 := 0x0184b503.
Lemma F_57a28 : fetch_word AsanUbsan.M.loaded_segments (0x57a78 : word) = Some W_57a28.
Proof. vm_refl. Qed.
Lemma D_57a28 : decode_any W_57a28 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a2c : bv 32 := 0x00ab7c63.
Lemma F_57a2c : fetch_word AsanUbsan.M.loaded_segments (0x57a7c : word) = Some W_57a2c.
Proof. vm_refl. Qed.
Lemma D_57a2c : decode_any W_57a2c = Some (Branch BC_GEU 22 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a30 : bv 32 := 0x00013603.
Lemma F_57a30 : fetch_word AsanUbsan.M.loaded_segments (0x57a80 : word) = Some W_57a30.
Proof. vm_refl. Qed.
Lemma D_57a30 : decode_any W_57a30 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a34 : bv 32 := 0x00813683.
Lemma F_57a34 : fetch_word AsanUbsan.M.loaded_segments (0x57a84 : word) = Some W_57a34.
Proof. vm_refl. Qed.
Lemma D_57a34 : decode_any W_57a34 = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a38 : bv 32 := 0x00040513.
Lemma F_57a38 : fetch_word AsanUbsan.M.loaded_segments (0x57a88 : word) = Some W_57a38.
Proof. vm_refl. Qed.
Lemma D_57a38 : decode_any W_57a38 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a3c : bv 32 := 0x00048593.
Lemma F_57a3c : fetch_word AsanUbsan.M.loaded_segments (0x57a8c : word) = Some W_57a3c.
Proof. vm_refl. Qed.
Lemma D_57a3c : decode_any W_57a3c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57a40 : bv 32 := 0x831fd0ef.
Lemma F_57a40 : fetch_word AsanUbsan.M.loaded_segments (0x57a90 : word) = Some W_57a40.
Proof. vm_refl. Qed.
Lemma D_57a40 : decode_any W_57a40 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.
