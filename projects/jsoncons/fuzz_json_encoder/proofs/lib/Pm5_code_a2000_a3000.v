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
Definition W_a2b10 : bv 32 := 0xfe010113.
Lemma F_a2b10 : fetch_word AsanUbsan.M.loaded_segments (0xa2b58 : word) = Some W_a2b10.
Proof. vm_refl. Qed.
Lemma D_a2b10 : decode_any W_a2b10 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b14 : bv 32 := 0x00113c23.
Lemma F_a2b14 : fetch_word AsanUbsan.M.loaded_segments (0xa2b5c : word) = Some W_a2b14.
Proof. vm_refl. Qed.
Lemma D_a2b14 : decode_any W_a2b14 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b18 : bv 32 := 0x00813823.
Lemma F_a2b18 : fetch_word AsanUbsan.M.loaded_segments (0xa2b60 : word) = Some W_a2b18.
Proof. vm_refl. Qed.
Lemma D_a2b18 : decode_any W_a2b18 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b1c : bv 32 := 0x00060593.
Lemma F_a2b1c : fetch_word AsanUbsan.M.loaded_segments (0xa2b64 : word) = Some W_a2b1c.
Proof. vm_refl. Qed.
Lemma D_a2b1c : decode_any W_a2b1c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b20 : bv 32 := 0x00050413.
Lemma F_a2b20 : fetch_word AsanUbsan.M.loaded_segments (0xa2b68 : word) = Some W_a2b20.
Proof. vm_refl. Qed.
Lemma D_a2b20 : decode_any W_a2b20 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b24 : bv 32 := 0x00d53023.
Lemma F_a2b24 : fetch_word AsanUbsan.M.loaded_segments (0xa2b6c : word) = Some W_a2b24.
Proof. vm_refl. Qed.
Lemma D_a2b24 : decode_any W_a2b24 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b28 : bv 32 := 0x00013423.
Lemma F_a2b28 : fetch_word AsanUbsan.M.loaded_segments (0xa2b70 : word) = Some W_a2b28.
Proof. vm_refl. Qed.
Lemma D_a2b28 : decode_any W_a2b28 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b2c : bv 32 := 0x0019d517.
Lemma F_a2b2c : fetch_word AsanUbsan.M.loaded_segments (0xa2b74 : word) = Some W_a2b2c.
Proof. vm_refl. Qed.
Lemma D_a2b2c : decode_any W_a2b2c = Some (Auipc 10 413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b30 : bv 32 := 0xb1450513.
Lemma F_a2b30 : fetch_word AsanUbsan.M.loaded_segments (0xa2b78 : word) = Some W_a2b30.
Proof. vm_refl. Qed.
Lemma D_a2b30 : decode_any W_a2b30 = Some (OpImm ALU_ADD 10 10 2836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b34 : bv 32 := 0x00810613.
Lemma F_a2b34 : fetch_word AsanUbsan.M.loaded_segments (0xa2b7c : word) = Some W_a2b34.
Proof. vm_refl. Qed.
Lemma D_a2b34 : decode_any W_a2b34 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b38 : bv 32 := 0xcc5fd0ef.
Lemma F_a2b38 : fetch_word AsanUbsan.M.loaded_segments (0xa2b80 : word) = Some W_a2b38.
Proof. vm_refl. Qed.
Lemma D_a2b38 : decode_any W_a2b38 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b3c : bv 32 := 0x00813583.
Lemma F_a2b3c : fetch_word AsanUbsan.M.loaded_segments (0xa2b84 : word) = Some W_a2b3c.
Proof. vm_refl. Qed.
Lemma D_a2b3c : decode_any W_a2b3c = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b40 : bv 32 := 0x00a42623.
Lemma F_a2b40 : fetch_word AsanUbsan.M.loaded_segments (0xa2b88 : word) = Some W_a2b40.
Proof. vm_refl. Qed.
Lemma D_a2b40 : decode_any W_a2b40 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b44 : bv 32 := 0x00059a63.
Lemma F_a2b44 : fetch_word AsanUbsan.M.loaded_segments (0xa2b8c : word) = Some W_a2b44.
Proof. vm_refl. Qed.
Lemma D_a2b44 : decode_any W_a2b44 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b48 : bv 32 := 0x01813083.
Lemma F_a2b48 : fetch_word AsanUbsan.M.loaded_segments (0xa2b90 : word) = Some W_a2b48.
Proof. vm_refl. Qed.
Lemma D_a2b48 : decode_any W_a2b48 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b4c : bv 32 := 0x01013403.
Lemma F_a2b4c : fetch_word AsanUbsan.M.loaded_segments (0xa2b94 : word) = Some W_a2b4c.
Proof. vm_refl. Qed.
Lemma D_a2b4c : decode_any W_a2b4c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b50 : bv 32 := 0x02010113.
Lemma F_a2b50 : fetch_word AsanUbsan.M.loaded_segments (0xa2b98 : word) = Some W_a2b50.
Proof. vm_refl. Qed.
Lemma D_a2b50 : decode_any W_a2b50 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2b54 : bv 32 := 0x00008067.
Lemma F_a2b54 : fetch_word AsanUbsan.M.loaded_segments (0xa2b9c : word) = Some W_a2b54.
Proof. vm_refl. Qed.
Lemma D_a2b54 : decode_any W_a2b54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2df8 : bv 32 := 0x00058613.
Lemma F_a2df8 : fetch_word AsanUbsan.M.loaded_segments (0xa2e40 : word) = Some W_a2df8.
Proof. vm_refl. Qed.
Lemma D_a2df8 : decode_any W_a2df8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2dfc : bv 32 := 0x001ad597.
Lemma F_a2dfc : fetch_word AsanUbsan.M.loaded_segments (0xa2e44 : word) = Some W_a2dfc.
Proof. vm_refl. Qed.
Lemma D_a2dfc : decode_any W_a2dfc = Some (Auipc 11 429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e00 : bv 32 := 0x85458593.
Lemma F_a2e00 : fetch_word AsanUbsan.M.loaded_segments (0xa2e48 : word) = Some W_a2e00.
Proof. vm_refl. Qed.
Lemma D_a2e00 : decode_any W_a2e00 = Some (OpImm ALU_ADD 11 11 2132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e04 : bv 32 := 0x00050693.
Lemma F_a2e04 : fetch_word AsanUbsan.M.loaded_segments (0xa2e4c : word) = Some W_a2e04.
Proof. vm_refl. Qed.
Lemma D_a2e04 : decode_any W_a2e04 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e08 : bv 32 := 0x00058513.
Lemma F_a2e08 : fetch_word AsanUbsan.M.loaded_segments (0xa2e50 : word) = Some W_a2e08.
Proof. vm_refl. Qed.
Lemma D_a2e08 : decode_any W_a2e08 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e0c : bv 32 := 0x00068593.
Lemma F_a2e0c : fetch_word AsanUbsan.M.loaded_segments (0xa2e54 : word) = Some W_a2e0c.
Proof. vm_refl. Qed.
Lemma D_a2e0c : decode_any W_a2e0c = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e10 : bv 32 := 0x00000693.
Lemma F_a2e10 : fetch_word AsanUbsan.M.loaded_segments (0xa2e58 : word) = Some W_a2e10.
Proof. vm_refl. Qed.
Lemma D_a2e10 : decode_any W_a2e10 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e14 : bv 32 := 0x0040006f.
Lemma F_a2e14 : fetch_word AsanUbsan.M.loaded_segments (0xa2e5c : word) = Some W_a2e14.
Proof. vm_refl. Qed.
Lemma D_a2e14 : decode_any W_a2e14 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e18 : bv 32 := 0xf9010113.
Lemma F_a2e18 : fetch_word AsanUbsan.M.loaded_segments (0xa2e60 : word) = Some W_a2e18.
Proof. vm_refl. Qed.
Lemma D_a2e18 : decode_any W_a2e18 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e1c : bv 32 := 0x06113423.
Lemma F_a2e1c : fetch_word AsanUbsan.M.loaded_segments (0xa2e64 : word) = Some W_a2e1c.
Proof. vm_refl. Qed.
Lemma D_a2e1c : decode_any W_a2e1c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e20 : bv 32 := 0x06813023.
Lemma F_a2e20 : fetch_word AsanUbsan.M.loaded_segments (0xa2e68 : word) = Some W_a2e20.
Proof. vm_refl. Qed.
Lemma D_a2e20 : decode_any W_a2e20 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e24 : bv 32 := 0x04913c23.
Lemma F_a2e24 : fetch_word AsanUbsan.M.loaded_segments (0xa2e6c : word) = Some W_a2e24.
Proof. vm_refl. Qed.
Lemma D_a2e24 : decode_any W_a2e24 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e28 : bv 32 := 0x05213823.
Lemma F_a2e28 : fetch_word AsanUbsan.M.loaded_segments (0xa2e70 : word) = Some W_a2e28.
Proof. vm_refl. Qed.
Lemma D_a2e28 : decode_any W_a2e28 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e2c : bv 32 := 0x05313423.
Lemma F_a2e2c : fetch_word AsanUbsan.M.loaded_segments (0xa2e74 : word) = Some W_a2e2c.
Proof. vm_refl. Qed.
Lemma D_a2e2c : decode_any W_a2e2c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e30 : bv 32 := 0x05413023.
Lemma F_a2e30 : fetch_word AsanUbsan.M.loaded_segments (0xa2e78 : word) = Some W_a2e30.
Proof. vm_refl. Qed.
Lemma D_a2e30 : decode_any W_a2e30 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e34 : bv 32 := 0x03513c23.
Lemma F_a2e34 : fetch_word AsanUbsan.M.loaded_segments (0xa2e7c : word) = Some W_a2e34.
Proof. vm_refl. Qed.
Lemma D_a2e34 : decode_any W_a2e34 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e38 : bv 32 := 0x03613823.
Lemma F_a2e38 : fetch_word AsanUbsan.M.loaded_segments (0xa2e80 : word) = Some W_a2e38.
Proof. vm_refl. Qed.
Lemma D_a2e38 : decode_any W_a2e38 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e3c : bv 32 := 0x03713423.
Lemma F_a2e3c : fetch_word AsanUbsan.M.loaded_segments (0xa2e84 : word) = Some W_a2e3c.
Proof. vm_refl. Qed.
Lemma D_a2e3c : decode_any W_a2e3c = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e40 : bv 32 := 0x03813023.
Lemma F_a2e40 : fetch_word AsanUbsan.M.loaded_segments (0xa2e88 : word) = Some W_a2e40.
Proof. vm_refl. Qed.
Lemma D_a2e40 : decode_any W_a2e40 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e44 : bv 32 := 0x01913c23.
Lemma F_a2e44 : fetch_word AsanUbsan.M.loaded_segments (0xa2e8c : word) = Some W_a2e44.
Proof. vm_refl. Qed.
Lemma D_a2e44 : decode_any W_a2e44 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e48 : bv 32 := 0x00068413.
Lemma F_a2e48 : fetch_word AsanUbsan.M.loaded_segments (0xa2e90 : word) = Some W_a2e48.
Proof. vm_refl. Qed.
Lemma D_a2e48 : decode_any W_a2e48 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e4c : bv 32 := 0x00050493.
Lemma F_a2e4c : fetch_word AsanUbsan.M.loaded_segments (0xa2e94 : word) = Some W_a2e4c.
Proof. vm_refl. Qed.
Lemma D_a2e4c : decode_any W_a2e4c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e50 : bv 32 := 0x00b13423.
Lemma F_a2e50 : fetch_word AsanUbsan.M.loaded_segments (0xa2e98 : word) = Some W_a2e50.
Proof. vm_refl. Qed.
Lemma D_a2e50 : decode_any W_a2e50 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e54 : bv 32 := 0x00c13823.
Lemma F_a2e54 : fetch_word AsanUbsan.M.loaded_segments (0xa2e9c : word) = Some W_a2e54.
Proof. vm_refl. Qed.
Lemma D_a2e54 : decode_any W_a2e54 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e58 : bv 32 := 0x00068463.
Lemma F_a2e58 : fetch_word AsanUbsan.M.loaded_segments (0xa2ea0 : word) = Some W_a2e58.
Proof. vm_refl. Qed.
Lemma D_a2e58 : decode_any W_a2e58 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e60 : bv 32 := 0x0006069b.
Lemma F_a2e60 : fetch_word AsanUbsan.M.loaded_segments (0xa2ea8 : word) = Some W_a2e60.
Proof. vm_refl. Qed.
Lemma D_a2e60 : decode_any W_a2e60 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e64 : bv 32 := 0x00000513.
Lemma F_a2e64 : fetch_word AsanUbsan.M.loaded_segments (0xa2eac : word) = Some W_a2e64.
Proof. vm_refl. Qed.
Lemma D_a2e64 : decode_any W_a2e64 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e68 : bv 32 := 0x1c068a63.
Lemma F_a2e68 : fetch_word AsanUbsan.M.loaded_segments (0xa2eb0 : word) = Some W_a2e68.
Proof. vm_refl. Qed.
Lemma D_a2e68 : decode_any W_a2e68 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e6c : bv 32 := 0x1c058863.
Lemma F_a2e6c : fetch_word AsanUbsan.M.loaded_segments (0xa2eb4 : word) = Some W_a2e6c.
Proof. vm_refl. Qed.
Lemma D_a2e6c : decode_any W_a2e6c = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e70 : bv 32 := 0x02065693.
Lemma F_a2e70 : fetch_word AsanUbsan.M.loaded_segments (0xa2eb8 : word) = Some W_a2e70.
Proof. vm_refl. Qed.
Lemma D_a2e70 : decode_any W_a2e70 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e74 : bv 32 := 0xfff00513.
Lemma F_a2e74 : fetch_word AsanUbsan.M.loaded_segments (0xa2ebc : word) = Some W_a2e74.
Proof. vm_refl. Qed.
Lemma D_a2e74 : decode_any W_a2e74 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e78 : bv 32 := 0xfff6d717.
Lemma F_a2e78 : fetch_word AsanUbsan.M.loaded_segments (0xa2ec0 : word) = Some W_a2e78.
Proof. vm_refl. Qed.
Lemma D_a2e78 : decode_any W_a2e78 = Some (Auipc 14 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e7c : bv 32 := 0xfff6d797.
Lemma F_a2e7c : fetch_word AsanUbsan.M.loaded_segments (0xa2ec4 : word) = Some W_a2e7c.
Proof. vm_refl. Qed.
Lemma D_a2e7c : decode_any W_a2e7c = Some (Auipc 15 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e80 : bv 32 := 0x02055513.
Lemma F_a2e80 : fetch_word AsanUbsan.M.loaded_segments (0xa2ec8 : word) = Some W_a2e80.
Proof. vm_refl. Qed.
Lemma D_a2e80 : decode_any W_a2e80 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e84 : bv 32 := 0x4647b783.
Lemma F_a2e84 : fetch_word AsanUbsan.M.loaded_segments (0xa2ecc : word) = Some W_a2e84.
Proof. vm_refl. Qed.
Lemma D_a2e84 : decode_any W_a2e84 = Some (Load SZ8 true 15 15 1124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e88 : bv 32 := 0x00a67633.
Lemma F_a2e88 : fetch_word AsanUbsan.M.loaded_segments (0xa2ed0 : word) = Some W_a2e88.
Proof. vm_refl. Qed.
Lemma D_a2e88 : decode_any W_a2e88 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e8c : bv 32 := 0xfff6d517.
Lemma F_a2e8c : fetch_word AsanUbsan.M.loaded_segments (0xa2ed4 : word) = Some W_a2e8c.
Proof. vm_refl. Qed.
Lemma D_a2e8c : decode_any W_a2e8c = Some (Auipc 10 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e90 : bv 32 := 0x57c53803.
Lemma F_a2e90 : fetch_word AsanUbsan.M.loaded_segments (0xa2ed8 : word) = Some W_a2e90.
Proof. vm_refl. Qed.
Lemma D_a2e90 : decode_any W_a2e90 = Some (Load SZ8 true 16 10 1404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e94 : bv 32 := 0x42873503.
Lemma F_a2e94 : fetch_word AsanUbsan.M.loaded_segments (0xa2edc : word) = Some W_a2e94.
Proof. vm_refl. Qed.
Lemma D_a2e94 : decode_any W_a2e94 = Some (Load SZ8 true 10 14 1064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e98 : bv 32 := 0x02f60733.
Lemma F_a2e98 : fetch_word AsanUbsan.M.loaded_segments (0xa2ee0 : word) = Some W_a2e98.
Proof. vm_refl. Qed.
Lemma D_a2e98 : decode_any W_a2e98 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e9c : bv 32 := 0x00361793.
Lemma F_a2e9c : fetch_word AsanUbsan.M.loaded_segments (0xa2ee4 : word) = Some W_a2e9c.
Proof. vm_refl. Qed.
Lemma D_a2e9c : decode_any W_a2e9c = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea0 : bv 32 := 0x01074633.
Lemma F_a2ea0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ee8 : word) = Some W_a2ea0.
Proof. vm_refl. Qed.
Lemma D_a2ea0 : decode_any W_a2ea0 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea4 : bv 32 := 0x00f58733.
Lemma F_a2ea4 : fetch_word AsanUbsan.M.loaded_segments (0xa2eec : word) = Some W_a2ea4.
Proof. vm_refl. Qed.
Lemma D_a2ea4 : decode_any W_a2ea4 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea8 : bv 32 := 0x0005b783.
Lemma F_a2ea8 : fetch_word AsanUbsan.M.loaded_segments (0xa2ef0 : word) = Some W_a2ea8.
Proof. vm_refl. Qed.
Lemma D_a2ea8 : decode_any W_a2ea8 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eac : bv 32 := 0x00858593.
Lemma F_a2eac : fetch_word AsanUbsan.M.loaded_segments (0xa2ef4 : word) = Some W_a2eac.
Proof. vm_refl. Qed.
Lemma D_a2eac : decode_any W_a2eac = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb0 : bv 32 := 0x02a787b3.
Lemma F_a2eb0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ef8 : word) = Some W_a2eb0.
Proof. vm_refl. Qed.
Lemma D_a2eb0 : decode_any W_a2eb0 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb4 : bv 32 := 0x02f7d813.
Lemma F_a2eb4 : fetch_word AsanUbsan.M.loaded_segments (0xa2efc : word) = Some W_a2eb4.
Proof. vm_refl. Qed.
Lemma D_a2eb4 : decode_any W_a2eb4 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb8 : bv 32 := 0x00f847b3.
Lemma F_a2eb8 : fetch_word AsanUbsan.M.loaded_segments (0xa2f00 : word) = Some W_a2eb8.
Proof. vm_refl. Qed.
Lemma D_a2eb8 : decode_any W_a2eb8 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ebc : bv 32 := 0x02a787b3.
Lemma F_a2ebc : fetch_word AsanUbsan.M.loaded_segments (0xa2f04 : word) = Some W_a2ebc.
Proof. vm_refl. Qed.
Lemma D_a2ebc : decode_any W_a2ebc = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec0 : bv 32 := 0x00c7c633.
Lemma F_a2ec0 : fetch_word AsanUbsan.M.loaded_segments (0xa2f08 : word) = Some W_a2ec0.
Proof. vm_refl. Qed.
Lemma D_a2ec0 : decode_any W_a2ec0 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec4 : bv 32 := 0x02a60633.
Lemma F_a2ec4 : fetch_word AsanUbsan.M.loaded_segments (0xa2f0c : word) = Some W_a2ec4.
Proof. vm_refl. Qed.
Lemma D_a2ec4 : decode_any W_a2ec4 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec8 : bv 32 := 0xfee590e3.
Lemma F_a2ec8 : fetch_word AsanUbsan.M.loaded_segments (0xa2f10 : word) = Some W_a2ec8.
Proof. vm_refl. Qed.
Lemma D_a2ec8 : decode_any W_a2ec8 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ecc : bv 32 := 0x00010b37.
Lemma F_a2ecc : fetch_word AsanUbsan.M.loaded_segments (0xa2f14 : word) = Some W_a2ecc.
Proof. vm_refl. Qed.
Lemma D_a2ecc : decode_any W_a2ecc = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ed0 : bv 32 := 0x80000bb7.
Lemma F_a2ed0 : fetch_word AsanUbsan.M.loaded_segments (0xa2f18 : word) = Some W_a2ed0.
Proof. vm_refl. Qed.
Lemma D_a2ed0 : decode_any W_a2ed0 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ed4 : bv 32 := 0x02a685b3.
Lemma F_a2ed4 : fetch_word AsanUbsan.M.loaded_segments (0xa2f1c : word) = Some W_a2ed4.
Proof. vm_refl. Qed.
Lemma D_a2ed4 : decode_any W_a2ed4 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ed8 : bv 32 := 0x004006b7.
Lemma F_a2ed8 : fetch_word AsanUbsan.M.loaded_segments (0xa2f20 : word) = Some W_a2ed8.
Proof. vm_refl. Qed.
Lemma D_a2ed8 : decode_any W_a2ed8 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2edc : bv 32 := 0xfffb0b1b.
Lemma F_a2edc : fetch_word AsanUbsan.M.loaded_segments (0xa2f24 : word) = Some W_a2edc.
Proof. vm_refl. Qed.
Lemma D_a2edc : decode_any W_a2edc = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ee0 : bv 32 := 0xfffb8b9b.
Lemma F_a2ee0 : fetch_word AsanUbsan.M.loaded_segments (0xa2f28 : word) = Some W_a2ee0.
Proof. vm_refl. Qed.
Lemma D_a2ee0 : decode_any W_a2ee0 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ee4 : bv 32 := 0x02f5d713.
Lemma F_a2ee4 : fetch_word AsanUbsan.M.loaded_segments (0xa2f2c : word) = Some W_a2ee4.
Proof. vm_refl. Qed.
Lemma D_a2ee4 : decode_any W_a2ee4 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ee8 : bv 32 := 0x00b745b3.
Lemma F_a2ee8 : fetch_word AsanUbsan.M.loaded_segments (0xa2f30 : word) = Some W_a2ee8.
Proof. vm_refl. Qed.
Lemma D_a2ee8 : decode_any W_a2ee8 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eec : bv 32 := 0x02a585b3.
Lemma F_a2eec : fetch_word AsanUbsan.M.loaded_segments (0xa2f34 : word) = Some W_a2eec.
Proof. vm_refl. Qed.
Lemma D_a2eec : decode_any W_a2eec = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ef0 : bv 32 := 0x00c5c5b3.
Lemma F_a2ef0 : fetch_word AsanUbsan.M.loaded_segments (0xa2f38 : word) = Some W_a2ef0.
Proof. vm_refl. Qed.
Lemma D_a2ef0 : decode_any W_a2ef0 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ef4 : bv 32 := 0x02a585b3.
Lemma F_a2ef4 : fetch_word AsanUbsan.M.loaded_segments (0xa2f3c : word) = Some W_a2ef4.
Proof. vm_refl. Qed.
Lemma D_a2ef4 : decode_any W_a2ef4 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ef8 : bv 32 := 0x02f5d613.
Lemma F_a2ef8 : fetch_word AsanUbsan.M.loaded_segments (0xa2f40 : word) = Some W_a2ef8.
Proof. vm_refl. Qed.
Lemma D_a2ef8 : decode_any W_a2ef8 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2efc : bv 32 := 0x00b645b3.
Lemma F_a2efc : fetch_word AsanUbsan.M.loaded_segments (0xa2f44 : word) = Some W_a2efc.
Proof. vm_refl. Qed.
Lemma D_a2efc : decode_any W_a2efc = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f00 : bv 32 := 0x02a58533.
Lemma F_a2f00 : fetch_word AsanUbsan.M.loaded_segments (0xa2f48 : word) = Some W_a2f00.
Proof. vm_refl. Qed.
Lemma D_a2f00 : decode_any W_a2f00 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f04 : bv 32 := 0x02f55593.
Lemma F_a2f04 : fetch_word AsanUbsan.M.loaded_segments (0xa2f4c : word) = Some W_a2f04.
Proof. vm_refl. Qed.
Lemma D_a2f04 : decode_any W_a2f04 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f08 : bv 32 := 0x00a5c9b3.
Lemma F_a2f08 : fetch_word AsanUbsan.M.loaded_segments (0xa2f50 : word) = Some W_a2f08.
Proof. vm_refl. Qed.
Lemma D_a2f08 : decode_any W_a2f08 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f0c : bv 32 := 0x02c99513.
Lemma F_a2f0c : fetch_word AsanUbsan.M.loaded_segments (0xa2f54 : word) = Some W_a2f0c.
Proof. vm_refl. Qed.
Lemma D_a2f0c : decode_any W_a2f0c = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f10 : bv 32 := 0x02a55513.
Lemma F_a2f10 : fetch_word AsanUbsan.M.loaded_segments (0xa2f58 : word) = Some W_a2f10.
Proof. vm_refl. Qed.
Lemma D_a2f10 : decode_any W_a2f10 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f14 : bv 32 := 0x00a48933.
Lemma F_a2f14 : fetch_word AsanUbsan.M.loaded_segments (0xa2f5c : word) = Some W_a2f14.
Proof. vm_refl. Qed.
Lemma D_a2f14 : decode_any W_a2f14 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f18 : bv 32 := 0x00092503.
Lemma F_a2f18 : fetch_word AsanUbsan.M.loaded_segments (0xa2f60 : word) = Some W_a2f18.
Proof. vm_refl. Qed.
Lemma D_a2f18 : decode_any W_a2f18 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f1c : bv 32 := 0x01068c1b.
Lemma F_a2f1c : fetch_word AsanUbsan.M.loaded_segments (0xa2f64 : word) = Some W_a2f1c.
Proof. vm_refl. Qed.
Lemma D_a2f1c : decode_any W_a2f1c = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f20 : bv 32 := 0x01848c33.
Lemma F_a2f20 : fetch_word AsanUbsan.M.loaded_segments (0xa2f68 : word) = Some W_a2f20.
Proof. vm_refl. Qed.
Lemma D_a2f20 : decode_any W_a2f20 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f24 : bv 32 := 0x0230000f.
Lemma F_a2f24 : fetch_word AsanUbsan.M.loaded_segments (0xa2f6c : word) = Some W_a2f24.
Proof. vm_refl. Qed.
Lemma D_a2f24 : decode_any W_a2f24 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f28 : bv 32 := 0x01757cb3.
Lemma F_a2f28 : fetch_word AsanUbsan.M.loaded_segments (0xa2f70 : word) = Some W_a2f28.
Proof. vm_refl. Qed.
Lemma D_a2f28 : decode_any W_a2f28 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f2c : bv 32 := 0x0086869b.
Lemma F_a2f2c : fetch_word AsanUbsan.M.loaded_segments (0xa2f74 : word) = Some W_a2f2c.
Proof. vm_refl. Qed.
Lemma D_a2f2c : decode_any W_a2f2c = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f30 : bv 32 := 0x00d48a33.
Lemma F_a2f30 : fetch_word AsanUbsan.M.loaded_segments (0xa2f78 : word) = Some W_a2f30.
Proof. vm_refl. Qed.
Lemma D_a2f30 : decode_any W_a2f30 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f34 : bv 32 := 0x000c8593.
Lemma F_a2f34 : fetch_word AsanUbsan.M.loaded_segments (0xa2f7c : word) = Some W_a2f34.
Proof. vm_refl. Qed.
Lemma D_a2f34 : decode_any W_a2f34 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f38 : bv 32 := 0x04058c63.
Lemma F_a2f38 : fetch_word AsanUbsan.M.loaded_segments (0xa2f80 : word) = Some W_a2f38.
Proof. vm_refl. Qed.
Lemma D_a2f38 : decode_any W_a2f38 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f3c : bv 32 := 0x00058513.
Lemma F_a2f3c : fetch_word AsanUbsan.M.loaded_segments (0xa2f84 : word) = Some W_a2f3c.
Proof. vm_refl. Qed.
Lemma D_a2f3c : decode_any W_a2f3c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f40 : bv 32 := 0x0105d59b.
Lemma F_a2f40 : fetch_word AsanUbsan.M.loaded_segments (0xa2f88 : word) = Some W_a2f40.
Proof. vm_refl. Qed.
Lemma D_a2f40 : decode_any W_a2f40 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f44 : bv 32 := 0x00359613.
Lemma F_a2f44 : fetch_word AsanUbsan.M.loaded_segments (0xa2f8c : word) = Some W_a2f44.
Proof. vm_refl. Qed.
Lemma D_a2f44 : decode_any W_a2f44 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f48 : bv 32 := 0x00cc0633.
Lemma F_a2f48 : fetch_word AsanUbsan.M.loaded_segments (0xa2f90 : word) = Some W_a2f48.
Proof. vm_refl. Qed.
Lemma D_a2f48 : decode_any W_a2f48 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f4c : bv 32 := 0x00063603.
Lemma F_a2f4c : fetch_word AsanUbsan.M.loaded_segments (0xa2f94 : word) = Some W_a2f4c.
Proof. vm_refl. Qed.
Lemma D_a2f4c : decode_any W_a2f4c = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f50 : bv 32 := 0x02060463.
Lemma F_a2f50 : fetch_word AsanUbsan.M.loaded_segments (0xa2f98 : word) = Some W_a2f50.
Proof. vm_refl. Qed.
Lemma D_a2f50 : decode_any W_a2f50 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f54 : bv 32 := 0x02051593.
Lemma F_a2f54 : fetch_word AsanUbsan.M.loaded_segments (0xa2f9c : word) = Some W_a2f54.
Proof. vm_refl. Qed.
Lemma D_a2f54 : decode_any W_a2f54 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f58 : bv 32 := 0x0205d593.
Lemma F_a2f58 : fetch_word AsanUbsan.M.loaded_segments (0xa2fa0 : word) = Some W_a2f58.
Proof. vm_refl. Qed.
Lemma D_a2f58 : decode_any W_a2f58 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f5c : bv 32 := 0x0165f5b3.
Lemma F_a2f5c : fetch_word AsanUbsan.M.loaded_segments (0xa2fa4 : word) = Some W_a2f5c.
Proof. vm_refl. Qed.
Lemma D_a2f5c : decode_any W_a2f5c = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f60 : bv 32 := 0x00459593.
Lemma F_a2f60 : fetch_word AsanUbsan.M.loaded_segments (0xa2fa8 : word) = Some W_a2f60.
Proof. vm_refl. Qed.
Lemma D_a2f60 : decode_any W_a2f60 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f64 : bv 32 := 0x00b605b3.
Lemma F_a2f64 : fetch_word AsanUbsan.M.loaded_segments (0xa2fac : word) = Some W_a2f64.
Proof. vm_refl. Qed.
Lemma D_a2f64 : decode_any W_a2f64 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f68 : bv 32 := 0x0005b603.
Lemma F_a2f68 : fetch_word AsanUbsan.M.loaded_segments (0xa2fb0 : word) = Some W_a2f68.
Proof. vm_refl. Qed.
Lemma D_a2f68 : decode_any W_a2f68 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f6c : bv 32 := 0x0085a583.
Lemma F_a2f6c : fetch_word AsanUbsan.M.loaded_segments (0xa2fb4 : word) = Some W_a2f6c.
Proof. vm_refl. Qed.
Lemma D_a2f6c : decode_any W_a2f6c = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f70 : bv 32 := 0xfcc994e3.
Lemma F_a2f70 : fetch_word AsanUbsan.M.loaded_segments (0xa2fb8 : word) = Some W_a2f70.
Proof. vm_refl. Qed.
Lemma D_a2f70 : decode_any W_a2f70 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f74 : bv 32 := 0x0c80006f.
Lemma F_a2f74 : fetch_word AsanUbsan.M.loaded_segments (0xa2fbc : word) = Some W_a2f74.
Proof. vm_refl. Qed.
Lemma D_a2f74 : decode_any W_a2f74 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f90 : bv 32 := 0x00090513.
Lemma F_a2f90 : fetch_word AsanUbsan.M.loaded_segments (0xa2fd8 : word) = Some W_a2f90.
Proof. vm_refl. Qed.
Lemma D_a2f90 : decode_any W_a2f90 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f94 : bv 32 := 0x5f8000ef.
Lemma F_a2f94 : fetch_word AsanUbsan.M.loaded_segments (0xa2fdc : word) = Some W_a2f94.
Proof. vm_refl. Qed.
Lemma D_a2f94 : decode_any W_a2f94 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f98 : bv 32 := 0x00050a93.
Lemma F_a2f98 : fetch_word AsanUbsan.M.loaded_segments (0xa2fe0 : word) = Some W_a2f98.
Proof. vm_refl. Qed.
Lemma D_a2f98 : decode_any W_a2f98 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f9c : bv 32 := 0x03950663.
Lemma F_a2f9c : fetch_word AsanUbsan.M.loaded_segments (0xa2fe4 : word) = Some W_a2f9c.
Proof. vm_refl. Qed.
Lemma D_a2f9c : decode_any W_a2f9c = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc8 : bv 32 := 0x00400537.
Lemma F_a2fc8 : fetch_word AsanUbsan.M.loaded_segments (0xa3010 : word) = Some W_a2fc8.
Proof. vm_refl. Qed.
Lemma D_a2fc8 : decode_any W_a2fc8 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fcc : bv 32 := 0x00a48533.
Lemma F_a2fcc : fetch_word AsanUbsan.M.loaded_segments (0xa3014 : word) = Some W_a2fcc.
Proof. vm_refl. Qed.
Lemma D_a2fcc : decode_any W_a2fcc = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fd0 : bv 32 := 0x00100593.
Lemma F_a2fd0 : fetch_word AsanUbsan.M.loaded_segments (0xa3018 : word) = Some W_a2fd0.
Proof. vm_refl. Qed.
Lemma D_a2fd0 : decode_any W_a2fd0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fd4 : bv 32 := 0x00b5252f.
Lemma F_a2fd4 : fetch_word AsanUbsan.M.loaded_segments (0xa301c : word) = Some W_a2fd4.
Proof. vm_refl. Qed.
Lemma D_a2fd4 : decode_any W_a2fd4 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fd8 : bv 32 := 0x0015051b.
Lemma F_a2fd8 : fetch_word AsanUbsan.M.loaded_segments (0xa3020 : word) = Some W_a2fd8.
Proof. vm_refl. Qed.
Lemma D_a2fd8 : decode_any W_a2fd8 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fdc : bv 32 := 0x02051493.
Lemma F_a2fdc : fetch_word AsanUbsan.M.loaded_segments (0xa3024 : word) = Some W_a2fdc.
Proof. vm_refl. Qed.
Lemma D_a2fdc : decode_any W_a2fdc = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fe0 : bv 32 := 0x0204d493.
Lemma F_a2fe0 : fetch_word AsanUbsan.M.loaded_segments (0xa3028 : word) = Some W_a2fe0.
Proof. vm_refl. Qed.
Lemma D_a2fe0 : decode_any W_a2fe0 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fe4 : bv 32 := 0x08054663.
Lemma F_a2fe4 : fetch_word AsanUbsan.M.loaded_segments (0xa302c : word) = Some W_a2fe4.
Proof. vm_refl. Qed.
Lemma D_a2fe4 : decode_any W_a2fe4 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fe8 : bv 32 := 0x00050b93.
Lemma F_a2fe8 : fetch_word AsanUbsan.M.loaded_segments (0xa3030 : word) = Some W_a2fe8.
Proof. vm_refl. Qed.
Lemma D_a2fe8 : decode_any W_a2fe8 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fec : bv 32 := 0x0104d593.
Lemma F_a2fec : fetch_word AsanUbsan.M.loaded_segments (0xa3034 : word) = Some W_a2fec.
Proof. vm_refl. Qed.
Lemma D_a2fec : decode_any W_a2fec = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ff0 : bv 32 := 0x00359513.
Lemma F_a2ff0 : fetch_word AsanUbsan.M.loaded_segments (0xa3038 : word) = Some W_a2ff0.
Proof. vm_refl. Qed.
Lemma D_a2ff0 : decode_any W_a2ff0 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ff4 : bv 32 := 0x00ac0533.
Lemma F_a2ff4 : fetch_word AsanUbsan.M.loaded_segments (0xa303c : word) = Some W_a2ff4.
Proof. vm_refl. Qed.
Lemma D_a2ff4 : decode_any W_a2ff4 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ff8 : bv 32 := 0x00053503.
Lemma F_a2ff8 : fetch_word AsanUbsan.M.loaded_segments (0xa3040 : word) = Some W_a2ff8.
Proof. vm_refl. Qed.
Lemma D_a2ff8 : decode_any W_a2ff8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ffc : bv 32 := 0x08050a63.
Lemma F_a2ffc : fetch_word AsanUbsan.M.loaded_segments (0xa3044 : word) = Some W_a2ffc.
Proof. vm_refl. Qed.
Lemma D_a2ffc : decode_any W_a2ffc = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

