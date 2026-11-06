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
Definition W_99e48 : bv 32 := 0xf7010113.
Lemma F_99e48 : fetch_word AsanUbsan.M.loaded_segments (0x99e90 : word) = Some W_99e48.
Proof. vm_refl. Qed.
Lemma D_99e48 : decode_any W_99e48 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e4c : bv 32 := 0x08113423.
Lemma F_99e4c : fetch_word AsanUbsan.M.loaded_segments (0x99e94 : word) = Some W_99e4c.
Proof. vm_refl. Qed.
Lemma D_99e4c : decode_any W_99e4c = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e50 : bv 32 := 0x08813023.
Lemma F_99e50 : fetch_word AsanUbsan.M.loaded_segments (0x99e98 : word) = Some W_99e50.
Proof. vm_refl. Qed.
Lemma D_99e50 : decode_any W_99e50 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e54 : bv 32 := 0x06913c23.
Lemma F_99e54 : fetch_word AsanUbsan.M.loaded_segments (0x99e9c : word) = Some W_99e54.
Proof. vm_refl. Qed.
Lemma D_99e54 : decode_any W_99e54 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e58 : bv 32 := 0x07213823.
Lemma F_99e58 : fetch_word AsanUbsan.M.loaded_segments (0x99ea0 : word) = Some W_99e58.
Proof. vm_refl. Qed.
Lemma D_99e58 : decode_any W_99e58 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e5c : bv 32 := 0x07313423.
Lemma F_99e5c : fetch_word AsanUbsan.M.loaded_segments (0x99ea4 : word) = Some W_99e5c.
Proof. vm_refl. Qed.
Lemma D_99e5c : decode_any W_99e5c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e60 : bv 32 := 0x07413023.
Lemma F_99e60 : fetch_word AsanUbsan.M.loaded_segments (0x99ea8 : word) = Some W_99e60.
Proof. vm_refl. Qed.
Lemma D_99e60 : decode_any W_99e60 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e64 : bv 32 := 0x05513c23.
Lemma F_99e64 : fetch_word AsanUbsan.M.loaded_segments (0x99eac : word) = Some W_99e64.
Proof. vm_refl. Qed.
Lemma D_99e64 : decode_any W_99e64 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e68 : bv 32 := 0x05613823.
Lemma F_99e68 : fetch_word AsanUbsan.M.loaded_segments (0x99eb0 : word) = Some W_99e68.
Proof. vm_refl. Qed.
Lemma D_99e68 : decode_any W_99e68 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e6c : bv 32 := 0x05713423.
Lemma F_99e6c : fetch_word AsanUbsan.M.loaded_segments (0x99eb4 : word) = Some W_99e6c.
Proof. vm_refl. Qed.
Lemma D_99e6c : decode_any W_99e6c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e70 : bv 32 := 0x05813023.
Lemma F_99e70 : fetch_word AsanUbsan.M.loaded_segments (0x99eb8 : word) = Some W_99e70.
Proof. vm_refl. Qed.
Lemma D_99e70 : decode_any W_99e70 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e74 : bv 32 := 0x03913c23.
Lemma F_99e74 : fetch_word AsanUbsan.M.loaded_segments (0x99ebc : word) = Some W_99e74.
Proof. vm_refl. Qed.
Lemma D_99e74 : decode_any W_99e74 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e78 : bv 32 := 0x03a13823.
Lemma F_99e78 : fetch_word AsanUbsan.M.loaded_segments (0x99ec0 : word) = Some W_99e78.
Proof. vm_refl. Qed.
Lemma D_99e78 : decode_any W_99e78 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e7c : bv 32 := 0x03b13423.
Lemma F_99e7c : fetch_word AsanUbsan.M.loaded_segments (0x99ec4 : word) = Some W_99e7c.
Proof. vm_refl. Qed.
Lemma D_99e7c : decode_any W_99e7c = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e80 : bv 32 := 0x00058913.
Lemma F_99e80 : fetch_word AsanUbsan.M.loaded_segments (0x99ec8 : word) = Some W_99e80.
Proof. vm_refl. Qed.
Lemma D_99e80 : decode_any W_99e80 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e84 : bv 32 := 0x000ca597.
Lemma F_99e84 : fetch_word AsanUbsan.M.loaded_segments (0x99ecc : word) = Some W_99e84.
Proof. vm_refl. Qed.
Lemma D_99e84 : decode_any W_99e84 = Some (Auipc 11 202, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e88 : bv 32 := 0x63c5b583.
Lemma F_99e88 : fetch_word AsanUbsan.M.loaded_segments (0x99ed0 : word) = Some W_99e88.
Proof. vm_refl. Qed.
Lemma D_99e88 : decode_any W_99e88 = Some (Load SZ8 true 11 11 1596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e8c : bv 32 := 0x0895c583.
Lemma F_99e8c : fetch_word AsanUbsan.M.loaded_segments (0x99ed4 : word) = Some W_99e8c.
Proof. vm_refl. Qed.
Lemma D_99e8c : decode_any W_99e8c = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e90 : bv 32 := 0x18058a63.
Lemma F_99e90 : fetch_word AsanUbsan.M.loaded_segments (0x99ed8 : word) = Some W_99e90.
Proof. vm_refl. Qed.
Lemma D_99e90 : decode_any W_99e90 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e94 : bv 32 := 0x00050993.
Lemma F_99e94 : fetch_word AsanUbsan.M.loaded_segments (0x99edc : word) = Some W_99e94.
Proof. vm_refl. Qed.
Lemma D_99e94 : decode_any W_99e94 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e98 : bv 32 := 0x000ca517.
Lemma F_99e98 : fetch_word AsanUbsan.M.loaded_segments (0x99ee0 : word) = Some W_99e98.
Proof. vm_refl. Qed.
Lemma D_99e98 : decode_any W_99e98 = Some (Auipc 10 202, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e9c : bv 32 := 0x68853d03.
Lemma F_99e9c : fetch_word AsanUbsan.M.loaded_segments (0x99ee4 : word) = Some W_99e9c.
Proof. vm_refl. Qed.
Lemma D_99e9c : decode_any W_99e9c = Some (Load SZ8 true 26 10 1672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ea0 : bv 32 := 0x0009ba03.
Lemma F_99ea0 : fetch_word AsanUbsan.M.loaded_segments (0x99ee8 : word) = Some W_99ea0.
Proof. vm_refl. Qed.
Lemma D_99ea0 : decode_any W_99ea0 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ea4 : bv 32 := 0x000cb517.
Lemma F_99ea4 : fetch_word AsanUbsan.M.loaded_segments (0x99eec : word) = Some W_99ea4.
Proof. vm_refl. Qed.
Lemma D_99ea4 : decode_any W_99ea4 = Some (Auipc 10 203, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ea8 : bv 32 := 0x000d2583.
Lemma F_99ea8 : fetch_word AsanUbsan.M.loaded_segments (0x99ef0 : word) = Some W_99ea8.
Proof. vm_refl. Qed.
Lemma D_99ea8 : decode_any W_99ea8 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99eac : bv 32 := 0x45c53a83.
Lemma F_99eac : fetch_word AsanUbsan.M.loaded_segments (0x99ef4 : word) = Some W_99eac.
Proof. vm_refl. Qed.
Lemma D_99eac : decode_any W_99eac = Some (Load SZ8 true 21 10 1116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99eb0 : bv 32 := 0x00300513.
Lemma F_99eb0 : fetch_word AsanUbsan.M.loaded_segments (0x99ef8 : word) = Some W_99eb0.
Proof. vm_refl. Qed.
Lemma D_99eb0 : decode_any W_99eb0 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99eb4 : bv 32 := 0x004a8ab3.
Lemma F_99eb4 : fetch_word AsanUbsan.M.loaded_segments (0x99efc : word) = Some W_99eb4.
Proof. vm_refl. Qed.
Lemma D_99eb4 : decode_any W_99eb4 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99eb8 : bv 32 := 0x1ea5fa63.
Lemma F_99eb8 : fetch_word AsanUbsan.M.loaded_segments (0x99f00 : word) = Some W_99eb8.
Proof. vm_refl. Qed.
Lemma D_99eb8 : decode_any W_99eb8 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ebc : bv 32 := 0x000abb03.
Lemma F_99ebc : fetch_word AsanUbsan.M.loaded_segments (0x99f04 : word) = Some W_99ebc.
Proof. vm_refl. Qed.
Lemma D_99ebc : decode_any W_99ebc = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ec0 : bv 32 := 0xfff00513.
Lemma F_99ec0 : fetch_word AsanUbsan.M.loaded_segments (0x99f08 : word) = Some W_99ec0.
Proof. vm_refl. Qed.
Lemma D_99ec0 : decode_any W_99ec0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ec4 : bv 32 := 0x0230000f.
Lemma F_99ec4 : fetch_word AsanUbsan.M.loaded_segments (0x99f0c : word) = Some W_99ec4.
Proof. vm_refl. Qed.
Lemma D_99ec4 : decode_any W_99ec4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ec8 : bv 32 := 0x14ab0e63.
Lemma F_99ec8 : fetch_word AsanUbsan.M.loaded_segments (0x99f10 : word) = Some W_99ec8.
Proof. vm_refl. Qed.
Lemma D_99ec8 : decode_any W_99ec8 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ecc : bv 32 := 0x080b1263.
Lemma F_99ecc : fetch_word AsanUbsan.M.loaded_segments (0x99f14 : word) = Some W_99ecc.
Proof. vm_refl. Qed.
Lemma D_99ecc : decode_any W_99ecc = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99f50 : bv 32 := 0x0c0b0a63.
Lemma F_99f50 : fetch_word AsanUbsan.M.loaded_segments (0x99f98 : word) = Some W_99f50.
Proof. vm_refl. Qed.
Lemma D_99f50 : decode_any W_99f50 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99f54 : bv 32 := 0x00c13823.
Lemma F_99f54 : fetch_word AsanUbsan.M.loaded_segments (0x99f9c : word) = Some W_99f54.
Proof. vm_refl. Qed.
Lemma D_99f54 : decode_any W_99f54 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99f58 : bv 32 := 0x00d13c23.
Lemma F_99f58 : fetch_word AsanUbsan.M.loaded_segments (0x99fa0 : word) = Some W_99f58.
Proof. vm_refl. Qed.
Lemma D_99f58 : decode_any W_99f58 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99f5c : bv 32 := 0x0ff00513.
Lemma F_99f5c : fetch_word AsanUbsan.M.loaded_segments (0x99fa4 : word) = Some W_99f5c.
Proof. vm_refl. Qed.
Lemma D_99f5c : decode_any W_99f5c = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99f60 : bv 32 := 0x0aaa6863.
Lemma F_99f60 : fetch_word AsanUbsan.M.loaded_segments (0x99fa8 : word) = Some W_99f60.
Proof. vm_refl. Qed.
Lemma D_99f60 : decode_any W_99f60 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

