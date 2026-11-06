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
Definition Wx_83d60 : bv 32 := 0x00058613.
Lemma Fx_83d60 : fetch_word Asan.M.loaded_segments (0x83db0 : word) = Some Wx_83d60.
Proof. vm_refl. Qed.
Lemma Dx_83d60 : decode_any Wx_83d60 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83d64 : bv 32 := 0x000dd597.
Lemma Fx_83d64 : fetch_word Asan.M.loaded_segments (0x83db4 : word) = Some Wx_83d64.
Proof. vm_refl. Qed.
Lemma Dx_83d64 : decode_any Wx_83d64 = Some (Auipc 11 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83d68 : bv 32 := 0xe845b583.
Lemma Fx_83d68 : fetch_word Asan.M.loaded_segments (0x83db8 : word) = Some Wx_83d68.
Proof. vm_refl. Qed.
Lemma Dx_83d68 : decode_any Wx_83d68 = Some (Load SZ8 true 11 11 3716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83d6c : bv 32 := 0x0005b303.
Lemma Fx_83d6c : fetch_word Asan.M.loaded_segments (0x83dbc : word) = Some Wx_83d6c.
Proof. vm_refl. Qed.
Lemma Dx_83d6c : decode_any Wx_83d6c = Some (Load SZ8 true 6 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83d70 : bv 32 := 0x00000593.
Lemma Fx_83d70 : fetch_word Asan.M.loaded_segments (0x83dc0 : word) = Some Wx_83d70.
Proof. vm_refl. Qed.
Lemma Dx_83d70 : decode_any Wx_83d70 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83d74 : bv 32 := 0x00030067.
Lemma Fx_83d74 : fetch_word Asan.M.loaded_segments (0x83dc4 : word) = Some Wx_83d74.
Proof. vm_refl. Qed.
Lemma Dx_83d74 : decode_any Wx_83d74 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e68 : bv 32 := 0x000dd617.
Lemma Fx_83e68 : fetch_word Asan.M.loaded_segments (0x83eb8 : word) = Some Wx_83e68.
Proof. vm_refl. Qed.
Lemma Dx_83e68 : decode_any Wx_83e68 = Some (Auipc 12 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e6c : bv 32 := 0xd8063603.
Lemma Fx_83e6c : fetch_word Asan.M.loaded_segments (0x83ebc : word) = Some Wx_83e6c.
Proof. vm_refl. Qed.
Lemma Dx_83e6c : decode_any Wx_83e6c = Some (Load SZ8 true 12 12 3456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e70 : bv 32 := 0x00063303.
Lemma Fx_83e70 : fetch_word Asan.M.loaded_segments (0x83ec0 : word) = Some Wx_83e70.
Proof. vm_refl. Qed.
Lemma Dx_83e70 : decode_any Wx_83e70 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e74 : bv 32 := 0x00058613.
Lemma Fx_83e74 : fetch_word Asan.M.loaded_segments (0x83ec4 : word) = Some Wx_83e74.
Proof. vm_refl. Qed.
Lemma Dx_83e74 : decode_any Wx_83e74 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e78 : bv 32 := 0x0f500593.
Lemma Fx_83e78 : fetch_word Asan.M.loaded_segments (0x83ec8 : word) = Some Wx_83e78.
Proof. vm_refl. Qed.
Lemma Dx_83e78 : decode_any Wx_83e78 = Some (OpImm ALU_ADD 11 0 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e7c : bv 32 := 0x00030067.
Lemma Fx_83e7c : fetch_word Asan.M.loaded_segments (0x83ecc : word) = Some Wx_83e7c.
Proof. vm_refl. Qed.
Lemma Dx_83e7c : decode_any Wx_83e7c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e80 : bv 32 := 0x000dd617.
Lemma Fx_83e80 : fetch_word Asan.M.loaded_segments (0x83ed0 : word) = Some Wx_83e80.
Proof. vm_refl. Qed.
Lemma Dx_83e80 : decode_any Wx_83e80 = Some (Auipc 12 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e84 : bv 32 := 0xd6863603.
Lemma Fx_83e84 : fetch_word Asan.M.loaded_segments (0x83ed4 : word) = Some Wx_83e84.
Proof. vm_refl. Qed.
Lemma Dx_83e84 : decode_any Wx_83e84 = Some (Load SZ8 true 12 12 3432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e88 : bv 32 := 0x00063303.
Lemma Fx_83e88 : fetch_word Asan.M.loaded_segments (0x83ed8 : word) = Some Wx_83e88.
Proof. vm_refl. Qed.
Lemma Dx_83e88 : decode_any Wx_83e88 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e8c : bv 32 := 0x00058613.
Lemma Fx_83e8c : fetch_word Asan.M.loaded_segments (0x83edc : word) = Some Wx_83e8c.
Proof. vm_refl. Qed.
Lemma Dx_83e8c : decode_any Wx_83e8c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e90 : bv 32 := 0x0f800593.
Lemma Fx_83e90 : fetch_word Asan.M.loaded_segments (0x83ee0 : word) = Some Wx_83e90.
Proof. vm_refl. Qed.
Lemma Dx_83e90 : decode_any Wx_83e90 = Some (OpImm ALU_ADD 11 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83e94 : bv 32 := 0x00030067.
Lemma Fx_83e94 : fetch_word Asan.M.loaded_segments (0x83ee4 : word) = Some Wx_83e94.
Proof. vm_refl. Qed.
Lemma Dx_83e94 : decode_any Wx_83e94 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

