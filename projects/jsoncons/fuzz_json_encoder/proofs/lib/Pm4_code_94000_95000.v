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
Definition W_941b8 : bv 32 := 0xfffff637.
Lemma F_941b8 : fetch_word Asan.M.loaded_segments (0x94208 : word) = Some W_941b8.
Proof. vm_refl. Qed.
Lemma D_941b8 : decode_any W_941b8 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941bc : bv 32 := 0x0016069b.
Lemma F_941bc : fetch_word Asan.M.loaded_segments (0x9420c : word) = Some W_941bc.
Proof. vm_refl. Qed.
Lemma D_941bc : decode_any W_941bc = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941c0 : bv 32 := 0x00d56863.
Lemma F_941c0 : fetch_word Asan.M.loaded_segments (0x94210 : word) = Some W_941c0.
Proof. vm_refl. Qed.
Lemma D_941c0 : decode_any W_941c0 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941d0 : bv 32 := 0x00a63533.
Lemma F_941d0 : fetch_word Asan.M.loaded_segments (0x94220 : word) = Some W_941d0.
Proof. vm_refl. Qed.
Lemma D_941d0 : decode_any W_941d0 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941d4 : bv 32 := 0x00008067.
Lemma F_941d4 : fetch_word Asan.M.loaded_segments (0x94224 : word) = Some W_941d4.
Proof. vm_refl. Qed.
Lemma D_941d4 : decode_any W_941d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941d8 : bv 32 := 0x0de00893.
Lemma F_941d8 : fetch_word Asan.M.loaded_segments (0x94228 : word) = Some W_941d8.
Proof. vm_refl. Qed.
Lemma D_941d8 : decode_any W_941d8 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941dc : bv 32 := 0x00000073.
Lemma F_941dc : fetch_word Asan.M.loaded_segments (0x9422c : word) = Some W_941dc.
Proof. vm_refl. Qed.
Lemma D_941dc : decode_any W_941dc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_941dc : is_ecall W_941dc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_941e0 : bv 32 := 0x00008067.
Lemma F_941e0 : fetch_word Asan.M.loaded_segments (0x94230 : word) = Some W_941e0.
Proof. vm_refl. Qed.
Lemma D_941e0 : decode_any W_941e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941e4 : bv 32 := 0x0d700893.
Lemma F_941e4 : fetch_word Asan.M.loaded_segments (0x94234 : word) = Some W_941e4.
Proof. vm_refl. Qed.
Lemma D_941e4 : decode_any W_941e4 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941e8 : bv 32 := 0x00000073.
Lemma F_941e8 : fetch_word Asan.M.loaded_segments (0x94238 : word) = Some W_941e8.
Proof. vm_refl. Qed.
Lemma D_941e8 : decode_any W_941e8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_941e8 : is_ecall W_941e8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_941ec : bv 32 := 0x00008067.
Lemma F_941ec : fetch_word Asan.M.loaded_segments (0x9423c : word) = Some W_941ec.
Proof. vm_refl. Qed.
Lemma D_941ec : decode_any W_941ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94200 : bv 32 := 0x000cd697.
Lemma F_94200 : fetch_word Asan.M.loaded_segments (0x94250 : word) = Some W_94200.
Proof. vm_refl. Qed.
Lemma D_94200 : decode_any W_94200 = Some (Auipc 13 205, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94204 : bv 32 := 0xa086b683.
Lemma F_94204 : fetch_word Asan.M.loaded_segments (0x94254 : word) = Some W_94204.
Proof. vm_refl. Qed.
Lemma D_94204 : decode_any W_94204 = Some (Load SZ8 true 13 13 2568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94208 : bv 32 := 0x00068a63.
Lemma F_94208 : fetch_word Asan.M.loaded_segments (0x94258 : word) = Some W_94208.
Proof. vm_refl. Qed.
Lemma D_94208 : decode_any W_94208 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9420c : bv 32 := 0x00400693.
Lemma F_9420c : fetch_word Asan.M.loaded_segments (0x9425c : word) = Some W_9420c.
Proof. vm_refl. Qed.
Lemma D_9420c : decode_any W_9420c = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94210 : bv 32 := 0x00d60663.
Lemma F_94210 : fetch_word Asan.M.loaded_segments (0x94260 : word) = Some W_94210.
Proof. vm_refl. Qed.
Lemma D_94210 : decode_any W_94210 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9421c : bv 32 := 0x0e900893.
Lemma F_9421c : fetch_word Asan.M.loaded_segments (0x9426c : word) = Some W_9421c.
Proof. vm_refl. Qed.
Lemma D_9421c : decode_any W_9421c = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94220 : bv 32 := 0x00000073.
Lemma F_94220 : fetch_word Asan.M.loaded_segments (0x94270 : word) = Some W_94220.
Proof. vm_refl. Qed.
Lemma D_94220 : decode_any W_94220 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_94220 : is_ecall W_94220 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_94224 : bv 32 := 0x0005051b.
Lemma F_94224 : fetch_word Asan.M.loaded_segments (0x94274 : word) = Some W_94224.
Proof. vm_refl. Qed.
Lemma D_94224 : decode_any W_94224 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94228 : bv 32 := 0x00008067.
Lemma F_94228 : fetch_word Asan.M.loaded_segments (0x94278 : word) = Some W_94228.
Proof. vm_refl. Qed.
Lemma D_94228 : decode_any W_94228 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

