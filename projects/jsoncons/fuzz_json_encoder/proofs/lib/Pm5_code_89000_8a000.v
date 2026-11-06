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
Definition W_89008 : bv 32 := 0x000e5517.
Lemma F_89008 : fetch_word AsanUbsan.M.loaded_segments (0x89050 : word) = Some W_89008.
Proof. vm_refl. Qed.
Lemma D_89008 : decode_any W_89008 = Some (Auipc 10 229, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8900c : bv 32 := 0x44850503.
Lemma F_8900c : fetch_word AsanUbsan.M.loaded_segments (0x89054 : word) = Some W_8900c.
Proof. vm_refl. Qed.
Lemma D_8900c : decode_any W_8900c = Some (Load SZ1 true 10 10 1096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89010 : bv 32 := 0x0230000f.
Lemma F_89010 : fetch_word AsanUbsan.M.loaded_segments (0x89058 : word) = Some W_89010.
Proof. vm_refl. Qed.
Lemma D_89010 : decode_any W_89010 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89014 : bv 32 := 0xfff50513.
Lemma F_89014 : fetch_word AsanUbsan.M.loaded_segments (0x8905c : word) = Some W_89014.
Proof. vm_refl. Qed.
Lemma D_89014 : decode_any W_89014 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89018 : bv 32 := 0x00153513.
Lemma F_89018 : fetch_word AsanUbsan.M.loaded_segments (0x89060 : word) = Some W_89018.
Proof. vm_refl. Qed.
Lemma D_89018 : decode_any W_89018 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8901c : bv 32 := 0x00008067.
Lemma F_8901c : fetch_word AsanUbsan.M.loaded_segments (0x89064 : word) = Some W_8901c.
Proof. vm_refl. Qed.
Lemma D_8901c : decode_any W_8901c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f18 : bv 32 := 0xff010113.
Lemma F_89f18 : fetch_word AsanUbsan.M.loaded_segments (0x89f60 : word) = Some W_89f18.
Proof. vm_refl. Qed.
Lemma D_89f18 : decode_any W_89f18 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f1c : bv 32 := 0x00113423.
Lemma F_89f1c : fetch_word AsanUbsan.M.loaded_segments (0x89f64 : word) = Some W_89f1c.
Proof. vm_refl. Qed.
Lemma D_89f1c : decode_any W_89f1c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f20 : bv 32 := 0x00813023.
Lemma F_89f20 : fetch_word AsanUbsan.M.loaded_segments (0x89f68 : word) = Some W_89f20.
Proof. vm_refl. Qed.
Lemma D_89f20 : decode_any W_89f20 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f24 : bv 32 := 0x000e4517.
Lemma F_89f24 : fetch_word AsanUbsan.M.loaded_segments (0x89f6c : word) = Some W_89f24.
Proof. vm_refl. Qed.
Lemma D_89f24 : decode_any W_89f24 = Some (Auipc 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f28 : bv 32 := 0x52c50413.
Lemma F_89f28 : fetch_word AsanUbsan.M.loaded_segments (0x89f70 : word) = Some W_89f28.
Proof. vm_refl. Qed.
Lemma D_89f28 : decode_any W_89f28 = Some (OpImm ALU_ADD 8 10 1324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f2c : bv 32 := 0x00040583.
Lemma F_89f2c : fetch_word AsanUbsan.M.loaded_segments (0x89f74 : word) = Some W_89f2c.
Proof. vm_refl. Qed.
Lemma D_89f2c : decode_any W_89f2c = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f30 : bv 32 := 0x00100513.
Lemma F_89f30 : fetch_word AsanUbsan.M.loaded_segments (0x89f78 : word) = Some W_89f30.
Proof. vm_refl. Qed.
Lemma D_89f30 : decode_any W_89f30 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f34 : bv 32 := 0x0230000f.
Lemma F_89f34 : fetch_word AsanUbsan.M.loaded_segments (0x89f7c : word) = Some W_89f34.
Proof. vm_refl. Qed.
Lemma D_89f34 : decode_any W_89f34 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f38 : bv 32 := 0x00a59a63.
Lemma F_89f38 : fetch_word AsanUbsan.M.loaded_segments (0x89f80 : word) = Some W_89f38.
Proof. vm_refl. Qed.
Lemma D_89f38 : decode_any W_89f38 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f3c : bv 32 := 0x00813083.
Lemma F_89f3c : fetch_word AsanUbsan.M.loaded_segments (0x89f84 : word) = Some W_89f3c.
Proof. vm_refl. Qed.
Lemma D_89f3c : decode_any W_89f3c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f40 : bv 32 := 0x00013403.
Lemma F_89f40 : fetch_word AsanUbsan.M.loaded_segments (0x89f88 : word) = Some W_89f40.
Proof. vm_refl. Qed.
Lemma D_89f40 : decode_any W_89f40 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f44 : bv 32 := 0x01010113.
Lemma F_89f44 : fetch_word AsanUbsan.M.loaded_segments (0x89f8c : word) = Some W_89f44.
Proof. vm_refl. Qed.
Lemma D_89f44 : decode_any W_89f44 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89f48 : bv 32 := 0x00008067.
Lemma F_89f48 : fetch_word AsanUbsan.M.loaded_segments (0x89f90 : word) = Some W_89f48.
Proof. vm_refl. Qed.
Lemma D_89f48 : decode_any W_89f48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

