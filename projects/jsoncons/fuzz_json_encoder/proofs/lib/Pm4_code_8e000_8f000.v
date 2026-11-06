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
Definition W_8e000 : bv 32 := 0x00008067.
Lemma F_8e000 : fetch_word Asan.M.loaded_segments (0x8e050 : word) = Some W_8e000.
Proof. vm_refl. Qed.
Lemma D_8e000 : decode_any W_8e000 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e3d0 : bv 32 := 0x0015e517.
Lemma F_8e3d0 : fetch_word Asan.M.loaded_segments (0x8e420 : word) = Some W_8e3d0.
Proof. vm_refl. Qed.
Lemma D_8e3d0 : decode_any W_8e3d0 = Some (Auipc 10 350, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e3d4 : bv 32 := 0xd4150503.
Lemma F_8e3d4 : fetch_word Asan.M.loaded_segments (0x8e424 : word) = Some W_8e3d4.
Proof. vm_refl. Qed.
Lemma D_8e3d4 : decode_any W_8e3d4 = Some (Load SZ1 true 10 10 3393, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e3d8 : bv 32 := 0x00a03533.
Lemma F_8e3d8 : fetch_word Asan.M.loaded_segments (0x8e428 : word) = Some W_8e3d8.
Proof. vm_refl. Qed.
Lemma D_8e3d8 : decode_any W_8e3d8 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e3dc : bv 32 := 0x00008067.
Lemma F_8e3dc : fetch_word Asan.M.loaded_segments (0x8e42c : word) = Some W_8e3dc.
Proof. vm_refl. Qed.
Lemma D_8e3dc : decode_any W_8e3dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e3f8 : bv 32 := 0x0015e517.
Lemma F_8e3f8 : fetch_word Asan.M.loaded_segments (0x8e448 : word) = Some W_8e3f8.
Proof. vm_refl. Qed.
Lemma D_8e3f8 : decode_any W_8e3f8 = Some (Auipc 10 350, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e3fc : bv 32 := 0xd1a50503.
Lemma F_8e3fc : fetch_word Asan.M.loaded_segments (0x8e44c : word) = Some W_8e3fc.
Proof. vm_refl. Qed.
Lemma D_8e3fc : decode_any W_8e3fc = Some (Load SZ1 true 10 10 3354, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e400 : bv 32 := 0x00a03533.
Lemma F_8e400 : fetch_word Asan.M.loaded_segments (0x8e450 : word) = Some W_8e400.
Proof. vm_refl. Qed.
Lemma D_8e400 : decode_any W_8e400 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e404 : bv 32 := 0x00008067.
Lemma F_8e404 : fetch_word Asan.M.loaded_segments (0x8e454 : word) = Some W_8e404.
Proof. vm_refl. Qed.
Lemma D_8e404 : decode_any W_8e404 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

