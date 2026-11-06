(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

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
Definition W_56010 : bv 32 := 0x0005d517.
Lemma F_56010 : fetch_word Asan.M.loaded_segments (0x56010 : word) = Some W_56010.
Proof. vm_refl. Qed.
Lemma D_56010 : decode_any W_56010 = Some (Auipc 10 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56014 : bv 32 := 0xe4c50503.
Lemma F_56014 : fetch_word Asan.M.loaded_segments (0x56014 : word) = Some W_56014.
Proof. vm_refl. Qed.
Lemma D_56014 : decode_any W_56014 = Some (Load SZ1 true 10 10 3660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56018 : bv 32 := 0x0230000f.
Lemma F_56018 : fetch_word Asan.M.loaded_segments (0x56018 : word) = Some W_56018.
Proof. vm_refl. Qed.
Lemma D_56018 : decode_any W_56018 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5601c : bv 32 := 0x00a03533.
Lemma F_5601c : fetch_word Asan.M.loaded_segments (0x5601c : word) = Some W_5601c.
Proof. vm_refl. Qed.
Lemma D_5601c : decode_any W_5601c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56020 : bv 32 := 0x00008067.
Lemma F_56020 : fetch_word Asan.M.loaded_segments (0x56020 : word) = Some W_56020.
Proof. vm_refl. Qed.
Lemma D_56020 : decode_any W_56020 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
