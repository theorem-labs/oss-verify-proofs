(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_56000 : bv 32 := 0x0005b517.
Lemma F_56000 : fetch_word AsanUbsan.M.loaded_segments (0x56000 : word) = Some W_56000.
Proof. vm_refl. Qed.
Lemma D_56000 : decode_any W_56000 = Some (Auipc 10 91, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56004 : bv 32 := 0x41c50503.
Lemma F_56004 : fetch_word AsanUbsan.M.loaded_segments (0x56004 : word) = Some W_56004.
Proof. vm_refl. Qed.
Lemma D_56004 : decode_any W_56004 = Some (Load SZ1 true 10 10 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56008 : bv 32 := 0x0230000f.
Lemma F_56008 : fetch_word AsanUbsan.M.loaded_segments (0x56008 : word) = Some W_56008.
Proof. vm_refl. Qed.
Lemma D_56008 : decode_any W_56008 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5600c : bv 32 := 0x00a03533.
Lemma F_5600c : fetch_word AsanUbsan.M.loaded_segments (0x5600c : word) = Some W_5600c.
Proof. vm_refl. Qed.
Lemma D_5600c : decode_any W_5600c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56010 : bv 32 := 0x00008067.
Lemma F_56010 : fetch_word AsanUbsan.M.loaded_segments (0x56010 : word) = Some W_56010.
Proof. vm_refl. Qed.
Lemma D_56010 : decode_any W_56010 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
