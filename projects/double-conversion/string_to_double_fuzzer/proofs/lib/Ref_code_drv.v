(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3299c : bv 32 := 0x00090517.
Lemma F_3299c : fetch_word ImgP.M.loaded_segments (0x3299c : word) = Some W_3299c.
Proof. vm_refl. Qed.
Lemma D_3299c : decode_any W_3299c = Some (Auipc 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_329a0 : bv 32 := 0x55854503.
Lemma F_329a0 : fetch_word ImgP.M.loaded_segments (0x329a0 : word) = Some W_329a0.
Proof. vm_refl. Qed.
Lemma D_329a0 : decode_any W_329a0 = Some (Load SZ1 false 10 10 1368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_329a4 : bv 32 := 0x00051463.
Lemma F_329a4 : fetch_word ImgP.M.loaded_segments (0x329a4 : word) = Some W_329a4.
Proof. vm_refl. Qed.
Lemma D_329a4 : decode_any W_329a4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_329a8 : bv 32 := 0x00008067.
Lemma F_329a8 : fetch_word ImgP.M.loaded_segments (0x329a8 : word) = Some W_329a8.
Proof. vm_refl. Qed.
Lemma D_329a8 : decode_any W_329a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96040 : bv 32 := 0x00050067.
Lemma F_96040 : fetch_word ImgP.M.loaded_segments (0x96040 : word) = Some W_96040.
Proof. vm_refl. Qed.
Lemma D_96040 : decode_any W_96040 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.
