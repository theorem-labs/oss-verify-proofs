(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_607e8 : bv 32 := 0xfe010113.
Lemma F_607e8 : fetch_word Ubsan.M.loaded_segments (0x607e8 : word) = Some W_607e8.
Proof. vm_refl. Qed.
Lemma D_607e8 : decode_any W_607e8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607ec : bv 32 := 0x00113c23.
Lemma F_607ec : fetch_word Ubsan.M.loaded_segments (0x607ec : word) = Some W_607ec.
Proof. vm_refl. Qed.
Lemma D_607ec : decode_any W_607ec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607f0 : bv 32 := 0x00813823.
Lemma F_607f0 : fetch_word Ubsan.M.loaded_segments (0x607f0 : word) = Some W_607f0.
Proof. vm_refl. Qed.
Lemma D_607f0 : decode_any W_607f0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607f4 : bv 32 := 0x00913423.
Lemma F_607f4 : fetch_word Ubsan.M.loaded_segments (0x607f4 : word) = Some W_607f4.
Proof. vm_refl. Qed.
Lemma D_607f4 : decode_any W_607f4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607f8 : bv 32 := 0x00058413.
Lemma F_607f8 : fetch_word Ubsan.M.loaded_segments (0x607f8 : word) = Some W_607f8.
Proof. vm_refl. Qed.
Lemma D_607f8 : decode_any W_607f8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607fc : bv 32 := 0x00050493.
Lemma F_607fc : fetch_word Ubsan.M.loaded_segments (0x607fc : word) = Some W_607fc.
Proof. vm_refl. Qed.
Lemma D_607fc : decode_any W_607fc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60800 : bv 32 := 0x00000593.
Lemma F_60800 : fetch_word Ubsan.M.loaded_segments (0x60800 : word) = Some W_60800.
Proof. vm_refl. Qed.
Lemma D_60800 : decode_any W_60800 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60804 : bv 32 := 0x00040613.
Lemma F_60804 : fetch_word Ubsan.M.loaded_segments (0x60804 : word) = Some W_60804.
Proof. vm_refl. Qed.
Lemma D_60804 : decode_any W_60804 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60808 : bv 32 := 0xfa4ff0ef.
Lemma F_60808 : fetch_word Ubsan.M.loaded_segments (0x60808 : word) = Some W_60808.
Proof. vm_refl. Qed.
Lemma D_60808 : decode_any W_60808 = Some (Jal 1 2095012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6080c : bv 32 := 0x00050463.
Lemma F_6080c : fetch_word Ubsan.M.loaded_segments (0x6080c : word) = Some W_6080c.
Proof. vm_refl. Qed.
Lemma D_6080c : decode_any W_6080c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60810 : bv 32 := 0x40950433.
Lemma F_60810 : fetch_word Ubsan.M.loaded_segments (0x60810 : word) = Some W_60810.
Proof. vm_refl. Qed.
Lemma D_60810 : decode_any W_60810 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60814 : bv 32 := 0x00040513.
Lemma F_60814 : fetch_word Ubsan.M.loaded_segments (0x60814 : word) = Some W_60814.
Proof. vm_refl. Qed.
Lemma D_60814 : decode_any W_60814 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60818 : bv 32 := 0x01813083.
Lemma F_60818 : fetch_word Ubsan.M.loaded_segments (0x60818 : word) = Some W_60818.
Proof. vm_refl. Qed.
Lemma D_60818 : decode_any W_60818 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6081c : bv 32 := 0x01013403.
Lemma F_6081c : fetch_word Ubsan.M.loaded_segments (0x6081c : word) = Some W_6081c.
Proof. vm_refl. Qed.
Lemma D_6081c : decode_any W_6081c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60820 : bv 32 := 0x00813483.
Lemma F_60820 : fetch_word Ubsan.M.loaded_segments (0x60820 : word) = Some W_60820.
Proof. vm_refl. Qed.
Lemma D_60820 : decode_any W_60820 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60824 : bv 32 := 0x02010113.
Lemma F_60824 : fetch_word Ubsan.M.loaded_segments (0x60824 : word) = Some W_60824.
Proof. vm_refl. Qed.
Lemma D_60824 : decode_any W_60824 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60828 : bv 32 := 0x00008067.
Lemma F_60828 : fetch_word Ubsan.M.loaded_segments (0x60828 : word) = Some W_60828.
Proof. vm_refl. Qed.
Lemma D_60828 : decode_any W_60828 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
