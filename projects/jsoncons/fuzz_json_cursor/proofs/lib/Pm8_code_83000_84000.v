(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_83044 : bv 32 := 0x00000513.
Lemma F_83044 : fetch_word Asan.M.loaded_segments (0x83094 : word) = Some W_83044.
Proof. vm_refl. Qed.
Lemma D_83044 : decode_any W_83044 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83048 : bv 32 := 0x04813083.
Lemma F_83048 : fetch_word Asan.M.loaded_segments (0x83098 : word) = Some W_83048.
Proof. vm_refl. Qed.
Lemma D_83048 : decode_any W_83048 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8304c : bv 32 := 0x04013403.
Lemma F_8304c : fetch_word Asan.M.loaded_segments (0x8309c : word) = Some W_8304c.
Proof. vm_refl. Qed.
Lemma D_8304c : decode_any W_8304c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_83050 : bv 32 := 0x05010113.
Lemma F_83050 : fetch_word Asan.M.loaded_segments (0x830a0 : word) = Some W_83050.
Proof. vm_refl. Qed.
Lemma D_83050 : decode_any W_83050 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_83054 : bv 32 := 0x00008067.
Lemma F_83054 : fetch_word Asan.M.loaded_segments (0x830a4 : word) = Some W_83054.
Proof. vm_refl. Qed.
Lemma D_83054 : decode_any W_83054 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_830f4 : bv 32 := 0x000d9517.
Lemma F_830f4 : fetch_word Asan.M.loaded_segments (0x83144 : word) = Some W_830f4.
Proof. vm_refl. Qed.
Lemma D_830f4 : decode_any W_830f4 = Some (Auipc 10 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_830f8 : bv 32 := 0x0dc50513.
Lemma F_830f8 : fetch_word Asan.M.loaded_segments (0x83148 : word) = Some W_830f8.
Proof. vm_refl. Qed.
Lemma D_830f8 : decode_any W_830f8 = Some (OpImm ALU_ADD 10 10 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_830fc : bv 32 := 0x00054583.
Lemma F_830fc : fetch_word Asan.M.loaded_segments (0x8314c : word) = Some W_830fc.
Proof. vm_refl. Qed.
Lemma D_830fc : decode_any W_830fc = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83100 : bv 32 := 0x00058663.
Lemma F_83100 : fetch_word Asan.M.loaded_segments (0x83150 : word) = Some W_83100.
Proof. vm_refl. Qed.
Lemma D_83100 : decode_any W_83100 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_83104 : bv 32 := 0x00452503.
Lemma F_83104 : fetch_word Asan.M.loaded_segments (0x83154 : word) = Some W_83104.
Proof. vm_refl. Qed.
Lemma D_83104 : decode_any W_83104 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_83108 : bv 32 := 0x1d9c406f.
Lemma F_83108 : fetch_word Asan.M.loaded_segments (0x83158 : word) = Some W_83108.
Proof. vm_refl. Qed.
Lemma D_83108 : decode_any W_83108 = Some (Jal 0 805336, 4%Z).
Proof. vm_refl. Qed.

