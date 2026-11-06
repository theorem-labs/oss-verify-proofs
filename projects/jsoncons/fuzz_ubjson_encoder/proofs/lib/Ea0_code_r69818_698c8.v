(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_843dc : bv 32 := 0x02850583.
Lemma F_843dc : fetch_word Asan.M.loaded_segments (0x8442c : word) = Some W_843dc.
Proof. vm_refl. Qed.
Lemma D_843dc : decode_any W_843dc = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_843e0 : bv 32 := 0x0230000f.
Lemma F_843e0 : fetch_word Asan.M.loaded_segments (0x84430 : word) = Some W_843e0.
Proof. vm_refl. Qed.
Lemma D_843e0 : decode_any W_843e0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_843e4 : bv 32 := 0x02058c63.
Lemma F_843e4 : fetch_word Asan.M.loaded_segments (0x84434 : word) = Some W_843e4.
Proof. vm_refl. Qed.
Lemma D_843e4 : decode_any W_843e4 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8441c : bv 32 := 0x00853583.
Lemma F_8441c : fetch_word Asan.M.loaded_segments (0x8446c : word) = Some W_8441c.
Proof. vm_refl. Qed.
Lemma D_8441c : decode_any W_8441c = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84420 : bv 32 := 0x01053503.
Lemma F_84420 : fetch_word Asan.M.loaded_segments (0x84470 : word) = Some W_84420.
Proof. vm_refl. Qed.
Lemma D_84420 : decode_any W_84420 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84424 : bv 32 := 0x00b53533.
Lemma F_84424 : fetch_word Asan.M.loaded_segments (0x84474 : word) = Some W_84424.
Proof. vm_refl. Qed.
Lemma D_84424 : decode_any W_84424 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84428 : bv 32 := 0x40a00533.
Lemma F_84428 : fetch_word Asan.M.loaded_segments (0x84478 : word) = Some W_84428.
Proof. vm_refl. Qed.
Lemma D_84428 : decode_any W_84428 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8442c : bv 32 := 0x00b57533.
Lemma F_8442c : fetch_word Asan.M.loaded_segments (0x8447c : word) = Some W_8442c.
Proof. vm_refl. Qed.
Lemma D_8442c : decode_any W_8442c = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84430 : bv 32 := 0x00008067.
Lemma F_84430 : fetch_word Asan.M.loaded_segments (0x84480 : word) = Some W_84430.
Proof. vm_refl. Qed.
Lemma D_84430 : decode_any W_84430 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84434 : bv 32 := 0x02850583.
Lemma F_84434 : fetch_word Asan.M.loaded_segments (0x84484 : word) = Some W_84434.
Proof. vm_refl. Qed.
Lemma D_84434 : decode_any W_84434 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84438 : bv 32 := 0x0230000f.
Lemma F_84438 : fetch_word Asan.M.loaded_segments (0x84488 : word) = Some W_84438.
Proof. vm_refl. Qed.
Lemma D_84438 : decode_any W_84438 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8443c : bv 32 := 0x02058c63.
Lemma F_8443c : fetch_word Asan.M.loaded_segments (0x8448c : word) = Some W_8443c.
Proof. vm_refl. Qed.
Lemma D_8443c : decode_any W_8443c = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84474 : bv 32 := 0x00853583.
Lemma F_84474 : fetch_word Asan.M.loaded_segments (0x844c4 : word) = Some W_84474.
Proof. vm_refl. Qed.
Lemma D_84474 : decode_any W_84474 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84478 : bv 32 := 0x01053503.
Lemma F_84478 : fetch_word Asan.M.loaded_segments (0x844c8 : word) = Some W_84478.
Proof. vm_refl. Qed.
Lemma D_84478 : decode_any W_84478 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8447c : bv 32 := 0x00b535b3.
Lemma F_8447c : fetch_word Asan.M.loaded_segments (0x844cc : word) = Some W_8447c.
Proof. vm_refl. Qed.
Lemma D_8447c : decode_any W_8447c = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84480 : bv 32 := 0x40b005b3.
Lemma F_84480 : fetch_word Asan.M.loaded_segments (0x844d0 : word) = Some W_84480.
Proof. vm_refl. Qed.
Lemma D_84480 : decode_any W_84480 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84484 : bv 32 := 0x00a5f533.
Lemma F_84484 : fetch_word Asan.M.loaded_segments (0x844d4 : word) = Some W_84484.
Proof. vm_refl. Qed.
Lemma D_84484 : decode_any W_84484 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_84488 : bv 32 := 0x00008067.
Lemma F_84488 : fetch_word Asan.M.loaded_segments (0x844d8 : word) = Some W_84488.
Proof. vm_refl. Qed.
Lemma D_84488 : decode_any W_84488 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
