(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bd00c : bv 32 := 0x0004b503.
Lemma F_bd00c : fetch_word Asan.M.loaded_segments (0xbd03c : word) = Some W_bd00c.
Proof. vm_refl. Qed.
Lemma D_bd00c : decode_any W_bd00c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd010 : bv 32 := 0x00848493.
Lemma F_bd010 : fetch_word Asan.M.loaded_segments (0xbd040 : word) = Some W_bd010.
Proof. vm_refl. Qed.
Lemma D_bd010 : decode_any W_bd010 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd014 : bv 32 := 0xfe051ce3.
Lemma F_bd014 : fetch_word Asan.M.loaded_segments (0xbd044 : word) = Some W_bd014.
Proof. vm_refl. Qed.
Lemma D_bd014 : decode_any W_bd014 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd0c8 : bv 32 := 0x00b53023.
Lemma F_bd0c8 : fetch_word Asan.M.loaded_segments (0xbd0f8 : word) = Some W_bd0c8.
Proof. vm_refl. Qed.
Lemma D_bd0c8 : decode_any W_bd0c8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd0cc : bv 32 := 0x00158593.
Lemma F_bd0cc : fetch_word Asan.M.loaded_segments (0xbd0fc : word) = Some W_bd0cc.
Proof. vm_refl. Qed.
Lemma D_bd0cc : decode_any W_bd0cc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd0d0 : bv 32 := 0xfff5c683.
Lemma F_bd0d0 : fetch_word Asan.M.loaded_segments (0xbd100 : word) = Some W_bd0d0.
Proof. vm_refl. Qed.
Lemma D_bd0d0 : decode_any W_bd0d0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd0d4 : bv 32 := 0xfec68ae3.
Lemma F_bd0d4 : fetch_word Asan.M.loaded_segments (0xbd104 : word) = Some W_bd0d4.
Proof. vm_refl. Qed.
Lemma D_bd0d4 : decode_any W_bd0d4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd0d8 : bv 32 := 0xfe069ae3.
Lemma F_bd0d8 : fetch_word Asan.M.loaded_segments (0xbd108 : word) = Some W_bd0d8.
Proof. vm_refl. Qed.
Lemma D_bd0d8 : decode_any W_bd0d8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
