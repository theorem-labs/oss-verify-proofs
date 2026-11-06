(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_527d0 : bv 32 := 0xfe010113.
Lemma F_527d0 : fetch_word Asan.M.loaded_segments (0x527d0 : word) = Some W_527d0.
Proof. vm_refl. Qed.
Lemma D_527d0 : decode_any W_527d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_527d4 : bv 32 := 0x00113c23.
Lemma F_527d4 : fetch_word Asan.M.loaded_segments (0x527d4 : word) = Some W_527d4.
Proof. vm_refl. Qed.
Lemma D_527d4 : decode_any W_527d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_527d8 : bv 32 := 0x00813823.
Lemma F_527d8 : fetch_word Asan.M.loaded_segments (0x527d8 : word) = Some W_527d8.
Proof. vm_refl. Qed.
Lemma D_527d8 : decode_any W_527d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_527dc : bv 32 := 0x00913423.
Lemma F_527dc : fetch_word Asan.M.loaded_segments (0x527dc : word) = Some W_527dc.
Proof. vm_refl. Qed.
Lemma D_527dc : decode_any W_527dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_527e0 : bv 32 := 0x01213023.
Lemma F_527e0 : fetch_word Asan.M.loaded_segments (0x527e0 : word) = Some W_527e0.
Proof. vm_refl. Qed.
Lemma D_527e0 : decode_any W_527e0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_527e4 : bv 32 := 0x00050413.
Lemma F_527e4 : fetch_word Asan.M.loaded_segments (0x527e4 : word) = Some W_527e4.
Proof. vm_refl. Qed.
Lemma D_527e4 : decode_any W_527e4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_527e8 : bv 32 := 0x7fc140ef.
Lemma F_527e8 : fetch_word Asan.M.loaded_segments (0x527e8 : word) = Some W_527e8.
Proof. vm_refl. Qed.
Lemma D_527e8 : decode_any W_527e8 = Some (Jal 1 83964, 4%Z).
Proof. vm_refl. Qed.

Definition W_527ec : bv 32 := 0x00085597.
Lemma F_527ec : fetch_word Asan.M.loaded_segments (0x527ec : word) = Some W_527ec.
Proof. vm_refl. Qed.
Lemma D_527ec : decode_any W_527ec = Some (Auipc 11 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_527f0 : bv 32 := 0xf4c5b583.
Lemma F_527f0 : fetch_word Asan.M.loaded_segments (0x527f0 : word) = Some W_527f0.
Proof. vm_refl. Qed.
Lemma D_527f0 : decode_any W_527f0 = Some (Load SZ8 true 11 11 3916, 4%Z).
Proof. vm_refl. Qed.

Definition W_527f4 : bv 32 := 0x00050913.
Lemma F_527f4 : fetch_word Asan.M.loaded_segments (0x527f4 : word) = Some W_527f4.
Proof. vm_refl. Qed.
Lemma D_527f4 : decode_any W_527f4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_527f8 : bv 32 := 0x00040513.
Lemma F_527f8 : fetch_word Asan.M.loaded_segments (0x527f8 : word) = Some W_527f8.
Proof. vm_refl. Qed.
Lemma D_527f8 : decode_any W_527f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_527fc : bv 32 := 0x000580e7.
Lemma F_527fc : fetch_word Asan.M.loaded_segments (0x527fc : word) = Some W_527fc.
Proof. vm_refl. Qed.
Lemma D_527fc : decode_any W_527fc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52800 : bv 32 := 0x00050493.
Lemma F_52800 : fetch_word Asan.M.loaded_segments (0x52800 : word) = Some W_52800.
Proof. vm_refl. Qed.
Lemma D_52800 : decode_any W_52800 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52804 : bv 32 := 0x02090663.
Lemma F_52804 : fetch_word Asan.M.loaded_segments (0x52804 : word) = Some W_52804.
Proof. vm_refl. Qed.
Lemma D_52804 : decode_any W_52804 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_52808 : bv 32 := 0x7dd160ef.
Lemma F_52808 : fetch_word Asan.M.loaded_segments (0x52808 : word) = Some W_52808.
Proof. vm_refl. Qed.
Lemma D_52808 : decode_any W_52808 = Some (Jal 1 94172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5280c : bv 32 := 0x00050863.
Lemma F_5280c : fetch_word Asan.M.loaded_segments (0x5280c : word) = Some W_5280c.
Proof. vm_refl. Qed.
Lemma D_5280c : decode_any W_5280c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52810 : bv 32 := 0x03053603.
Lemma F_52810 : fetch_word Asan.M.loaded_segments (0x52810 : word) = Some W_52810.
Proof. vm_refl. Qed.
Lemma D_52810 : decode_any W_52810 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_52814 : bv 32 := 0x03853683.
Lemma F_52814 : fetch_word Asan.M.loaded_segments (0x52814 : word) = Some W_52814.
Proof. vm_refl. Qed.
Lemma D_52814 : decode_any W_52814 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52818 : bv 32 := 0x00c0006f.
Lemma F_52818 : fetch_word Asan.M.loaded_segments (0x52818 : word) = Some W_52818.
Proof. vm_refl. Qed.
Lemma D_52818 : decode_any W_52818 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5281c : bv 32 := 0x00000613.
Lemma F_5281c : fetch_word Asan.M.loaded_segments (0x5281c : word) = Some W_5281c.
Proof. vm_refl. Qed.
Lemma D_5281c : decode_any W_5281c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52820 : bv 32 := 0x00000693.
Lemma F_52820 : fetch_word Asan.M.loaded_segments (0x52820 : word) = Some W_52820.
Proof. vm_refl. Qed.
Lemma D_52820 : decode_any W_52820 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52824 : bv 32 := 0x00040513.
Lemma F_52824 : fetch_word Asan.M.loaded_segments (0x52824 : word) = Some W_52824.
Proof. vm_refl. Qed.
Lemma D_52824 : decode_any W_52824 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52828 : bv 32 := 0x00048593.
Lemma F_52828 : fetch_word Asan.M.loaded_segments (0x52828 : word) = Some W_52828.
Proof. vm_refl. Qed.
Lemma D_52828 : decode_any W_52828 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5282c : bv 32 := 0x6cc240ef.
Lemma F_5282c : fetch_word Asan.M.loaded_segments (0x5282c : word) = Some W_5282c.
Proof. vm_refl. Qed.
Lemma D_5282c : decode_any W_5282c = Some (Jal 1 149196, 4%Z).
Proof. vm_refl. Qed.

Definition W_52830 : bv 32 := 0x00048513.
Lemma F_52830 : fetch_word Asan.M.loaded_segments (0x52830 : word) = Some W_52830.
Proof. vm_refl. Qed.
Lemma D_52830 : decode_any W_52830 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52834 : bv 32 := 0x01813083.
Lemma F_52834 : fetch_word Asan.M.loaded_segments (0x52834 : word) = Some W_52834.
Proof. vm_refl. Qed.
Lemma D_52834 : decode_any W_52834 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52838 : bv 32 := 0x01013403.
Lemma F_52838 : fetch_word Asan.M.loaded_segments (0x52838 : word) = Some W_52838.
Proof. vm_refl. Qed.
Lemma D_52838 : decode_any W_52838 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5283c : bv 32 := 0x00813483.
Lemma F_5283c : fetch_word Asan.M.loaded_segments (0x5283c : word) = Some W_5283c.
Proof. vm_refl. Qed.
Lemma D_5283c : decode_any W_5283c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52840 : bv 32 := 0x00013903.
Lemma F_52840 : fetch_word Asan.M.loaded_segments (0x52840 : word) = Some W_52840.
Proof. vm_refl. Qed.
Lemma D_52840 : decode_any W_52840 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52844 : bv 32 := 0x02010113.
Lemma F_52844 : fetch_word Asan.M.loaded_segments (0x52844 : word) = Some W_52844.
Proof. vm_refl. Qed.
Lemma D_52844 : decode_any W_52844 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52848 : bv 32 := 0x00008067.
Lemma F_52848 : fetch_word Asan.M.loaded_segments (0x52848 : word) = Some W_52848.
Proof. vm_refl. Qed.
Lemma D_52848 : decode_any W_52848 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
