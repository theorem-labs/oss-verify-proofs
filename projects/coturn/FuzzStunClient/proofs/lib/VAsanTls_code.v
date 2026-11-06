(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

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
Definition W_4428c : bv 32 := 0x1250406f.
Lemma F_4428c : fetch_word Asan.M.loaded_segments (0x4428c : word) = Some W_4428c.
Proof. vm_refl. Qed.
Lemma D_4428c : decode_any W_4428c = Some (Jal 0 18724, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_48bb0 : bv 32 := 0xfe010113.
Lemma F_48bb0 : fetch_word Asan.M.loaded_segments (0x48bb0 : word) = Some W_48bb0.
Proof. vm_refl. Qed.
Lemma D_48bb0 : decode_any W_48bb0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bb4 : bv 32 := 0x00113c23.
Lemma F_48bb4 : fetch_word Asan.M.loaded_segments (0x48bb4 : word) = Some W_48bb4.
Proof. vm_refl. Qed.
Lemma D_48bb4 : decode_any W_48bb4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bb8 : bv 32 := 0x00813823.
Lemma F_48bb8 : fetch_word Asan.M.loaded_segments (0x48bb8 : word) = Some W_48bb8.
Proof. vm_refl. Qed.
Lemma D_48bb8 : decode_any W_48bb8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bbc : bv 32 := 0x00913423.
Lemma F_48bbc : fetch_word Asan.M.loaded_segments (0x48bbc : word) = Some W_48bbc.
Proof. vm_refl. Qed.
Lemma D_48bbc : decode_any W_48bbc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bc0 : bv 32 := 0x01213023.
Lemma F_48bc0 : fetch_word Asan.M.loaded_segments (0x48bc0 : word) = Some W_48bc0.
Proof. vm_refl. Qed.
Lemma D_48bc0 : decode_any W_48bc0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bc4 : bv 32 := 0x00050413.
Lemma F_48bc4 : fetch_word Asan.M.loaded_segments (0x48bc4 : word) = Some W_48bc4.
Proof. vm_refl. Qed.
Lemma D_48bc4 : decode_any W_48bc4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bc8 : bv 32 := 0x278130ef.
Lemma F_48bc8 : fetch_word Asan.M.loaded_segments (0x48bc8 : word) = Some W_48bc8.
Proof. vm_refl. Qed.
Lemma D_48bc8 : decode_any W_48bc8 = Some (Jal 1 78456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bcc : bv 32 := 0x00064597.
Lemma F_48bcc : fetch_word Asan.M.loaded_segments (0x48bcc : word) = Some W_48bcc.
Proof. vm_refl. Qed.
Lemma D_48bcc : decode_any W_48bcc = Some (Auipc 11 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bd0 : bv 32 := 0x05c5b583.
Lemma F_48bd0 : fetch_word Asan.M.loaded_segments (0x48bd0 : word) = Some W_48bd0.
Proof. vm_refl. Qed.
Lemma D_48bd0 : decode_any W_48bd0 = Some (Load SZ8 true 11 11 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bd4 : bv 32 := 0x00050913.
Lemma F_48bd4 : fetch_word Asan.M.loaded_segments (0x48bd4 : word) = Some W_48bd4.
Proof. vm_refl. Qed.
Lemma D_48bd4 : decode_any W_48bd4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bd8 : bv 32 := 0x00040513.
Lemma F_48bd8 : fetch_word Asan.M.loaded_segments (0x48bd8 : word) = Some W_48bd8.
Proof. vm_refl. Qed.
Lemma D_48bd8 : decode_any W_48bd8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bdc : bv 32 := 0x000580e7.
Lemma F_48bdc : fetch_word Asan.M.loaded_segments (0x48bdc : word) = Some W_48bdc.
Proof. vm_refl. Qed.
Lemma D_48bdc : decode_any W_48bdc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48be0 : bv 32 := 0x00050493.
Lemma F_48be0 : fetch_word Asan.M.loaded_segments (0x48be0 : word) = Some W_48be0.
Proof. vm_refl. Qed.
Lemma D_48be0 : decode_any W_48be0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48be4 : bv 32 := 0x02090663.
Lemma F_48be4 : fetch_word Asan.M.loaded_segments (0x48be4 : word) = Some W_48be4.
Proof. vm_refl. Qed.
Lemma D_48be4 : decode_any W_48be4 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48be8 : bv 32 := 0x259150ef.
Lemma F_48be8 : fetch_word Asan.M.loaded_segments (0x48be8 : word) = Some W_48be8.
Proof. vm_refl. Qed.
Lemma D_48be8 : decode_any W_48be8 = Some (Jal 1 88664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bec : bv 32 := 0x00050863.
Lemma F_48bec : fetch_word Asan.M.loaded_segments (0x48bec : word) = Some W_48bec.
Proof. vm_refl. Qed.
Lemma D_48bec : decode_any W_48bec = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bf0 : bv 32 := 0x03053603.
Lemma F_48bf0 : fetch_word Asan.M.loaded_segments (0x48bf0 : word) = Some W_48bf0.
Proof. vm_refl. Qed.
Lemma D_48bf0 : decode_any W_48bf0 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bf4 : bv 32 := 0x03853683.
Lemma F_48bf4 : fetch_word Asan.M.loaded_segments (0x48bf4 : word) = Some W_48bf4.
Proof. vm_refl. Qed.
Lemma D_48bf4 : decode_any W_48bf4 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bf8 : bv 32 := 0x00c0006f.
Lemma F_48bf8 : fetch_word Asan.M.loaded_segments (0x48bf8 : word) = Some W_48bf8.
Proof. vm_refl. Qed.
Lemma D_48bf8 : decode_any W_48bf8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48bfc : bv 32 := 0x00000613.
Lemma F_48bfc : fetch_word Asan.M.loaded_segments (0x48bfc : word) = Some W_48bfc.
Proof. vm_refl. Qed.
Lemma D_48bfc : decode_any W_48bfc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c00 : bv 32 := 0x00000693.
Lemma F_48c00 : fetch_word Asan.M.loaded_segments (0x48c00 : word) = Some W_48c00.
Proof. vm_refl. Qed.
Lemma D_48c00 : decode_any W_48c00 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c04 : bv 32 := 0x00040513.
Lemma F_48c04 : fetch_word Asan.M.loaded_segments (0x48c04 : word) = Some W_48c04.
Proof. vm_refl. Qed.
Lemma D_48c04 : decode_any W_48c04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c08 : bv 32 := 0x00048593.
Lemma F_48c08 : fetch_word Asan.M.loaded_segments (0x48c08 : word) = Some W_48c08.
Proof. vm_refl. Qed.
Lemma D_48c08 : decode_any W_48c08 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c0c : bv 32 := 0x148230ef.
Lemma F_48c0c : fetch_word Asan.M.loaded_segments (0x48c0c : word) = Some W_48c0c.
Proof. vm_refl. Qed.
Lemma D_48c0c : decode_any W_48c0c = Some (Jal 1 143688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c10 : bv 32 := 0x00048513.
Lemma F_48c10 : fetch_word Asan.M.loaded_segments (0x48c10 : word) = Some W_48c10.
Proof. vm_refl. Qed.
Lemma D_48c10 : decode_any W_48c10 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c14 : bv 32 := 0x01813083.
Lemma F_48c14 : fetch_word Asan.M.loaded_segments (0x48c14 : word) = Some W_48c14.
Proof. vm_refl. Qed.
Lemma D_48c14 : decode_any W_48c14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c18 : bv 32 := 0x01013403.
Lemma F_48c18 : fetch_word Asan.M.loaded_segments (0x48c18 : word) = Some W_48c18.
Proof. vm_refl. Qed.
Lemma D_48c18 : decode_any W_48c18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c1c : bv 32 := 0x00813483.
Lemma F_48c1c : fetch_word Asan.M.loaded_segments (0x48c1c : word) = Some W_48c1c.
Proof. vm_refl. Qed.
Lemma D_48c1c : decode_any W_48c1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c20 : bv 32 := 0x00013903.
Lemma F_48c20 : fetch_word Asan.M.loaded_segments (0x48c20 : word) = Some W_48c20.
Proof. vm_refl. Qed.
Lemma D_48c20 : decode_any W_48c20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c24 : bv 32 := 0x02010113.
Lemma F_48c24 : fetch_word Asan.M.loaded_segments (0x48c24 : word) = Some W_48c24.
Proof. vm_refl. Qed.
Lemma D_48c24 : decode_any W_48c24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_48c28 : bv 32 := 0x00008067.
Lemma F_48c28 : fetch_word Asan.M.loaded_segments (0x48c28 : word) = Some W_48c28.
Proof. vm_refl. Qed.
Lemma D_48c28 : decode_any W_48c28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_5718c : bv 32 := 0x0005c517.
Lemma F_5718c : fetch_word Asan.M.loaded_segments (0x5718c : word) = Some W_5718c.
Proof. vm_refl. Qed.
Lemma D_5718c : decode_any W_5718c = Some (Auipc 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57190 : bv 32 := 0xcd450513.
Lemma F_57190 : fetch_word Asan.M.loaded_segments (0x57190 : word) = Some W_57190.
Proof. vm_refl. Qed.
Lemma D_57190 : decode_any W_57190 = Some (OpImm ALU_ADD 10 10 3284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57194 : bv 32 := 0x00054583.
Lemma F_57194 : fetch_word Asan.M.loaded_segments (0x57194 : word) = Some W_57194.
Proof. vm_refl. Qed.
Lemma D_57194 : decode_any W_57194 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57198 : bv 32 := 0x00058663.
Lemma F_57198 : fetch_word Asan.M.loaded_segments (0x57198 : word) = Some W_57198.
Proof. vm_refl. Qed.
Lemma D_57198 : decode_any W_57198 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5719c : bv 32 := 0x00452503.
Lemma F_5719c : fetch_word Asan.M.loaded_segments (0x5719c : word) = Some W_5719c.
Proof. vm_refl. Qed.
Lemma D_5719c : decode_any W_5719c = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_571a0 : bv 32 := 0x6f14e06f.
Lemma F_571a0 : fetch_word Asan.M.loaded_segments (0x571a0 : word) = Some W_571a0.
Proof. vm_refl. Qed.
Lemma D_571a0 : decode_any W_571a0 = Some (Jal 0 323312, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_5be40 : bv 32 := 0xff010113.
Lemma F_5be40 : fetch_word Asan.M.loaded_segments (0x5be40 : word) = Some W_5be40.
Proof. vm_refl. Qed.
Lemma D_5be40 : decode_any W_5be40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be44 : bv 32 := 0x00113423.
Lemma F_5be44 : fetch_word Asan.M.loaded_segments (0x5be44 : word) = Some W_5be44.
Proof. vm_refl. Qed.
Lemma D_5be44 : decode_any W_5be44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be48 : bv 32 := 0x00813023.
Lemma F_5be48 : fetch_word Asan.M.loaded_segments (0x5be48 : word) = Some W_5be48.
Proof. vm_refl. Qed.
Lemma D_5be48 : decode_any W_5be48 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be4c : bv 32 := 0x00058517.
Lemma F_5be4c : fetch_word Asan.M.loaded_segments (0x5be4c : word) = Some W_5be4c.
Proof. vm_refl. Qed.
Lemma D_5be4c : decode_any W_5be4c = Some (Auipc 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be50 : bv 32 := 0x48c50413.
Lemma F_5be50 : fetch_word Asan.M.loaded_segments (0x5be50 : word) = Some W_5be50.
Proof. vm_refl. Qed.
Lemma D_5be50 : decode_any W_5be50 = Some (OpImm ALU_ADD 8 10 1164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be54 : bv 32 := 0x00040583.
Lemma F_5be54 : fetch_word Asan.M.loaded_segments (0x5be54 : word) = Some W_5be54.
Proof. vm_refl. Qed.
Lemma D_5be54 : decode_any W_5be54 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be58 : bv 32 := 0x00100513.
Lemma F_5be58 : fetch_word Asan.M.loaded_segments (0x5be58 : word) = Some W_5be58.
Proof. vm_refl. Qed.
Lemma D_5be58 : decode_any W_5be58 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be5c : bv 32 := 0x0230000f.
Lemma F_5be5c : fetch_word Asan.M.loaded_segments (0x5be5c : word) = Some W_5be5c.
Proof. vm_refl. Qed.
Lemma D_5be5c : decode_any W_5be5c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be60 : bv 32 := 0x00a59a63.
Lemma F_5be60 : fetch_word Asan.M.loaded_segments (0x5be60 : word) = Some W_5be60.
Proof. vm_refl. Qed.
Lemma D_5be60 : decode_any W_5be60 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be64 : bv 32 := 0x00813083.
Lemma F_5be64 : fetch_word Asan.M.loaded_segments (0x5be64 : word) = Some W_5be64.
Proof. vm_refl. Qed.
Lemma D_5be64 : decode_any W_5be64 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be68 : bv 32 := 0x00013403.
Lemma F_5be68 : fetch_word Asan.M.loaded_segments (0x5be68 : word) = Some W_5be68.
Proof. vm_refl. Qed.
Lemma D_5be68 : decode_any W_5be68 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be6c : bv 32 := 0x01010113.
Lemma F_5be6c : fetch_word Asan.M.loaded_segments (0x5be6c : word) = Some W_5be6c.
Proof. vm_refl. Qed.
Lemma D_5be6c : decode_any W_5be6c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5be70 : bv 32 := 0x00008067.
Lemma F_5be70 : fetch_word Asan.M.loaded_segments (0x5be70 : word) = Some W_5be70.
Proof. vm_refl. Qed.
Lemma D_5be70 : decode_any W_5be70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_5e640 : bv 32 := 0xff010113.
Lemma F_5e640 : fetch_word Asan.M.loaded_segments (0x5e640 : word) = Some W_5e640.
Proof. vm_refl. Qed.
Lemma D_5e640 : decode_any W_5e640 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e644 : bv 32 := 0x00113423.
Lemma F_5e644 : fetch_word Asan.M.loaded_segments (0x5e644 : word) = Some W_5e644.
Proof. vm_refl. Qed.
Lemma D_5e644 : decode_any W_5e644 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e648 : bv 32 := 0xb45f80ef.
Lemma F_5e648 : fetch_word Asan.M.loaded_segments (0x5e648 : word) = Some W_5e648.
Proof. vm_refl. Qed.
Lemma D_5e648 : decode_any W_5e648 = Some (Jal 1 2067268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e64c : bv 32 := 0x00050463.
Lemma F_5e64c : fetch_word Asan.M.loaded_segments (0x5e64c : word) = Some W_5e64c.
Proof. vm_refl. Qed.
Lemma D_5e64c : decode_any W_5e64c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e650 : bv 32 := 0x09853503.
Lemma F_5e650 : fetch_word Asan.M.loaded_segments (0x5e650 : word) = Some W_5e650.
Proof. vm_refl. Qed.
Lemma D_5e650 : decode_any W_5e650 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e654 : bv 32 := 0x00813083.
Lemma F_5e654 : fetch_word Asan.M.loaded_segments (0x5e654 : word) = Some W_5e654.
Proof. vm_refl. Qed.
Lemma D_5e654 : decode_any W_5e654 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e658 : bv 32 := 0x01010113.
Lemma F_5e658 : fetch_word Asan.M.loaded_segments (0x5e658 : word) = Some W_5e658.
Proof. vm_refl. Qed.
Lemma D_5e658 : decode_any W_5e658 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e65c : bv 32 := 0x00008067.
Lemma F_5e65c : fetch_word Asan.M.loaded_segments (0x5e65c : word) = Some W_5e65c.
Proof. vm_refl. Qed.
Lemma D_5e65c : decode_any W_5e65c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_6bd54 : bv 32 := 0xf7010113.
Lemma F_6bd54 : fetch_word Asan.M.loaded_segments (0x6bd54 : word) = Some W_6bd54.
Proof. vm_refl. Qed.
Lemma D_6bd54 : decode_any W_6bd54 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd58 : bv 32 := 0x08113423.
Lemma F_6bd58 : fetch_word Asan.M.loaded_segments (0x6bd58 : word) = Some W_6bd58.
Proof. vm_refl. Qed.
Lemma D_6bd58 : decode_any W_6bd58 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd5c : bv 32 := 0x08813023.
Lemma F_6bd5c : fetch_word Asan.M.loaded_segments (0x6bd5c : word) = Some W_6bd5c.
Proof. vm_refl. Qed.
Lemma D_6bd5c : decode_any W_6bd5c = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd60 : bv 32 := 0x06913c23.
Lemma F_6bd60 : fetch_word Asan.M.loaded_segments (0x6bd60 : word) = Some W_6bd60.
Proof. vm_refl. Qed.
Lemma D_6bd60 : decode_any W_6bd60 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd64 : bv 32 := 0x07213823.
Lemma F_6bd64 : fetch_word Asan.M.loaded_segments (0x6bd64 : word) = Some W_6bd64.
Proof. vm_refl. Qed.
Lemma D_6bd64 : decode_any W_6bd64 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd68 : bv 32 := 0x07313423.
Lemma F_6bd68 : fetch_word Asan.M.loaded_segments (0x6bd68 : word) = Some W_6bd68.
Proof. vm_refl. Qed.
Lemma D_6bd68 : decode_any W_6bd68 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd6c : bv 32 := 0x07413023.
Lemma F_6bd6c : fetch_word Asan.M.loaded_segments (0x6bd6c : word) = Some W_6bd6c.
Proof. vm_refl. Qed.
Lemma D_6bd6c : decode_any W_6bd6c = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd70 : bv 32 := 0x05513c23.
Lemma F_6bd70 : fetch_word Asan.M.loaded_segments (0x6bd70 : word) = Some W_6bd70.
Proof. vm_refl. Qed.
Lemma D_6bd70 : decode_any W_6bd70 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd74 : bv 32 := 0x05613823.
Lemma F_6bd74 : fetch_word Asan.M.loaded_segments (0x6bd74 : word) = Some W_6bd74.
Proof. vm_refl. Qed.
Lemma D_6bd74 : decode_any W_6bd74 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd78 : bv 32 := 0x05713423.
Lemma F_6bd78 : fetch_word Asan.M.loaded_segments (0x6bd78 : word) = Some W_6bd78.
Proof. vm_refl. Qed.
Lemma D_6bd78 : decode_any W_6bd78 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd7c : bv 32 := 0x05813023.
Lemma F_6bd7c : fetch_word Asan.M.loaded_segments (0x6bd7c : word) = Some W_6bd7c.
Proof. vm_refl. Qed.
Lemma D_6bd7c : decode_any W_6bd7c = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd80 : bv 32 := 0x03913c23.
Lemma F_6bd80 : fetch_word Asan.M.loaded_segments (0x6bd80 : word) = Some W_6bd80.
Proof. vm_refl. Qed.
Lemma D_6bd80 : decode_any W_6bd80 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd84 : bv 32 := 0x03a13823.
Lemma F_6bd84 : fetch_word Asan.M.loaded_segments (0x6bd84 : word) = Some W_6bd84.
Proof. vm_refl. Qed.
Lemma D_6bd84 : decode_any W_6bd84 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd88 : bv 32 := 0x03b13423.
Lemma F_6bd88 : fetch_word Asan.M.loaded_segments (0x6bd88 : word) = Some W_6bd88.
Proof. vm_refl. Qed.
Lemma D_6bd88 : decode_any W_6bd88 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd8c : bv 32 := 0x00058913.
Lemma F_6bd8c : fetch_word Asan.M.loaded_segments (0x6bd8c : word) = Some W_6bd8c.
Proof. vm_refl. Qed.
Lemma D_6bd8c : decode_any W_6bd8c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd90 : bv 32 := 0x0003f597.
Lemma F_6bd90 : fetch_word Asan.M.loaded_segments (0x6bd90 : word) = Some W_6bd90.
Proof. vm_refl. Qed.
Lemma D_6bd90 : decode_any W_6bd90 = Some (Auipc 11 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd94 : bv 32 := 0x0e05b583.
Lemma F_6bd94 : fetch_word Asan.M.loaded_segments (0x6bd94 : word) = Some W_6bd94.
Proof. vm_refl. Qed.
Lemma D_6bd94 : decode_any W_6bd94 = Some (Load SZ8 true 11 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd98 : bv 32 := 0x0895c583.
Lemma F_6bd98 : fetch_word Asan.M.loaded_segments (0x6bd98 : word) = Some W_6bd98.
Proof. vm_refl. Qed.
Lemma D_6bd98 : decode_any W_6bd98 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd9c : bv 32 := 0x18058a63.
Lemma F_6bd9c : fetch_word Asan.M.loaded_segments (0x6bd9c : word) = Some W_6bd9c.
Proof. vm_refl. Qed.
Lemma D_6bd9c : decode_any W_6bd9c = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bda0 : bv 32 := 0x00050993.
Lemma F_6bda0 : fetch_word Asan.M.loaded_segments (0x6bda0 : word) = Some W_6bda0.
Proof. vm_refl. Qed.
Lemma D_6bda0 : decode_any W_6bda0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bda4 : bv 32 := 0x0003f517.
Lemma F_6bda4 : fetch_word Asan.M.loaded_segments (0x6bda4 : word) = Some W_6bda4.
Proof. vm_refl. Qed.
Lemma D_6bda4 : decode_any W_6bda4 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bda8 : bv 32 := 0x12c53d03.
Lemma F_6bda8 : fetch_word Asan.M.loaded_segments (0x6bda8 : word) = Some W_6bda8.
Proof. vm_refl. Qed.
Lemma D_6bda8 : decode_any W_6bda8 = Some (Load SZ8 true 26 10 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdac : bv 32 := 0x0009ba03.
Lemma F_6bdac : fetch_word Asan.M.loaded_segments (0x6bdac : word) = Some W_6bdac.
Proof. vm_refl. Qed.
Lemma D_6bdac : decode_any W_6bdac = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdb0 : bv 32 := 0x00040517.
Lemma F_6bdb0 : fetch_word Asan.M.loaded_segments (0x6bdb0 : word) = Some W_6bdb0.
Proof. vm_refl. Qed.
Lemma D_6bdb0 : decode_any W_6bdb0 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdb4 : bv 32 := 0x000d2583.
Lemma F_6bdb4 : fetch_word Asan.M.loaded_segments (0x6bdb4 : word) = Some W_6bdb4.
Proof. vm_refl. Qed.
Lemma D_6bdb4 : decode_any W_6bdb4 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdb8 : bv 32 := 0xdc053a83.
Lemma F_6bdb8 : fetch_word Asan.M.loaded_segments (0x6bdb8 : word) = Some W_6bdb8.
Proof. vm_refl. Qed.
Lemma D_6bdb8 : decode_any W_6bdb8 = Some (Load SZ8 true 21 10 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdbc : bv 32 := 0x00300513.
Lemma F_6bdbc : fetch_word Asan.M.loaded_segments (0x6bdbc : word) = Some W_6bdbc.
Proof. vm_refl. Qed.
Lemma D_6bdbc : decode_any W_6bdbc = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdc0 : bv 32 := 0x004a8ab3.
Lemma F_6bdc0 : fetch_word Asan.M.loaded_segments (0x6bdc0 : word) = Some W_6bdc0.
Proof. vm_refl. Qed.
Lemma D_6bdc0 : decode_any W_6bdc0 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdc4 : bv 32 := 0x1ea5fa63.
Lemma F_6bdc4 : fetch_word Asan.M.loaded_segments (0x6bdc4 : word) = Some W_6bdc4.
Proof. vm_refl. Qed.
Lemma D_6bdc4 : decode_any W_6bdc4 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdc8 : bv 32 := 0x000abb03.
Lemma F_6bdc8 : fetch_word Asan.M.loaded_segments (0x6bdc8 : word) = Some W_6bdc8.
Proof. vm_refl. Qed.
Lemma D_6bdc8 : decode_any W_6bdc8 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdcc : bv 32 := 0xfff00513.
Lemma F_6bdcc : fetch_word Asan.M.loaded_segments (0x6bdcc : word) = Some W_6bdcc.
Proof. vm_refl. Qed.
Lemma D_6bdcc : decode_any W_6bdcc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdd0 : bv 32 := 0x0230000f.
Lemma F_6bdd0 : fetch_word Asan.M.loaded_segments (0x6bdd0 : word) = Some W_6bdd0.
Proof. vm_refl. Qed.
Lemma D_6bdd0 : decode_any W_6bdd0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdd4 : bv 32 := 0x14ab0e63.
Lemma F_6bdd4 : fetch_word Asan.M.loaded_segments (0x6bdd4 : word) = Some W_6bdd4.
Proof. vm_refl. Qed.
Lemma D_6bdd4 : decode_any W_6bdd4 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdd8 : bv 32 := 0x080b1263.
Lemma F_6bdd8 : fetch_word Asan.M.loaded_segments (0x6bdd8 : word) = Some W_6bdd8.
Proof. vm_refl. Qed.
Lemma D_6bdd8 : decode_any W_6bdd8 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bddc : bv 32 := 0x00060c13.
Lemma F_6bddc : fetch_word Asan.M.loaded_segments (0x6bddc : word) = Some W_6bddc.
Proof. vm_refl. Qed.
Lemma D_6bddc : decode_any W_6bddc = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bde0 : bv 32 := 0x00068493.
Lemma F_6bde0 : fetch_word Asan.M.loaded_segments (0x6bde0 : word) = Some W_6bde0.
Proof. vm_refl. Qed.
Lemma D_6bde0 : decode_any W_6bde0 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bde4 : bv 32 := 0xfffa8517.
Lemma F_6bde4 : fetch_word Asan.M.loaded_segments (0x6bde4 : word) = Some W_6bde4.
Proof. vm_refl. Qed.
Lemma D_6bde4 : decode_any W_6bde4 = Some (Auipc 10 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bde8 : bv 32 := 0x00001bb7.
Lemma F_6bde8 : fetch_word Asan.M.loaded_segments (0x6bde8 : word) = Some W_6bde8.
Proof. vm_refl. Qed.
Lemma D_6bde8 : decode_any W_6bde8 = Some (Lui 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdec : bv 32 := 0x01e50593.
Lemma F_6bdec : fetch_word Asan.M.loaded_segments (0x6bdec : word) = Some W_6bdec.
Proof. vm_refl. Qed.
Lemma D_6bdec : decode_any W_6bdec = Some (OpImm ALU_ADD 11 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdf0 : bv 32 := 0xff8b8b9b.
Lemma F_6bdf0 : fetch_word Asan.M.loaded_segments (0x6bdf0 : word) = Some W_6bdf0.
Proof. vm_refl. Qed.
Lemma D_6bdf0 : decode_any W_6bdf0 = Some (OpImm32 23 23 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdf4 : bv 32 := 0x000b8513.
Lemma F_6bdf4 : fetch_word Asan.M.loaded_segments (0x6bdf4 : word) = Some W_6bdf4.
Proof. vm_refl. Qed.
Lemma D_6bdf4 : decode_any W_6bdf4 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdf8 : bv 32 := 0x00000613.
Lemma F_6bdf8 : fetch_word Asan.M.loaded_segments (0x6bdf8 : word) = Some W_6bdf8.
Proof. vm_refl. Qed.
Lemma D_6bdf8 : decode_any W_6bdf8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdfc : bv 32 := 0xa90fc0ef.
Lemma F_6bdfc : fetch_word Asan.M.loaded_segments (0x6bdfc : word) = Some W_6bdfc.
Proof. vm_refl. Qed.
Lemma D_6bdfc : decode_any W_6bdfc = Some (Jal 1 2081424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be00 : bv 32 := 0x00050b13.
Lemma F_6be00 : fetch_word Asan.M.loaded_segments (0x6be00 : word) = Some W_6be00.
Proof. vm_refl. Qed.
Lemma D_6be00 : decode_any W_6be00 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be04 : bv 32 := 0x160ab42f.
Lemma F_6be04 : fetch_word Asan.M.loaded_segments (0x6be04 : word) = Some W_6be04.
Proof. vm_refl. Qed.
Lemma D_6be04 : decode_any W_6be04 = Some (Lr AD true true 8 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be08 : bv 32 := 0x02041c63.
Lemma F_6be08 : fetch_word Asan.M.loaded_segments (0x6be08 : word) = Some W_6be08.
Proof. vm_refl. Qed.
Lemma D_6be08 : decode_any W_6be08 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be0c : bv 32 := 0x1b6ab52f.
Lemma F_6be0c : fetch_word Asan.M.loaded_segments (0x6be0c : word) = Some W_6be0c.
Proof. vm_refl. Qed.
Lemma D_6be0c : decode_any W_6be0c = Some (Sc AD false true 10 21 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be10 : bv 32 := 0xfe051ae3.
Lemma F_6be10 : fetch_word Asan.M.loaded_segments (0x6be10 : word) = Some W_6be10.
Proof. vm_refl. Qed.
Lemma D_6be10 : decode_any W_6be10 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be14 : bv 32 := 0x000d9517.
Lemma F_6be14 : fetch_word Asan.M.loaded_segments (0x6be14 : word) = Some W_6be14.
Proof. vm_refl. Qed.
Lemma D_6be14 : decode_any W_6be14 = Some (Auipc 10 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be18 : bv 32 := 0x52450513.
Lemma F_6be18 : fetch_word Asan.M.loaded_segments (0x6be18 : word) = Some W_6be18.
Proof. vm_refl. Qed.
Lemma D_6be18 : decode_any W_6be18 = Some (OpImm ALU_ADD 10 10 1316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be1c : bv 32 := 0x00100593.
Lemma F_6be1c : fetch_word Asan.M.loaded_segments (0x6be1c : word) = Some W_6be1c.
Proof. vm_refl. Qed.
Lemma D_6be1c : decode_any W_6be1c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be20 : bv 32 := 0x00b5362f.
Lemma F_6be20 : fetch_word Asan.M.loaded_segments (0x6be20 : word) = Some W_6be20.
Proof. vm_refl. Qed.
Lemma D_6be20 : decode_any W_6be20 = Some (Amo AMO_ADD AD false false 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be24 : bv 32 := 0x000d2503.
Lemma F_6be24 : fetch_word Asan.M.loaded_segments (0x6be24 : word) = Some W_6be24.
Proof. vm_refl. Qed.
Lemma D_6be24 : decode_any W_6be24 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be28 : bv 32 := 0x02a5f663.
Lemma F_6be28 : fetch_word Asan.M.loaded_segments (0x6be28 : word) = Some W_6be28.
Proof. vm_refl. Qed.
Lemma D_6be28 : decode_any W_6be28 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be2c : bv 32 := 0xfffa8517.
Lemma F_6be2c : fetch_word Asan.M.loaded_segments (0x6be2c : word) = Some W_6be2c.
Proof. vm_refl. Qed.
Lemma D_6be2c : decode_any W_6be2c = Some (Auipc 10 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be30 : bv 32 := 0xfe550513.
Lemma F_6be30 : fetch_word Asan.M.loaded_segments (0x6be30 : word) = Some W_6be30.
Proof. vm_refl. Qed.
Lemma D_6be30 : decode_any W_6be30 = Some (OpImm ALU_ADD 10 10 4069, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be34 : bv 32 := 0x000a8593.
Lemma F_6be34 : fetch_word Asan.M.loaded_segments (0x6be34 : word) = Some W_6be34.
Proof. vm_refl. Qed.
Lemma D_6be34 : decode_any W_6be34 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be38 : bv 32 := 0xfacfd0ef.
Lemma F_6be38 : fetch_word Asan.M.loaded_segments (0x6be38 : word) = Some W_6be38.
Proof. vm_refl. Qed.
Lemma D_6be38 : decode_any W_6be38 = Some (Jal 1 2086828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be3c : bv 32 := 0x0180006f.
Lemma F_6be3c : fetch_word Asan.M.loaded_segments (0x6be3c : word) = Some W_6be3c.
Proof. vm_refl. Qed.
Lemma D_6be3c : decode_any W_6be3c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be40 : bv 32 := 0x000b0513.
Lemma F_6be40 : fetch_word Asan.M.loaded_segments (0x6be40 : word) = Some W_6be40.
Proof. vm_refl. Qed.
Lemma D_6be40 : decode_any W_6be40 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be44 : bv 32 := 0x000b8593.
Lemma F_6be44 : fetch_word Asan.M.loaded_segments (0x6be44 : word) = Some W_6be44.
Proof. vm_refl. Qed.
Lemma D_6be44 : decode_any W_6be44 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be48 : bv 32 := 0x00000613.
Lemma F_6be48 : fetch_word Asan.M.loaded_segments (0x6be48 : word) = Some W_6be48.
Proof. vm_refl. Qed.
Lemma D_6be48 : decode_any W_6be48 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be4c : bv 32 := 0xbc0fc0ef.
Lemma F_6be4c : fetch_word Asan.M.loaded_segments (0x6be4c : word) = Some W_6be4c.
Proof. vm_refl. Qed.
Lemma D_6be4c : decode_any W_6be4c = Some (Jal 1 2081728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be50 : bv 32 := 0x00040b13.
Lemma F_6be50 : fetch_word Asan.M.loaded_segments (0x6be50 : word) = Some W_6be50.
Proof. vm_refl. Qed.
Lemma D_6be50 : decode_any W_6be50 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be54 : bv 32 := 0x00048693.
Lemma F_6be54 : fetch_word Asan.M.loaded_segments (0x6be54 : word) = Some W_6be54.
Proof. vm_refl. Qed.
Lemma D_6be54 : decode_any W_6be54 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be58 : bv 32 := 0x000c0613.
Lemma F_6be58 : fetch_word Asan.M.loaded_segments (0x6be58 : word) = Some W_6be58.
Proof. vm_refl. Qed.
Lemma D_6be58 : decode_any W_6be58 = Some (OpImm ALU_ADD 12 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be5c : bv 32 := 0x0c0b0a63.
Lemma F_6be5c : fetch_word Asan.M.loaded_segments (0x6be5c : word) = Some W_6be5c.
Proof. vm_refl. Qed.
Lemma D_6be5c : decode_any W_6be5c = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be60 : bv 32 := 0x00c13823.
Lemma F_6be60 : fetch_word Asan.M.loaded_segments (0x6be60 : word) = Some W_6be60.
Proof. vm_refl. Qed.
Lemma D_6be60 : decode_any W_6be60 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be64 : bv 32 := 0x00d13c23.
Lemma F_6be64 : fetch_word Asan.M.loaded_segments (0x6be64 : word) = Some W_6be64.
Proof. vm_refl. Qed.
Lemma D_6be64 : decode_any W_6be64 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be68 : bv 32 := 0x0ff00513.
Lemma F_6be68 : fetch_word Asan.M.loaded_segments (0x6be68 : word) = Some W_6be68.
Proof. vm_refl. Qed.
Lemma D_6be68 : decode_any W_6be68 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be6c : bv 32 := 0x0aaa6863.
Lemma F_6be6c : fetch_word Asan.M.loaded_segments (0x6be6c : word) = Some W_6be6c.
Proof. vm_refl. Qed.
Lemma D_6be6c : decode_any W_6be6c = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be70 : bv 32 := 0xfff00d93.
Lemma F_6be70 : fetch_word Asan.M.loaded_segments (0x6be70 : word) = Some W_6be70.
Proof. vm_refl. Qed.
Lemma D_6be70 : decode_any W_6be70 = Some (OpImm ALU_ADD 27 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be74 : bv 32 := 0x0fe00c93.
Lemma F_6be74 : fetch_word Asan.M.loaded_segments (0x6be74 : word) = Some W_6be74.
Proof. vm_refl. Qed.
Lemma D_6be74 : decode_any W_6be74 = Some (OpImm ALU_ADD 25 0 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be78 : bv 32 := 0xfffa8517.
Lemma F_6be78 : fetch_word Asan.M.loaded_segments (0x6be78 : word) = Some W_6be78.
Proof. vm_refl. Qed.
Lemma D_6be78 : decode_any W_6be78 = Some (Auipc 10 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be7c : bv 32 := 0x00001c37.
Lemma F_6be7c : fetch_word Asan.M.loaded_segments (0x6be7c : word) = Some W_6be7c.
Proof. vm_refl. Qed.
Lemma D_6be7c : decode_any W_6be7c = Some (Lui 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be80 : bv 32 := 0x000d9597.
Lemma F_6be80 : fetch_word Asan.M.loaded_segments (0x6be80 : word) = Some W_6be80.
Proof. vm_refl. Qed.
Lemma D_6be80 : decode_any W_6be80 = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be84 : bv 32 := 0xfffa8617.
Lemma F_6be84 : fetch_word Asan.M.loaded_segments (0x6be84 : word) = Some W_6be84.
Proof. vm_refl. Qed.
Lemma D_6be84 : decode_any W_6be84 = Some (Auipc 12 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be88 : bv 32 := 0xf8a50b93.
Lemma F_6be88 : fetch_word Asan.M.loaded_segments (0x6be88 : word) = Some W_6be88.
Proof. vm_refl. Qed.
Lemma D_6be88 : decode_any W_6be88 = Some (OpImm ALU_ADD 23 10 3978, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be8c : bv 32 := 0xff8c0c1b.
Lemma F_6be8c : fetch_word Asan.M.loaded_segments (0x6be8c : word) = Some W_6be8c.
Proof. vm_refl. Qed.
Lemma D_6be8c : decode_any W_6be8c = Some (OpImm32 24 24 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be90 : bv 32 := 0x4b858413.
Lemma F_6be90 : fetch_word Asan.M.loaded_segments (0x6be90 : word) = Some W_6be90.
Proof. vm_refl. Qed.
Lemma D_6be90 : decode_any W_6be90 = Some (OpImm ALU_ADD 8 11 1208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be94 : bv 32 := 0xf8d60513.
Lemma F_6be94 : fetch_word Asan.M.loaded_segments (0x6be94 : word) = Some W_6be94.
Proof. vm_refl. Qed.
Lemma D_6be94 : decode_any W_6be94 = Some (OpImm ALU_ADD 10 12 3981, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be98 : bv 32 := 0x00a13423.
Lemma F_6be98 : fetch_word Asan.M.loaded_segments (0x6be98 : word) = Some W_6be98.
Proof. vm_refl. Qed.
Lemma D_6be98 : decode_any W_6be98 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be9c : bv 32 := 0x0140006f.
Lemma F_6be9c : fetch_word Asan.M.loaded_segments (0x6be9c : word) = Some W_6be9c.
Proof. vm_refl. Qed.
Lemma D_6be9c : decode_any W_6be9c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bea0 : bv 32 := 0x00000513.
Lemma F_6bea0 : fetch_word Asan.M.loaded_segments (0x6bea0 : word) = Some W_6bea0.
Proof. vm_refl. Qed.
Lemma D_6bea0 : decode_any W_6bea0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bea4 : bv 32 := 0xf01a0a13.
Lemma F_6bea4 : fetch_word Asan.M.loaded_segments (0x6bea4 : word) = Some W_6bea4.
Proof. vm_refl. Qed.
Lemma D_6bea4 : decode_any W_6bea4 = Some (OpImm ALU_ADD 20 20 3841, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bea8 : bv 32 := 0x00050b13.
Lemma F_6bea8 : fetch_word Asan.M.loaded_segments (0x6bea8 : word) = Some W_6bea8.
Proof. vm_refl. Qed.
Lemma D_6bea8 : decode_any W_6bea8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beac : bv 32 := 0x074cfa63.
Lemma F_6beac : fetch_word Asan.M.loaded_segments (0x6beac : word) = Some W_6beac.
Proof. vm_refl. Qed.
Lemma D_6beac : decode_any W_6beac = Some (Branch BC_GEU 25 20 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beb0 : bv 32 := 0x000b3503.
Lemma F_6beb0 : fetch_word Asan.M.loaded_segments (0x6beb0 : word) = Some W_6beb0.
Proof. vm_refl. Qed.
Lemma D_6beb0 : decode_any W_6beb0 = Some (Load SZ8 true 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beb4 : bv 32 := 0x0230000f.
Lemma F_6beb4 : fetch_word Asan.M.loaded_segments (0x6beb4 : word) = Some W_6beb4.
Proof. vm_refl. Qed.
Lemma D_6beb4 : decode_any W_6beb4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beb8 : bv 32 := 0xffb504e3.
Lemma F_6beb8 : fetch_word Asan.M.loaded_segments (0x6beb8 : word) = Some W_6beb8.
Proof. vm_refl. Qed.
Lemma D_6beb8 : decode_any W_6beb8 = Some (Branch BC_EQ 10 27 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bebc : bv 32 := 0xfe0514e3.
Lemma F_6bebc : fetch_word Asan.M.loaded_segments (0x6bebc : word) = Some W_6bebc.
Proof. vm_refl. Qed.
Lemma D_6bebc : decode_any W_6bebc = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bec0 : bv 32 := 0x000c0513.
Lemma F_6bec0 : fetch_word Asan.M.loaded_segments (0x6bec0 : word) = Some W_6bec0.
Proof. vm_refl. Qed.
Lemma D_6bec0 : decode_any W_6bec0 = Some (OpImm ALU_ADD 10 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bec4 : bv 32 := 0x000b8593.
Lemma F_6bec4 : fetch_word Asan.M.loaded_segments (0x6bec4 : word) = Some W_6bec4.
Proof. vm_refl. Qed.
Lemma D_6bec4 : decode_any W_6bec4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bec8 : bv 32 := 0x00000613.
Lemma F_6bec8 : fetch_word Asan.M.loaded_segments (0x6bec8 : word) = Some W_6bec8.
Proof. vm_refl. Qed.
Lemma D_6bec8 : decode_any W_6bec8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6becc : bv 32 := 0x9c0fc0ef.
Lemma F_6becc : fetch_word Asan.M.loaded_segments (0x6becc : word) = Some W_6becc.
Proof. vm_refl. Qed.
Lemma D_6becc : decode_any W_6becc = Some (Jal 1 2081216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bed0 : bv 32 := 0x160b34af.
Lemma F_6bed0 : fetch_word Asan.M.loaded_segments (0x6bed0 : word) = Some W_6bed0.
Proof. vm_refl. Qed.
Lemma D_6bed0 : decode_any W_6bed0 = Some (Lr AD true true 9 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bed4 : bv 32 := 0x02049a63.
Lemma F_6bed4 : fetch_word Asan.M.loaded_segments (0x6bed4 : word) = Some W_6bed4.
Proof. vm_refl. Qed.
Lemma D_6bed4 : decode_any W_6bed4 = Some (Branch BC_NE 9 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bed8 : bv 32 := 0x1aab35af.
Lemma F_6bed8 : fetch_word Asan.M.loaded_segments (0x6bed8 : word) = Some W_6bed8.
Proof. vm_refl. Qed.
Lemma D_6bed8 : decode_any W_6bed8 = Some (Sc AD false true 11 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bedc : bv 32 := 0xfe059ae3.
Lemma F_6bedc : fetch_word Asan.M.loaded_segments (0x6bedc : word) = Some W_6bedc.
Proof. vm_refl. Qed.
Lemma D_6bedc : decode_any W_6bedc = Some (Branch BC_NE 11 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bee0 : bv 32 := 0x00100593.
Lemma F_6bee0 : fetch_word Asan.M.loaded_segments (0x6bee0 : word) = Some W_6bee0.
Proof. vm_refl. Qed.
Lemma D_6bee0 : decode_any W_6bee0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bee4 : bv 32 := 0x00b4362f.
Lemma F_6bee4 : fetch_word Asan.M.loaded_segments (0x6bee4 : word) = Some W_6bee4.
Proof. vm_refl. Qed.
Lemma D_6bee4 : decode_any W_6bee4 = Some (Amo AMO_ADD AD false false 12 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bee8 : bv 32 := 0x000d2583.
Lemma F_6bee8 : fetch_word Asan.M.loaded_segments (0x6bee8 : word) = Some W_6bee8.
Proof. vm_refl. Qed.
Lemma D_6bee8 : decode_any W_6bee8 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beec : bv 32 := 0x00200693.
Lemma F_6beec : fetch_word Asan.M.loaded_segments (0x6beec : word) = Some W_6beec.
Proof. vm_refl. Qed.
Lemma D_6beec : decode_any W_6beec = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bef0 : bv 32 := 0xfad5eae3.
Lemma F_6bef0 : fetch_word Asan.M.loaded_segments (0x6bef0 : word) = Some W_6bef0.
Proof. vm_refl. Qed.
Lemma D_6bef0 : decode_any W_6bef0 = Some (Branch BC_LTU 11 13 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bef4 : bv 32 := 0x00050493.
Lemma F_6bef4 : fetch_word Asan.M.loaded_segments (0x6bef4 : word) = Some W_6bef4.
Proof. vm_refl. Qed.
Lemma D_6bef4 : decode_any W_6bef4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bef8 : bv 32 := 0x00813503.
Lemma F_6bef8 : fetch_word Asan.M.loaded_segments (0x6bef8 : word) = Some W_6bef8.
Proof. vm_refl. Qed.
Lemma D_6bef8 : decode_any W_6bef8 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6befc : bv 32 := 0x000a8593.
Lemma F_6befc : fetch_word Asan.M.loaded_segments (0x6befc : word) = Some W_6befc.
Proof. vm_refl. Qed.
Lemma D_6befc : decode_any W_6befc = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf00 : bv 32 := 0xee4fd0ef.
Lemma F_6bf00 : fetch_word Asan.M.loaded_segments (0x6bf00 : word) = Some W_6bf00.
Proof. vm_refl. Qed.
Lemma D_6bf00 : decode_any W_6bf00 = Some (Jal 1 2086628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf04 : bv 32 := 0x0100006f.
Lemma F_6bf04 : fetch_word Asan.M.loaded_segments (0x6bf04 : word) = Some W_6bf04.
Proof. vm_refl. Qed.
Lemma D_6bf04 : decode_any W_6bf04 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf08 : bv 32 := 0x000c0593.
Lemma F_6bf08 : fetch_word Asan.M.loaded_segments (0x6bf08 : word) = Some W_6bf08.
Proof. vm_refl. Qed.
Lemma D_6bf08 : decode_any W_6bf08 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf0c : bv 32 := 0x00000613.
Lemma F_6bf0c : fetch_word Asan.M.loaded_segments (0x6bf0c : word) = Some W_6bf0c.
Proof. vm_refl. Qed.
Lemma D_6bf0c : decode_any W_6bf0c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf10 : bv 32 := 0xafcfc0ef.
Lemma F_6bf10 : fetch_word Asan.M.loaded_segments (0x6bf10 : word) = Some W_6bf10.
Proof. vm_refl. Qed.
Lemma D_6bf10 : decode_any W_6bf10 = Some (Jal 1 2081532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf14 : bv 32 := 0x00048513.
Lemma F_6bf14 : fetch_word Asan.M.loaded_segments (0x6bf14 : word) = Some W_6bf14.
Proof. vm_refl. Qed.
Lemma D_6bf14 : decode_any W_6bf14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf18 : bv 32 := 0xf8dff06f.
Lemma F_6bf18 : fetch_word Asan.M.loaded_segments (0x6bf18 : word) = Some W_6bf18.
Proof. vm_refl. Qed.
Lemma D_6bf18 : decode_any W_6bf18 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf1c : bv 32 := 0x000b0513.
Lemma F_6bf1c : fetch_word Asan.M.loaded_segments (0x6bf1c : word) = Some W_6bf1c.
Proof. vm_refl. Qed.
Lemma D_6bf1c : decode_any W_6bf1c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf20 : bv 32 := 0x004a1413.
Lemma F_6bf20 : fetch_word Asan.M.loaded_segments (0x6bf20 : word) = Some W_6bf20.
Proof. vm_refl. Qed.
Lemma D_6bf20 : decode_any W_6bf20 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf24 : bv 32 := 0x00850433.
Lemma F_6bf24 : fetch_word Asan.M.loaded_segments (0x6bf24 : word) = Some W_6bf24.
Proof. vm_refl. Qed.
Lemma D_6bf24 : decode_any W_6bf24 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf28 : bv 32 := 0x00843503.
Lemma F_6bf28 : fetch_word Asan.M.loaded_segments (0x6bf28 : word) = Some W_6bf28.
Proof. vm_refl. Qed.
Lemma D_6bf28 : decode_any W_6bf28 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf2c : bv 32 := 0x04050263.
Lemma F_6bf2c : fetch_word Asan.M.loaded_segments (0x6bf2c : word) = Some W_6bf2c.
Proof. vm_refl. Qed.
Lemma D_6bf2c : decode_any W_6bf2c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf30 : bv 32 := 0x00000513.
Lemma F_6bf30 : fetch_word Asan.M.loaded_segments (0x6bf30 : word) = Some W_6bf30.
Proof. vm_refl. Qed.
Lemma D_6bf30 : decode_any W_6bf30 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf34 : bv 32 := 0x08813083.
Lemma F_6bf34 : fetch_word Asan.M.loaded_segments (0x6bf34 : word) = Some W_6bf34.
Proof. vm_refl. Qed.
Lemma D_6bf34 : decode_any W_6bf34 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf38 : bv 32 := 0x08013403.
Lemma F_6bf38 : fetch_word Asan.M.loaded_segments (0x6bf38 : word) = Some W_6bf38.
Proof. vm_refl. Qed.
Lemma D_6bf38 : decode_any W_6bf38 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf3c : bv 32 := 0x07813483.
Lemma F_6bf3c : fetch_word Asan.M.loaded_segments (0x6bf3c : word) = Some W_6bf3c.
Proof. vm_refl. Qed.
Lemma D_6bf3c : decode_any W_6bf3c = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf40 : bv 32 := 0x07013903.
Lemma F_6bf40 : fetch_word Asan.M.loaded_segments (0x6bf40 : word) = Some W_6bf40.
Proof. vm_refl. Qed.
Lemma D_6bf40 : decode_any W_6bf40 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf44 : bv 32 := 0x06813983.
Lemma F_6bf44 : fetch_word Asan.M.loaded_segments (0x6bf44 : word) = Some W_6bf44.
Proof. vm_refl. Qed.
Lemma D_6bf44 : decode_any W_6bf44 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf48 : bv 32 := 0x06013a03.
Lemma F_6bf48 : fetch_word Asan.M.loaded_segments (0x6bf48 : word) = Some W_6bf48.
Proof. vm_refl. Qed.
Lemma D_6bf48 : decode_any W_6bf48 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf4c : bv 32 := 0x05813a83.
Lemma F_6bf4c : fetch_word Asan.M.loaded_segments (0x6bf4c : word) = Some W_6bf4c.
Proof. vm_refl. Qed.
Lemma D_6bf4c : decode_any W_6bf4c = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf50 : bv 32 := 0x05013b03.
Lemma F_6bf50 : fetch_word Asan.M.loaded_segments (0x6bf50 : word) = Some W_6bf50.
Proof. vm_refl. Qed.
Lemma D_6bf50 : decode_any W_6bf50 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf54 : bv 32 := 0x04813b83.
Lemma F_6bf54 : fetch_word Asan.M.loaded_segments (0x6bf54 : word) = Some W_6bf54.
Proof. vm_refl. Qed.
Lemma D_6bf54 : decode_any W_6bf54 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf58 : bv 32 := 0x04013c03.
Lemma F_6bf58 : fetch_word Asan.M.loaded_segments (0x6bf58 : word) = Some W_6bf58.
Proof. vm_refl. Qed.
Lemma D_6bf58 : decode_any W_6bf58 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf5c : bv 32 := 0x03813c83.
Lemma F_6bf5c : fetch_word Asan.M.loaded_segments (0x6bf5c : word) = Some W_6bf5c.
Proof. vm_refl. Qed.
Lemma D_6bf5c : decode_any W_6bf5c = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf60 : bv 32 := 0x03013d03.
Lemma F_6bf60 : fetch_word Asan.M.loaded_segments (0x6bf60 : word) = Some W_6bf60.
Proof. vm_refl. Qed.
Lemma D_6bf60 : decode_any W_6bf60 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf64 : bv 32 := 0x02813d83.
Lemma F_6bf64 : fetch_word Asan.M.loaded_segments (0x6bf64 : word) = Some W_6bf64.
Proof. vm_refl. Qed.
Lemma D_6bf64 : decode_any W_6bf64 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf68 : bv 32 := 0x09010113.
Lemma F_6bf68 : fetch_word Asan.M.loaded_segments (0x6bf68 : word) = Some W_6bf68.
Proof. vm_refl. Qed.
Lemma D_6bf68 : decode_any W_6bf68 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf6c : bv 32 := 0x00008067.
Lemma F_6bf6c : fetch_word Asan.M.loaded_segments (0x6bf6c : word) = Some W_6bf6c.
Proof. vm_refl. Qed.
Lemma D_6bf6c : decode_any W_6bf6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a4da0 : bv 32 := 0x00020593.
Lemma F_a4da0 : fetch_word Asan.M.loaded_segments (0xa4da0 : word) = Some W_a4da0.
Proof. vm_refl. Qed.
Lemma D_a4da0 : decode_any W_a4da0 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4da4 : bv 32 := 0x00053603.
Lemma F_a4da4 : fetch_word Asan.M.loaded_segments (0xa4da4 : word) = Some W_a4da4.
Proof. vm_refl. Qed.
Lemma D_a4da4 : decode_any W_a4da4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4da8 : bv 32 := 0xff85b583.
Lemma F_a4da8 : fetch_word Asan.M.loaded_segments (0xa4da8 : word) = Some W_a4da8.
Proof. vm_refl. Qed.
Lemma D_a4da8 : decode_any W_a4da8 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4dac : bv 32 := 0x00853503.
Lemma F_a4dac : fetch_word Asan.M.loaded_segments (0xa4dac : word) = Some W_a4dac.
Proof. vm_refl. Qed.
Lemma D_a4dac : decode_any W_a4dac = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4db0 : bv 32 := 0x00361613.
Lemma F_a4db0 : fetch_word Asan.M.loaded_segments (0xa4db0 : word) = Some W_a4db0.
Proof. vm_refl. Qed.
Lemma D_a4db0 : decode_any W_a4db0 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4db4 : bv 32 := 0x00c585b3.
Lemma F_a4db4 : fetch_word Asan.M.loaded_segments (0xa4db4 : word) = Some W_a4db4.
Proof. vm_refl. Qed.
Lemma D_a4db4 : decode_any W_a4db4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4db8 : bv 32 := 0x0005b583.
Lemma F_a4db8 : fetch_word Asan.M.loaded_segments (0xa4db8 : word) = Some W_a4db8.
Proof. vm_refl. Qed.
Lemma D_a4db8 : decode_any W_a4db8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4dbc : bv 32 := 0x00b50533.
Lemma F_a4dbc : fetch_word Asan.M.loaded_segments (0xa4dbc : word) = Some W_a4dbc.
Proof. vm_refl. Qed.
Lemma D_a4dbc : decode_any W_a4dbc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4dc0 : bv 32 := 0x00008067.
Lemma F_a4dc0 : fetch_word Asan.M.loaded_segments (0xa4dc0 : word) = Some W_a4dc0.
Proof. vm_refl. Qed.
Lemma D_a4dc0 : decode_any W_a4dc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a6090 : bv 32 := 0x00020593.
Lemma F_a6090 : fetch_word Asan.M.loaded_segments (0xa6090 : word) = Some W_a6090.
Proof. vm_refl. Qed.
Lemma D_a6090 : decode_any W_a6090 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6094 : bv 32 := 0xfa85b583.
Lemma F_a6094 : fetch_word Asan.M.loaded_segments (0xa6094 : word) = Some W_a6094.
Proof. vm_refl. Qed.
Lemma D_a6094 : decode_any W_a6094 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6098 : bv 32 := 0x02051513.
Lemma F_a6098 : fetch_word Asan.M.loaded_segments (0xa6098 : word) = Some W_a6098.
Proof. vm_refl. Qed.
Lemma D_a6098 : decode_any W_a6098 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a609c : bv 32 := 0x01d55513.
Lemma F_a609c : fetch_word Asan.M.loaded_segments (0xa609c : word) = Some W_a609c.
Proof. vm_refl. Qed.
Lemma D_a609c : decode_any W_a609c = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a60a0 : bv 32 := 0x00a58533.
Lemma F_a60a0 : fetch_word Asan.M.loaded_segments (0xa60a0 : word) = Some W_a60a0.
Proof. vm_refl. Qed.
Lemma D_a60a0 : decode_any W_a60a0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a60a4 : bv 32 := 0x00053503.
Lemma F_a60a4 : fetch_word Asan.M.loaded_segments (0xa60a4 : word) = Some W_a60a4.
Proof. vm_refl. Qed.
Lemma D_a60a4 : decode_any W_a60a4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a60a8 : bv 32 := 0x00008067.
Lemma F_a60a8 : fetch_word Asan.M.loaded_segments (0xa60a8 : word) = Some W_a60a8.
Proof. vm_refl. Qed.
Lemma D_a60a8 : decode_any W_a60a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
