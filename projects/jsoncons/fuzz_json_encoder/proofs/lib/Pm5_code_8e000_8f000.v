(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8e794 : bv 32 := 0xfd010113.
Lemma F_8e794 : fetch_word AsanUbsan.M.loaded_segments (0x8e7dc : word) = Some W_8e794.
Proof. vm_refl. Qed.
Lemma D_8e794 : decode_any W_8e794 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e798 : bv 32 := 0x02113423.
Lemma F_8e798 : fetch_word AsanUbsan.M.loaded_segments (0x8e7e0 : word) = Some W_8e798.
Proof. vm_refl. Qed.
Lemma D_8e798 : decode_any W_8e798 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e79c : bv 32 := 0x02813023.
Lemma F_8e79c : fetch_word AsanUbsan.M.loaded_segments (0x8e7e4 : word) = Some W_8e79c.
Proof. vm_refl. Qed.
Lemma D_8e79c : decode_any W_8e79c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7a0 : bv 32 := 0x00913c23.
Lemma F_8e7a0 : fetch_word AsanUbsan.M.loaded_segments (0x8e7e8 : word) = Some W_8e7a0.
Proof. vm_refl. Qed.
Lemma D_8e7a0 : decode_any W_8e7a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7a4 : bv 32 := 0x01213823.
Lemma F_8e7a4 : fetch_word AsanUbsan.M.loaded_segments (0x8e7ec : word) = Some W_8e7a4.
Proof. vm_refl. Qed.
Lemma D_8e7a4 : decode_any W_8e7a4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7a8 : bv 32 := 0x01313423.
Lemma F_8e7a8 : fetch_word AsanUbsan.M.loaded_segments (0x8e7f0 : word) = Some W_8e7a8.
Proof. vm_refl. Qed.
Lemma D_8e7a8 : decode_any W_8e7a8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7ac : bv 32 := 0x0016f517.
Lemma F_8e7ac : fetch_word AsanUbsan.M.loaded_segments (0x8e7f4 : word) = Some W_8e7ac.
Proof. vm_refl. Qed.
Lemma D_8e7ac : decode_any W_8e7ac = Some (Auipc 10 367, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7b0 : bv 32 := 0xa5450413.
Lemma F_8e7b0 : fetch_word AsanUbsan.M.loaded_segments (0x8e7f8 : word) = Some W_8e7b0.
Proof. vm_refl. Qed.
Lemma D_8e7b0 : decode_any W_8e7b0 = Some (OpImm ALU_ADD 8 10 2644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7b4 : bv 32 := 0x00040503.
Lemma F_8e7b4 : fetch_word AsanUbsan.M.loaded_segments (0x8e7fc : word) = Some W_8e7b4.
Proof. vm_refl. Qed.
Lemma D_8e7b4 : decode_any W_8e7b4 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7b8 : bv 32 := 0x0230000f.
Lemma F_8e7b8 : fetch_word AsanUbsan.M.loaded_segments (0x8e800 : word) = Some W_8e7b8.
Proof. vm_refl. Qed.
Lemma D_8e7b8 : decode_any W_8e7b8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7bc : bv 32 := 0x0e051e63.
Lemma F_8e7bc : fetch_word AsanUbsan.M.loaded_segments (0x8e804 : word) = Some W_8e7bc.
Proof. vm_refl. Qed.
Lemma D_8e7bc : decode_any W_8e7bc = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7c0 : bv 32 := 0x00140513.
Lemma F_8e7c0 : fetch_word AsanUbsan.M.loaded_segments (0x8e808 : word) = Some W_8e7c0.
Proof. vm_refl. Qed.
Lemma D_8e7c0 : decode_any W_8e7c0 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7c4 : bv 32 := 0x0ff00593.
Lemma F_8e7c4 : fetch_word AsanUbsan.M.loaded_segments (0x8e80c : word) = Some W_8e7c4.
Proof. vm_refl. Qed.
Lemma D_8e7c4 : decode_any W_8e7c4 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7c8 : bv 32 := 0x00100613.
Lemma F_8e7c8 : fetch_word AsanUbsan.M.loaded_segments (0x8e810 : word) = Some W_8e7c8.
Proof. vm_refl. Qed.
Lemma D_8e7c8 : decode_any W_8e7c8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7cc : bv 32 := 0xffc57693.
Lemma F_8e7cc : fetch_word AsanUbsan.M.loaded_segments (0x8e814 : word) = Some W_8e7cc.
Proof. vm_refl. Qed.
Lemma D_8e7cc : decode_any W_8e7cc = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7d0 : bv 32 := 0x00357713.
Lemma F_8e7d0 : fetch_word AsanUbsan.M.loaded_segments (0x8e818 : word) = Some W_8e7d0.
Proof. vm_refl. Qed.
Lemma D_8e7d0 : decode_any W_8e7d0 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7d4 : bv 32 := 0x00371713.
Lemma F_8e7d4 : fetch_word AsanUbsan.M.loaded_segments (0x8e81c : word) = Some W_8e7d4.
Proof. vm_refl. Qed.
Lemma D_8e7d4 : decode_any W_8e7d4 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7d8 : bv 32 := 0x00e595bb.
Lemma F_8e7d8 : fetch_word AsanUbsan.M.loaded_segments (0x8e820 : word) = Some W_8e7d8.
Proof. vm_refl. Qed.
Lemma D_8e7d8 : decode_any W_8e7d8 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7dc : bv 32 := 0x00e6163b.
Lemma F_8e7dc : fetch_word AsanUbsan.M.loaded_segments (0x8e824 : word) = Some W_8e7dc.
Proof. vm_refl. Qed.
Lemma D_8e7dc : decode_any W_8e7dc = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7e0 : bv 32 := 0x1406a7af.
Lemma F_8e7e0 : fetch_word AsanUbsan.M.loaded_segments (0x8e828 : word) = Some W_8e7e0.
Proof. vm_refl. Qed.
Lemma D_8e7e0 : decode_any W_8e7e0 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7e4 : bv 32 := 0x00060813.
Lemma F_8e7e4 : fetch_word AsanUbsan.M.loaded_segments (0x8e82c : word) = Some W_8e7e4.
Proof. vm_refl. Qed.
Lemma D_8e7e4 : decode_any W_8e7e4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7e8 : bv 32 := 0x0107c833.
Lemma F_8e7e8 : fetch_word AsanUbsan.M.loaded_segments (0x8e830 : word) = Some W_8e7e8.
Proof. vm_refl. Qed.
Lemma D_8e7e8 : decode_any W_8e7e8 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7ec : bv 32 := 0x00b87833.
Lemma F_8e7ec : fetch_word AsanUbsan.M.loaded_segments (0x8e834 : word) = Some W_8e7ec.
Proof. vm_refl. Qed.
Lemma D_8e7ec : decode_any W_8e7ec = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7f0 : bv 32 := 0x0107c833.
Lemma F_8e7f0 : fetch_word AsanUbsan.M.loaded_segments (0x8e838 : word) = Some W_8e7f0.
Proof. vm_refl. Qed.
Lemma D_8e7f0 : decode_any W_8e7f0 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7f4 : bv 32 := 0x1906a82f.
Lemma F_8e7f4 : fetch_word AsanUbsan.M.loaded_segments (0x8e83c : word) = Some W_8e7f4.
Proof. vm_refl. Qed.
Lemma D_8e7f4 : decode_any W_8e7f4 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7f8 : bv 32 := 0xfe0814e3.
Lemma F_8e7f8 : fetch_word AsanUbsan.M.loaded_segments (0x8e840 : word) = Some W_8e7f8.
Proof. vm_refl. Qed.
Lemma D_8e7f8 : decode_any W_8e7f8 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e7fc : bv 32 := 0x00e7d5bb.
Lemma F_8e7fc : fetch_word AsanUbsan.M.loaded_segments (0x8e844 : word) = Some W_8e7fc.
Proof. vm_refl. Qed.
Lemma D_8e7fc : decode_any W_8e7fc = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e800 : bv 32 := 0x0ff5f593.
Lemma F_8e800 : fetch_word AsanUbsan.M.loaded_segments (0x8e848 : word) = Some W_8e800.
Proof. vm_refl. Qed.
Lemma D_8e800 : decode_any W_8e800 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e804 : bv 32 := 0x0c059c63.
Lemma F_8e804 : fetch_word AsanUbsan.M.loaded_segments (0x8e84c : word) = Some W_8e804.
Proof. vm_refl. Qed.
Lemma D_8e804 : decode_any W_8e804 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e808 : bv 32 := 0x00040503.
Lemma F_8e808 : fetch_word AsanUbsan.M.loaded_segments (0x8e850 : word) = Some W_8e808.
Proof. vm_refl. Qed.
Lemma D_8e808 : decode_any W_8e808 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e80c : bv 32 := 0x0a051263.
Lemma F_8e80c : fetch_word AsanUbsan.M.loaded_segments (0x8e854 : word) = Some W_8e80c.
Proof. vm_refl. Qed.
Lemma D_8e80c : decode_any W_8e80c = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e810 : bv 32 := 0x000e0517.
Lemma F_8e810 : fetch_word AsanUbsan.M.loaded_segments (0x8e858 : word) = Some W_8e810.
Proof. vm_refl. Qed.
Lemma D_8e810 : decode_any W_8e810 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e814 : bv 32 := 0x000815b7.
Lemma F_8e814 : fetch_word AsanUbsan.M.loaded_segments (0x8e85c : word) = Some W_8e814.
Proof. vm_refl. Qed.
Lemma D_8e814 : decode_any W_8e814 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e818 : bv 32 := 0x16850493.
Lemma F_8e818 : fetch_word AsanUbsan.M.loaded_segments (0x8e860 : word) = Some W_8e818.
Proof. vm_refl. Qed.
Lemma D_8e818 : decode_any W_8e818 = Some (OpImm ALU_ADD 9 10 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e81c : bv 32 := 0x0085851b.
Lemma F_8e81c : fetch_word AsanUbsan.M.loaded_segments (0x8e864 : word) = Some W_8e81c.
Proof. vm_refl. Qed.
Lemma D_8e81c : decode_any W_8e81c = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e820 : bv 32 := 0x00a48533.
Lemma F_8e820 : fetch_word AsanUbsan.M.loaded_segments (0x8e868 : word) = Some W_8e820.
Proof. vm_refl. Qed.
Lemma D_8e820 : decode_any W_8e820 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e824 : bv 32 := 0x02800613.
Lemma F_8e824 : fetch_word AsanUbsan.M.loaded_segments (0x8e86c : word) = Some W_8e824.
Proof. vm_refl. Qed.
Lemma D_8e824 : decode_any W_8e824 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e828 : bv 32 := 0x00000593.
Lemma F_8e828 : fetch_word AsanUbsan.M.loaded_segments (0x8e870 : word) = Some W_8e828.
Proof. vm_refl. Qed.
Lemma D_8e828 : decode_any W_8e828 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e82c : bv 32 := 0x269050ef.
Lemma F_8e82c : fetch_word AsanUbsan.M.loaded_segments (0x8e874 : word) = Some W_8e82c.
Proof. vm_refl. Qed.
Lemma D_8e82c : decode_any W_8e82c = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e830 : bv 32 := 0x00048023.
Lemma F_8e830 : fetch_word AsanUbsan.M.loaded_segments (0x8e878 : word) = Some W_8e830.
Proof. vm_refl. Qed.
Lemma D_8e830 : decode_any W_8e830 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e834 : bv 32 := 0x00848513.
Lemma F_8e834 : fetch_word AsanUbsan.M.loaded_segments (0x8e87c : word) = Some W_8e834.
Proof. vm_refl. Qed.
Lemma D_8e834 : decode_any W_8e834 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e838 : bv 32 := 0x00040637.
Lemma F_8e838 : fetch_word AsanUbsan.M.loaded_segments (0x8e880 : word) = Some W_8e838.
Proof. vm_refl. Qed.
Lemma D_8e838 : decode_any W_8e838 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e83c : bv 32 := 0x000409b7.
Lemma F_8e83c : fetch_word AsanUbsan.M.loaded_segments (0x8e884 : word) = Some W_8e83c.
Proof. vm_refl. Qed.
Lemma D_8e83c : decode_any W_8e83c = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e840 : bv 32 := 0x00000593.
Lemma F_8e840 : fetch_word AsanUbsan.M.loaded_segments (0x8e888 : word) = Some W_8e840.
Proof. vm_refl. Qed.
Lemma D_8e840 : decode_any W_8e840 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e844 : bv 32 := 0x251050ef.
Lemma F_8e844 : fetch_word AsanUbsan.M.loaded_segments (0x8e88c : word) = Some W_8e844.
Proof. vm_refl. Qed.
Lemma D_8e844 : decode_any W_8e844 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e848 : bv 32 := 0x0409851b.
Lemma F_8e848 : fetch_word AsanUbsan.M.loaded_segments (0x8e890 : word) = Some W_8e848.
Proof. vm_refl. Qed.
Lemma D_8e848 : decode_any W_8e848 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e84c : bv 32 := 0x00a48533.
Lemma F_8e84c : fetch_word AsanUbsan.M.loaded_segments (0x8e894 : word) = Some W_8e84c.
Proof. vm_refl. Qed.
Lemma D_8e84c : decode_any W_8e84c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e850 : bv 32 := 0x01b00613.
Lemma F_8e850 : fetch_word AsanUbsan.M.loaded_segments (0x8e898 : word) = Some W_8e850.
Proof. vm_refl. Qed.
Lemma D_8e850 : decode_any W_8e850 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e854 : bv 32 := 0x00761613.
Lemma F_8e854 : fetch_word AsanUbsan.M.loaded_segments (0x8e89c : word) = Some W_8e854.
Proof. vm_refl. Qed.
Lemma D_8e854 : decode_any W_8e854 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e858 : bv 32 := 0x00000593.
Lemma F_8e858 : fetch_word AsanUbsan.M.loaded_segments (0x8e8a0 : word) = Some W_8e858.
Proof. vm_refl. Qed.
Lemma D_8e858 : decode_any W_8e858 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e85c : bv 32 := 0x239050ef.
Lemma F_8e85c : fetch_word AsanUbsan.M.loaded_segments (0x8e8a4 : word) = Some W_8e85c.
Proof. vm_refl. Qed.
Lemma D_8e85c : decode_any W_8e85c = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e860 : bv 32 := 0x00041937.
Lemma F_8e860 : fetch_word AsanUbsan.M.loaded_segments (0x8e8a8 : word) = Some W_8e860.
Proof. vm_refl. Qed.
Lemma D_8e860 : decode_any W_8e860 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e864 : bv 32 := 0xdc09051b.
Lemma F_8e864 : fetch_word AsanUbsan.M.loaded_segments (0x8e8ac : word) = Some W_8e864.
Proof. vm_refl. Qed.
Lemma D_8e864 : decode_any W_8e864 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e868 : bv 32 := 0x00a48533.
Lemma F_8e868 : fetch_word AsanUbsan.M.loaded_segments (0x8e8b0 : word) = Some W_8e868.
Proof. vm_refl. Qed.
Lemma D_8e868 : decode_any W_8e868 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e86c : bv 32 := 0x2489861b.
Lemma F_8e86c : fetch_word AsanUbsan.M.loaded_segments (0x8e8b4 : word) = Some W_8e86c.
Proof. vm_refl. Qed.
Lemma D_8e86c : decode_any W_8e86c = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e870 : bv 32 := 0x00000593.
Lemma F_8e870 : fetch_word AsanUbsan.M.loaded_segments (0x8e8b8 : word) = Some W_8e870.
Proof. vm_refl. Qed.
Lemma D_8e870 : decode_any W_8e870 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e874 : bv 32 := 0x221050ef.
Lemma F_8e874 : fetch_word AsanUbsan.M.loaded_segments (0x8e8bc : word) = Some W_8e874.
Proof. vm_refl. Qed.
Lemma D_8e874 : decode_any W_8e874 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e878 : bv 32 := 0x000d6517.
Lemma F_8e878 : fetch_word AsanUbsan.M.loaded_segments (0x8e8c0 : word) = Some W_8e878.
Proof. vm_refl. Qed.
Lemma D_8e878 : decode_any W_8e878 = Some (Auipc 10 214, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e87c : bv 32 := 0xc3853983.
Lemma F_8e87c : fetch_word AsanUbsan.M.loaded_segments (0x8e8c4 : word) = Some W_8e87c.
Proof. vm_refl. Qed.
Lemma D_8e87c : decode_any W_8e87c = Some (Load SZ8 true 19 10 3128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e880 : bv 32 := 0x0009b503.
Lemma F_8e880 : fetch_word AsanUbsan.M.loaded_segments (0x8e8c8 : word) = Some W_8e880.
Proof. vm_refl. Qed.
Lemma D_8e880 : decode_any W_8e880 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e884 : bv 32 := 0x00051663.
Lemma F_8e884 : fetch_word AsanUbsan.M.loaded_segments (0x8e8cc : word) = Some W_8e884.
Proof. vm_refl. Qed.
Lemma D_8e884 : decode_any W_8e884 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e890 : bv 32 := 0x012485b3.
Lemma F_8e890 : fetch_word AsanUbsan.M.loaded_segments (0x8e8d8 : word) = Some W_8e890.
Proof. vm_refl. Qed.
Lemma D_8e890 : decode_any W_8e890 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e894 : bv 32 := 0xdd09061b.
Lemma F_8e894 : fetch_word AsanUbsan.M.loaded_segments (0x8e8dc : word) = Some W_8e894.
Proof. vm_refl. Qed.
Lemma D_8e894 : decode_any W_8e894 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e898 : bv 32 := 0x00c48633.
Lemma F_8e898 : fetch_word AsanUbsan.M.loaded_segments (0x8e8e0 : word) = Some W_8e898.
Proof. vm_refl. Qed.
Lemma D_8e898 : decode_any W_8e898 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e89c : bv 32 := 0x00100693.
Lemma F_8e89c : fetch_word AsanUbsan.M.loaded_segments (0x8e8e4 : word) = Some W_8e89c.
Proof. vm_refl. Qed.
Lemma D_8e89c : decode_any W_8e89c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8a0 : bv 32 := 0xdca5b023.
Lemma F_8e8a0 : fetch_word AsanUbsan.M.loaded_segments (0x8e8e8 : word) = Some W_8e8a0.
Proof. vm_refl. Qed.
Lemma D_8e8a0 : decode_any W_8e8a0 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8a4 : bv 32 := 0xdcc5b423.
Lemma F_8e8a4 : fetch_word AsanUbsan.M.loaded_segments (0x8e8ec : word) = Some W_8e8a4.
Proof. vm_refl. Qed.
Lemma D_8e8a4 : decode_any W_8e8a4 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8a8 : bv 32 := 0x0310000f.
Lemma F_8e8a8 : fetch_word AsanUbsan.M.loaded_segments (0x8e8f0 : word) = Some W_8e8a8.
Proof. vm_refl. Qed.
Lemma D_8e8a8 : decode_any W_8e8a8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8ac : bv 32 := 0x00d40023.
Lemma F_8e8ac : fetch_word AsanUbsan.M.loaded_segments (0x8e8f4 : word) = Some W_8e8ac.
Proof. vm_refl. Qed.
Lemma D_8e8ac : decode_any W_8e8ac = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8b0 : bv 32 := 0x0310000f.
Lemma F_8e8b0 : fetch_word AsanUbsan.M.loaded_segments (0x8e8f8 : word) = Some W_8e8b0.
Proof. vm_refl. Qed.
Lemma D_8e8b0 : decode_any W_8e8b0 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8b4 : bv 32 := 0x000400a3.
Lemma F_8e8b4 : fetch_word AsanUbsan.M.loaded_segments (0x8e8fc : word) = Some W_8e8b4.
Proof. vm_refl. Qed.
Lemma D_8e8b4 : decode_any W_8e8b4 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8b8 : bv 32 := 0x000e0517.
Lemma F_8e8b8 : fetch_word AsanUbsan.M.loaded_segments (0x8e900 : word) = Some W_8e8b8.
Proof. vm_refl. Qed.
Lemma D_8e8b8 : decode_any W_8e8b8 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8bc : bv 32 := 0x0c050513.
Lemma F_8e8bc : fetch_word AsanUbsan.M.loaded_segments (0x8e904 : word) = Some W_8e8bc.
Proof. vm_refl. Qed.
Lemma D_8e8bc : decode_any W_8e8bc = Some (OpImm ALU_ADD 10 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8c0 : bv 32 := 0x02813083.
Lemma F_8e8c0 : fetch_word AsanUbsan.M.loaded_segments (0x8e908 : word) = Some W_8e8c0.
Proof. vm_refl. Qed.
Lemma D_8e8c0 : decode_any W_8e8c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8c4 : bv 32 := 0x02013403.
Lemma F_8e8c4 : fetch_word AsanUbsan.M.loaded_segments (0x8e90c : word) = Some W_8e8c4.
Proof. vm_refl. Qed.
Lemma D_8e8c4 : decode_any W_8e8c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8c8 : bv 32 := 0x01813483.
Lemma F_8e8c8 : fetch_word AsanUbsan.M.loaded_segments (0x8e910 : word) = Some W_8e8c8.
Proof. vm_refl. Qed.
Lemma D_8e8c8 : decode_any W_8e8c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8cc : bv 32 := 0x01013903.
Lemma F_8e8cc : fetch_word AsanUbsan.M.loaded_segments (0x8e914 : word) = Some W_8e8cc.
Proof. vm_refl. Qed.
Lemma D_8e8cc : decode_any W_8e8cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8d0 : bv 32 := 0x00813983.
Lemma F_8e8d0 : fetch_word AsanUbsan.M.loaded_segments (0x8e918 : word) = Some W_8e8d0.
Proof. vm_refl. Qed.
Lemma D_8e8d0 : decode_any W_8e8d0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8d4 : bv 32 := 0x03010113.
Lemma F_8e8d4 : fetch_word AsanUbsan.M.loaded_segments (0x8e91c : word) = Some W_8e8d4.
Proof. vm_refl. Qed.
Lemma D_8e8d4 : decode_any W_8e8d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e8d8 : bv 32 := 0x00008067.
Lemma F_8e8d8 : fetch_word AsanUbsan.M.loaded_segments (0x8e920 : word) = Some W_8e8d8.
Proof. vm_refl. Qed.
Lemma D_8e8d8 : decode_any W_8e8d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8eca8 : bv 32 := 0x00161517.
Lemma F_8eca8 : fetch_word AsanUbsan.M.loaded_segments (0x8ecf0 : word) = Some W_8eca8.
Proof. vm_refl. Qed.
Lemma D_8eca8 : decode_any W_8eca8 = Some (Auipc 10 353, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecac : bv 32 := 0xd3150503.
Lemma F_8ecac : fetch_word AsanUbsan.M.loaded_segments (0x8ecf4 : word) = Some W_8ecac.
Proof. vm_refl. Qed.
Lemma D_8ecac : decode_any W_8ecac = Some (Load SZ1 true 10 10 3377, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecb0 : bv 32 := 0x00a03533.
Lemma F_8ecb0 : fetch_word AsanUbsan.M.loaded_segments (0x8ecf8 : word) = Some W_8ecb0.
Proof. vm_refl. Qed.
Lemma D_8ecb0 : decode_any W_8ecb0 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecb4 : bv 32 := 0x00008067.
Lemma F_8ecb4 : fetch_word AsanUbsan.M.loaded_segments (0x8ecfc : word) = Some W_8ecb4.
Proof. vm_refl. Qed.
Lemma D_8ecb4 : decode_any W_8ecb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecd0 : bv 32 := 0x00161517.
Lemma F_8ecd0 : fetch_word AsanUbsan.M.loaded_segments (0x8ed18 : word) = Some W_8ecd0.
Proof. vm_refl. Qed.
Lemma D_8ecd0 : decode_any W_8ecd0 = Some (Auipc 10 353, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecd4 : bv 32 := 0xd0a50503.
Lemma F_8ecd4 : fetch_word AsanUbsan.M.loaded_segments (0x8ed1c : word) = Some W_8ecd4.
Proof. vm_refl. Qed.
Lemma D_8ecd4 : decode_any W_8ecd4 = Some (Load SZ1 true 10 10 3338, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecd8 : bv 32 := 0x00a03533.
Lemma F_8ecd8 : fetch_word AsanUbsan.M.loaded_segments (0x8ed20 : word) = Some W_8ecd8.
Proof. vm_refl. Qed.
Lemma D_8ecd8 : decode_any W_8ecd8 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ecdc : bv 32 := 0x00008067.
Lemma F_8ecdc : fetch_word AsanUbsan.M.loaded_segments (0x8ed24 : word) = Some W_8ecdc.
Proof. vm_refl. Qed.
Lemma D_8ecdc : decode_any W_8ecdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

