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
Definition W_a07fc : bv 32 := 0xfc010113.
Lemma F_a07fc : fetch_word AsanUbsan.M.loaded_segments (0xa0844 : word) = Some W_a07fc.
Proof. vm_refl. Qed.
Lemma D_a07fc : decode_any W_a07fc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0800 : bv 32 := 0x02113c23.
Lemma F_a0800 : fetch_word AsanUbsan.M.loaded_segments (0xa0848 : word) = Some W_a0800.
Proof. vm_refl. Qed.
Lemma D_a0800 : decode_any W_a0800 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0804 : bv 32 := 0x02813823.
Lemma F_a0804 : fetch_word AsanUbsan.M.loaded_segments (0xa084c : word) = Some W_a0804.
Proof. vm_refl. Qed.
Lemma D_a0804 : decode_any W_a0804 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0808 : bv 32 := 0x02913423.
Lemma F_a0808 : fetch_word AsanUbsan.M.loaded_segments (0xa0850 : word) = Some W_a0808.
Proof. vm_refl. Qed.
Lemma D_a0808 : decode_any W_a0808 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a080c : bv 32 := 0x03213023.
Lemma F_a080c : fetch_word AsanUbsan.M.loaded_segments (0xa0854 : word) = Some W_a080c.
Proof. vm_refl. Qed.
Lemma D_a080c : decode_any W_a080c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0810 : bv 32 := 0x01313c23.
Lemma F_a0810 : fetch_word AsanUbsan.M.loaded_segments (0xa0858 : word) = Some W_a0810.
Proof. vm_refl. Qed.
Lemma D_a0810 : decode_any W_a0810 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0814 : bv 32 := 0x01413823.
Lemma F_a0814 : fetch_word AsanUbsan.M.loaded_segments (0xa085c : word) = Some W_a0814.
Proof. vm_refl. Qed.
Lemma D_a0814 : decode_any W_a0814 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0818 : bv 32 := 0x01513423.
Lemma F_a0818 : fetch_word AsanUbsan.M.loaded_segments (0xa0860 : word) = Some W_a0818.
Proof. vm_refl. Qed.
Lemma D_a0818 : decode_any W_a0818 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a081c : bv 32 := 0x00058993.
Lemma F_a081c : fetch_word AsanUbsan.M.loaded_segments (0xa0864 : word) = Some W_a081c.
Proof. vm_refl. Qed.
Lemma D_a081c : decode_any W_a081c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0820 : bv 32 := 0x0085aa03.
Lemma F_a0820 : fetch_word AsanUbsan.M.loaded_segments (0xa0868 : word) = Some W_a0820.
Proof. vm_refl. Qed.
Lemma D_a0820 : decode_any W_a0820 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0824 : bv 32 := 0x00c5aa83.
Lemma F_a0824 : fetch_word AsanUbsan.M.loaded_segments (0xa086c : word) = Some W_a0824.
Proof. vm_refl. Qed.
Lemma D_a0824 : decode_any W_a0824 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0828 : bv 32 := 0x015a65b3.
Lemma F_a0828 : fetch_word AsanUbsan.M.loaded_segments (0xa0870 : word) = Some W_a0828.
Proof. vm_refl. Qed.
Lemma D_a0828 : decode_any W_a0828 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a082c : bv 32 := 0x00059663.
Lemma F_a082c : fetch_word AsanUbsan.M.loaded_segments (0xa0874 : word) = Some W_a082c.
Proof. vm_refl. Qed.
Lemma D_a082c : decode_any W_a082c = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0838 : bv 32 := 0x00050493.
Lemma F_a0838 : fetch_word AsanUbsan.M.loaded_segments (0xa0880 : word) = Some W_a0838.
Proof. vm_refl. Qed.
Lemma D_a0838 : decode_any W_a0838 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a083c : bv 32 := 0x10000513.
Lemma F_a083c : fetch_word AsanUbsan.M.loaded_segments (0xa0884 : word) = Some W_a083c.
Proof. vm_refl. Qed.
Lemma D_a083c : decode_any W_a083c = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0840 : bv 32 := 0x0aaafe63.
Lemma F_a0840 : fetch_word AsanUbsan.M.loaded_segments (0xa0888 : word) = Some W_a0840.
Proof. vm_refl. Qed.
Lemma D_a0840 : decode_any W_a0840 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0844 : bv 32 := 0x00060413.
Lemma F_a0844 : fetch_word AsanUbsan.M.loaded_segments (0xa088c : word) = Some W_a0844.
Proof. vm_refl. Qed.
Lemma D_a0844 : decode_any W_a0844 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0848 : bv 32 := 0x0ff00513.
Lemma F_a0848 : fetch_word AsanUbsan.M.loaded_segments (0xa0890 : word) = Some W_a0848.
Proof. vm_refl. Qed.
Lemma D_a0848 : decode_any W_a0848 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a084c : bv 32 := 0x00aa6463.
Lemma F_a084c : fetch_word AsanUbsan.M.loaded_segments (0xa0894 : word) = Some W_a084c.
Proof. vm_refl. Qed.
Lemma D_a084c : decode_any W_a084c = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0854 : bv 32 := 0x00013023.
Lemma F_a0854 : fetch_word AsanUbsan.M.loaded_segments (0xa089c : word) = Some W_a0854.
Proof. vm_refl. Qed.
Lemma D_a0854 : decode_any W_a0854 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0858 : bv 32 := 0x00043023.
Lemma F_a0858 : fetch_word AsanUbsan.M.loaded_segments (0xa08a0 : word) = Some W_a0858.
Proof. vm_refl. Qed.
Lemma D_a0858 : decode_any W_a0858 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a085c : bv 32 := 0x001a0913.
Lemma F_a085c : fetch_word AsanUbsan.M.loaded_segments (0xa08a4 : word) = Some W_a085c.
Proof. vm_refl. Qed.
Lemma D_a085c : decode_any W_a085c = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0860 : bv 32 := 0x00010613.
Lemma F_a0860 : fetch_word AsanUbsan.M.loaded_segments (0xa08a8 : word) = Some W_a0860.
Proof. vm_refl. Qed.
Lemma D_a0860 : decode_any W_a0860 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0864 : bv 32 := 0x00048513.
Lemma F_a0864 : fetch_word AsanUbsan.M.loaded_segments (0xa08ac : word) = Some W_a0864.
Proof. vm_refl. Qed.
Lemma D_a0864 : decode_any W_a0864 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0868 : bv 32 := 0x00090593.
Lemma F_a0868 : fetch_word AsanUbsan.M.loaded_segments (0xa08b0 : word) = Some W_a0868.
Proof. vm_refl. Qed.
Lemma D_a0868 : decode_any W_a0868 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a086c : bv 32 := 0x00040693.
Lemma F_a086c : fetch_word AsanUbsan.M.loaded_segments (0xa08b4 : word) = Some W_a086c.
Proof. vm_refl. Qed.
Lemma D_a086c : decode_any W_a086c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0870 : bv 32 := 0x0b0000ef.
Lemma F_a0870 : fetch_word AsanUbsan.M.loaded_segments (0xa08b8 : word) = Some W_a0870.
Proof. vm_refl. Qed.
Lemma D_a0870 : decode_any W_a0870 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0874 : bv 32 := 0x06050263.
Lemma F_a0874 : fetch_word AsanUbsan.M.loaded_segments (0xa08bc : word) = Some W_a0874.
Proof. vm_refl. Qed.
Lemma D_a0874 : decode_any W_a0874 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0878 : bv 32 := 0x008a961b.
Lemma F_a0878 : fetch_word AsanUbsan.M.loaded_segments (0xa08c0 : word) = Some W_a0878.
Proof. vm_refl. Qed.
Lemma D_a0878 : decode_any W_a0878 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a087c : bv 32 := 0x0009b583.
Lemma F_a087c : fetch_word AsanUbsan.M.loaded_segments (0xa08c4 : word) = Some W_a087c.
Proof. vm_refl. Qed.
Lemma D_a087c : decode_any W_a087c = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0880 : bv 32 := 0x01466633.
Lemma F_a0880 : fetch_word AsanUbsan.M.loaded_segments (0xa08c8 : word) = Some W_a0880.
Proof. vm_refl. Qed.
Lemma D_a0880 : decode_any W_a0880 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0884 : bv 32 := 0x00c53023.
Lemma F_a0884 : fetch_word AsanUbsan.M.loaded_segments (0xa08cc : word) = Some W_a0884.
Proof. vm_refl. Qed.
Lemma D_a0884 : decode_any W_a0884 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0888 : bv 32 := 0x00850513.
Lemma F_a0888 : fetch_word AsanUbsan.M.loaded_segments (0xa08d0 : word) = Some W_a0888.
Proof. vm_refl. Qed.
Lemma D_a0888 : decode_any W_a0888 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a088c : bv 32 := 0x003a1613.
Lemma F_a088c : fetch_word AsanUbsan.M.loaded_segments (0xa08d4 : word) = Some W_a088c.
Proof. vm_refl. Qed.
Lemma D_a088c : decode_any W_a088c = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0890 : bv 32 := 0x989f30ef.
Lemma F_a0890 : fetch_word AsanUbsan.M.loaded_segments (0xa08d8 : word) = Some W_a0890.
Proof. vm_refl. Qed.
Lemma D_a0890 : decode_any W_a0890 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0894 : bv 32 := 0x00013503.
Lemma F_a0894 : fetch_word AsanUbsan.M.loaded_segments (0xa08dc : word) = Some W_a0894.
Proof. vm_refl. Qed.
Lemma D_a0894 : decode_any W_a0894 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0898 : bv 32 := 0x01055513.
Lemma F_a0898 : fetch_word AsanUbsan.M.loaded_segments (0xa08e0 : word) = Some W_a0898.
Proof. vm_refl. Qed.
Lemma D_a0898 : decode_any W_a0898 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a089c : bv 32 := 0xff057513.
Lemma F_a089c : fetch_word AsanUbsan.M.loaded_segments (0xa08e4 : word) = Some W_a089c.
Proof. vm_refl. Qed.
Lemma D_a089c : decode_any W_a089c = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08a0 : bv 32 := 0x00a48533.
Lemma F_a08a0 : fetch_word AsanUbsan.M.loaded_segments (0xa08e8 : word) = Some W_a08a0.
Proof. vm_refl. Qed.
Lemma D_a08a0 : decode_any W_a08a0 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08a4 : bv 32 := 0x01850513.
Lemma F_a08a4 : fetch_word AsanUbsan.M.loaded_segments (0xa08ec : word) = Some W_a08a4.
Proof. vm_refl. Qed.
Lemma D_a08a4 : decode_any W_a08a4 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08a8 : bv 32 := 0x0325252f.
Lemma F_a08a8 : fetch_word AsanUbsan.M.loaded_segments (0xa08f0 : word) = Some W_a08a8.
Proof. vm_refl. Qed.
Lemma D_a08a8 : decode_any W_a08a8 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08ac : bv 32 := 0x001005b7.
Lemma F_a08ac : fetch_word AsanUbsan.M.loaded_segments (0xa08f4 : word) = Some W_a08ac.
Proof. vm_refl. Qed.
Lemma D_a08ac : decode_any W_a08ac = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08b0 : bv 32 := 0x02051513.
Lemma F_a08b0 : fetch_word AsanUbsan.M.loaded_segments (0xa08f8 : word) = Some W_a08b0.
Proof. vm_refl. Qed.
Lemma D_a08b0 : decode_any W_a08b0 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08b4 : bv 32 := 0x02055513.
Lemma F_a08b4 : fetch_word AsanUbsan.M.loaded_segments (0xa08fc : word) = Some W_a08b4.
Proof. vm_refl. Qed.
Lemma D_a08b4 : decode_any W_a08b4 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08b8 : bv 32 := 0x00a90533.
Lemma F_a08b8 : fetch_word AsanUbsan.M.loaded_segments (0xa0900 : word) = Some W_a08b8.
Proof. vm_refl. Qed.
Lemma D_a08b8 : decode_any W_a08b8 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08bc : bv 32 := 0x00043603.
Lemma F_a08bc : fetch_word AsanUbsan.M.loaded_segments (0xa0904 : word) = Some W_a08bc.
Proof. vm_refl. Qed.
Lemma D_a08bc : decode_any W_a08bc = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08c0 : bv 32 := 0x00b54533.
Lemma F_a08c0 : fetch_word AsanUbsan.M.loaded_segments (0xa0908 : word) = Some W_a08c0.
Proof. vm_refl. Qed.
Lemma D_a08c0 : decode_any W_a08c0 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08c4 : bv 32 := 0x00012583.
Lemma F_a08c4 : fetch_word AsanUbsan.M.loaded_segments (0xa090c : word) = Some W_a08c4.
Proof. vm_refl. Qed.
Lemma D_a08c4 : decode_any W_a08c4 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08c8 : bv 32 := 0x00153513.
Lemma F_a08c8 : fetch_word AsanUbsan.M.loaded_segments (0xa0910 : word) = Some W_a08c8.
Proof. vm_refl. Qed.
Lemma D_a08c8 : decode_any W_a08c8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08cc : bv 32 := 0x00a60533.
Lemma F_a08cc : fetch_word AsanUbsan.M.loaded_segments (0xa0914 : word) = Some W_a08cc.
Proof. vm_refl. Qed.
Lemma D_a08cc : decode_any W_a08cc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08d0 : bv 32 := 0x00a43023.
Lemma F_a08d0 : fetch_word AsanUbsan.M.loaded_segments (0xa0918 : word) = Some W_a08d0.
Proof. vm_refl. Qed.
Lemma D_a08d0 : decode_any W_a08d0 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08d4 : bv 32 := 0x0015851b.
Lemma F_a08d4 : fetch_word AsanUbsan.M.loaded_segments (0xa091c : word) = Some W_a08d4.
Proof. vm_refl. Qed.
Lemma D_a08d4 : decode_any W_a08d4 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08d8 : bv 32 := 0x03813083.
Lemma F_a08d8 : fetch_word AsanUbsan.M.loaded_segments (0xa0920 : word) = Some W_a08d8.
Proof. vm_refl. Qed.
Lemma D_a08d8 : decode_any W_a08d8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08dc : bv 32 := 0x03013403.
Lemma F_a08dc : fetch_word AsanUbsan.M.loaded_segments (0xa0924 : word) = Some W_a08dc.
Proof. vm_refl. Qed.
Lemma D_a08dc : decode_any W_a08dc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08e0 : bv 32 := 0x02813483.
Lemma F_a08e0 : fetch_word AsanUbsan.M.loaded_segments (0xa0928 : word) = Some W_a08e0.
Proof. vm_refl. Qed.
Lemma D_a08e0 : decode_any W_a08e0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08e4 : bv 32 := 0x02013903.
Lemma F_a08e4 : fetch_word AsanUbsan.M.loaded_segments (0xa092c : word) = Some W_a08e4.
Proof. vm_refl. Qed.
Lemma D_a08e4 : decode_any W_a08e4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08e8 : bv 32 := 0x01813983.
Lemma F_a08e8 : fetch_word AsanUbsan.M.loaded_segments (0xa0930 : word) = Some W_a08e8.
Proof. vm_refl. Qed.
Lemma D_a08e8 : decode_any W_a08e8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08ec : bv 32 := 0x01013a03.
Lemma F_a08ec : fetch_word AsanUbsan.M.loaded_segments (0xa0934 : word) = Some W_a08ec.
Proof. vm_refl. Qed.
Lemma D_a08ec : decode_any W_a08ec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08f0 : bv 32 := 0x00813a83.
Lemma F_a08f0 : fetch_word AsanUbsan.M.loaded_segments (0xa0938 : word) = Some W_a08f0.
Proof. vm_refl. Qed.
Lemma D_a08f0 : decode_any W_a08f0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08f4 : bv 32 := 0x04010113.
Lemma F_a08f4 : fetch_word AsanUbsan.M.loaded_segments (0xa093c : word) = Some W_a08f4.
Proof. vm_refl. Qed.
Lemma D_a08f4 : decode_any W_a08f4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a08f8 : bv 32 := 0x00008067.
Lemma F_a08f8 : fetch_word AsanUbsan.M.loaded_segments (0xa0940 : word) = Some W_a08f8.
Proof. vm_refl. Qed.
Lemma D_a08f8 : decode_any W_a08f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0920 : bv 32 := 0xff010113.
Lemma F_a0920 : fetch_word AsanUbsan.M.loaded_segments (0xa0968 : word) = Some W_a0920.
Proof. vm_refl. Qed.
Lemma D_a0920 : decode_any W_a0920 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0924 : bv 32 := 0x00113423.
Lemma F_a0924 : fetch_word AsanUbsan.M.loaded_segments (0xa096c : word) = Some W_a0924.
Proof. vm_refl. Qed.
Lemma D_a0924 : decode_any W_a0924 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0928 : bv 32 := 0x00813023.
Lemma F_a0928 : fetch_word AsanUbsan.M.loaded_segments (0xa0970 : word) = Some W_a0928.
Proof. vm_refl. Qed.
Lemma D_a0928 : decode_any W_a0928 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a092c : bv 32 := 0x00058793.
Lemma F_a092c : fetch_word AsanUbsan.M.loaded_segments (0xa0974 : word) = Some W_a092c.
Proof. vm_refl. Qed.
Lemma D_a092c : decode_any W_a092c = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0930 : bv 32 := 0x00050593.
Lemma F_a0930 : fetch_word AsanUbsan.M.loaded_segments (0xa0978 : word) = Some W_a0930.
Proof. vm_refl. Qed.
Lemma D_a0930 : decode_any W_a0930 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0934 : bv 32 := 0x00f5342f.
Lemma F_a0934 : fetch_word AsanUbsan.M.loaded_segments (0xa097c : word) = Some W_a0934.
Proof. vm_refl. Qed.
Lemma D_a0934 : decode_any W_a0934 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0938 : bv 32 := 0xfff78513.
Lemma F_a0938 : fetch_word AsanUbsan.M.loaded_segments (0xa0980 : word) = Some W_a0938.
Proof. vm_refl. Qed.
Lemma D_a0938 : decode_any W_a0938 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a093c : bv 32 := 0x01445293.
Lemma F_a093c : fetch_word AsanUbsan.M.loaded_segments (0xa0984 : word) = Some W_a093c.
Proof. vm_refl. Qed.
Lemma D_a093c : decode_any W_a093c = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0940 : bv 32 := 0x00850733.
Lemma F_a0940 : fetch_word AsanUbsan.M.loaded_segments (0xa0988 : word) = Some W_a0940.
Proof. vm_refl. Qed.
Lemma D_a0940 : decode_any W_a0940 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0944 : bv 32 := 0x01475313.
Lemma F_a0944 : fetch_word AsanUbsan.M.loaded_segments (0xa098c : word) = Some W_a0944.
Proof. vm_refl. Qed.
Lemma D_a0944 : decode_any W_a0944 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0948 : bv 32 := 0x04629863.
Lemma F_a0948 : fetch_word AsanUbsan.M.loaded_segments (0xa0990 : word) = Some W_a0948.
Proof. vm_refl. Qed.
Lemma D_a0948 : decode_any W_a0948 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a094c : bv 32 := 0x02045513.
Lemma F_a094c : fetch_word AsanUbsan.M.loaded_segments (0xa0994 : word) = Some W_a094c.
Proof. vm_refl. Qed.
Lemma D_a094c : decode_any W_a094c = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0950 : bv 32 := 0x00050c63.
Lemma F_a0950 : fetch_word AsanUbsan.M.loaded_segments (0xa0998 : word) = Some W_a0950.
Proof. vm_refl. Qed.
Lemma D_a0950 : decode_any W_a0950 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0968 : bv 32 := 0x00863023.
Lemma F_a0968 : fetch_word AsanUbsan.M.loaded_segments (0xa09b0 : word) = Some W_a0968.
Proof. vm_refl. Qed.
Lemma D_a0968 : decode_any W_a0968 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a096c : bv 32 := 0x00429613.
Lemma F_a096c : fetch_word AsanUbsan.M.loaded_segments (0xa09b4 : word) = Some W_a096c.
Proof. vm_refl. Qed.
Lemma D_a096c : decode_any W_a096c = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0970 : bv 32 := 0x00c58633.
Lemma F_a0970 : fetch_word AsanUbsan.M.loaded_segments (0xa09b8 : word) = Some W_a0970.
Proof. vm_refl. Qed.
Lemma D_a0970 : decode_any W_a0970 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0974 : bv 32 := 0x01063503.
Lemma F_a0974 : fetch_word AsanUbsan.M.loaded_segments (0xa09bc : word) = Some W_a0974.
Proof. vm_refl. Qed.
Lemma D_a0974 : decode_any W_a0974 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0978 : bv 32 := 0x0a050a63.
Lemma F_a0978 : fetch_word AsanUbsan.M.loaded_segments (0xa09c0 : word) = Some W_a0978.
Proof. vm_refl. Qed.
Lemma D_a0978 : decode_any W_a0978 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a097c : bv 32 := 0x02c41413.
Lemma F_a097c : fetch_word AsanUbsan.M.loaded_segments (0xa09c4 : word) = Some W_a097c.
Proof. vm_refl. Qed.
Lemma D_a097c : decode_any W_a097c = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0980 : bv 32 := 0x02945413.
Lemma F_a0980 : fetch_word AsanUbsan.M.loaded_segments (0xa09c8 : word) = Some W_a0980.
Proof. vm_refl. Qed.
Lemma D_a0980 : decode_any W_a0980 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0984 : bv 32 := 0x00850533.
Lemma F_a0984 : fetch_word AsanUbsan.M.loaded_segments (0xa09cc : word) = Some W_a0984.
Proof. vm_refl. Qed.
Lemma D_a0984 : decode_any W_a0984 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0988 : bv 32 := 0x00813083.
Lemma F_a0988 : fetch_word AsanUbsan.M.loaded_segments (0xa09d0 : word) = Some W_a0988.
Proof. vm_refl. Qed.
Lemma D_a0988 : decode_any W_a0988 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a098c : bv 32 := 0x00013403.
Lemma F_a098c : fetch_word AsanUbsan.M.loaded_segments (0xa09d4 : word) = Some W_a098c.
Proof. vm_refl. Qed.
Lemma D_a098c : decode_any W_a098c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0990 : bv 32 := 0x01010113.
Lemma F_a0990 : fetch_word AsanUbsan.M.loaded_segments (0xa09d8 : word) = Some W_a0990.
Proof. vm_refl. Qed.
Lemma D_a0990 : decode_any W_a0990 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0994 : bv 32 := 0x00008067.
Lemma F_a0994 : fetch_word AsanUbsan.M.loaded_segments (0xa09dc : word) = Some W_a0994.
Proof. vm_refl. Qed.
Lemma D_a0994 : decode_any W_a0994 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

