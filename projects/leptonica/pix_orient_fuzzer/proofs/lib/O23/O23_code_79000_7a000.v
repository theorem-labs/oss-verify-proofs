(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_79754 : bv 32 := 0xf2010113.
Lemma F_79754 : fetch_word Plain.M.loaded_segments (0x797ac : word) = Some W_79754.
Proof. vm_refl. Qed.
Lemma D_79754 : decode_any W_79754 = Some (OpImm ALU_ADD 2 2 3872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79758 : bv 32 := 0x0c113c23.
Lemma F_79758 : fetch_word Plain.M.loaded_segments (0x797b0 : word) = Some W_79758.
Proof. vm_refl. Qed.
Lemma D_79758 : decode_any W_79758 = Some (Store SZ8 2 1 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7975c : bv 32 := 0x0c813823.
Lemma F_7975c : fetch_word Plain.M.loaded_segments (0x797b4 : word) = Some W_7975c.
Proof. vm_refl. Qed.
Lemma D_7975c : decode_any W_7975c = Some (Store SZ8 2 8 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79760 : bv 32 := 0x0c913423.
Lemma F_79760 : fetch_word Plain.M.loaded_segments (0x797b8 : word) = Some W_79760.
Proof. vm_refl. Qed.
Lemma D_79760 : decode_any W_79760 = Some (Store SZ8 2 9 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79764 : bv 32 := 0x0d213023.
Lemma F_79764 : fetch_word Plain.M.loaded_segments (0x797bc : word) = Some W_79764.
Proof. vm_refl. Qed.
Lemma D_79764 : decode_any W_79764 = Some (Store SZ8 2 18 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79768 : bv 32 := 0x0b313c23.
Lemma F_79768 : fetch_word Plain.M.loaded_segments (0x797c0 : word) = Some W_79768.
Proof. vm_refl. Qed.
Lemma D_79768 : decode_any W_79768 = Some (Store SZ8 2 19 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7976c : bv 32 := 0x0b413823.
Lemma F_7976c : fetch_word Plain.M.loaded_segments (0x797c4 : word) = Some W_7976c.
Proof. vm_refl. Qed.
Lemma D_7976c : decode_any W_7976c = Some (Store SZ8 2 20 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79770 : bv 32 := 0x0b513423.
Lemma F_79770 : fetch_word Plain.M.loaded_segments (0x797c8 : word) = Some W_79770.
Proof. vm_refl. Qed.
Lemma D_79770 : decode_any W_79770 = Some (Store SZ8 2 21 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79774 : bv 32 := 0x0b613023.
Lemma F_79774 : fetch_word Plain.M.loaded_segments (0x797cc : word) = Some W_79774.
Proof. vm_refl. Qed.
Lemma D_79774 : decode_any W_79774 = Some (Store SZ8 2 22 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79778 : bv 32 := 0x09713c23.
Lemma F_79778 : fetch_word Plain.M.loaded_segments (0x797d0 : word) = Some W_79778.
Proof. vm_refl. Qed.
Lemma D_79778 : decode_any W_79778 = Some (Store SZ8 2 23 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7977c : bv 32 := 0x09813823.
Lemma F_7977c : fetch_word Plain.M.loaded_segments (0x797d4 : word) = Some W_7977c.
Proof. vm_refl. Qed.
Lemma D_7977c : decode_any W_7977c = Some (Store SZ8 2 24 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79780 : bv 32 := 0x09913423.
Lemma F_79780 : fetch_word Plain.M.loaded_segments (0x797d8 : word) = Some W_79780.
Proof. vm_refl. Qed.
Lemma D_79780 : decode_any W_79780 = Some (Store SZ8 2 25 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79784 : bv 32 := 0x09a13023.
Lemma F_79784 : fetch_word Plain.M.loaded_segments (0x797dc : word) = Some W_79784.
Proof. vm_refl. Qed.
Lemma D_79784 : decode_any W_79784 = Some (Store SZ8 2 26 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79788 : bv 32 := 0x07b13c23.
Lemma F_79788 : fetch_word Plain.M.loaded_segments (0x797e0 : word) = Some W_79788.
Proof. vm_refl. Qed.
Lemma D_79788 : decode_any W_79788 = Some (Store SZ8 2 27 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7978c : bv 32 := 0x0a050863.
Lemma F_7978c : fetch_word Plain.M.loaded_segments (0x797e4 : word) = Some W_7978c.
Proof. vm_refl. Qed.
Lemma D_7978c : decode_any W_7978c = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79790 : bv 32 := 0x00078993.
Lemma F_79790 : fetch_word Plain.M.loaded_segments (0x797e8 : word) = Some W_79790.
Proof. vm_refl. Qed.
Lemma D_79790 : decode_any W_79790 = Some (OpImm ALU_ADD 19 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79794 : bv 32 := 0x00a00793.
Lemma F_79794 : fetch_word Plain.M.loaded_segments (0x797ec : word) = Some W_79794.
Proof. vm_refl. Qed.
Lemma D_79794 : decode_any W_79794 = Some (OpImm ALU_ADD 15 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79798 : bv 32 := 0x08f98e63.
Lemma F_79798 : fetch_word Plain.M.loaded_segments (0x797f0 : word) = Some W_79798.
Proof. vm_refl. Qed.
Lemma D_79798 : decode_any W_79798 = Some (Branch BC_EQ 19 15 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7979c : bv 32 := 0x00080c93.
Lemma F_7979c : fetch_word Plain.M.loaded_segments (0x797f4 : word) = Some W_7979c.
Proof. vm_refl. Qed.
Lemma D_7979c : decode_any W_7979c = Some (OpImm ALU_ADD 25 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797a0 : bv 32 := 0x00088b13.
Lemma F_797a0 : fetch_word Plain.M.loaded_segments (0x797f8 : word) = Some W_797a0.
Proof. vm_refl. Qed.
Lemma D_797a0 : decode_any W_797a0 = Some (OpImm ALU_ADD 22 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797a4 : bv 32 := 0x00070d93.
Lemma F_797a4 : fetch_word Plain.M.loaded_segments (0x797fc : word) = Some W_797a4.
Proof. vm_refl. Qed.
Lemma D_797a4 : decode_any W_797a4 = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797a8 : bv 32 := 0x00058913.
Lemma F_797a8 : fetch_word Plain.M.loaded_segments (0x79800 : word) = Some W_797a8.
Proof. vm_refl. Qed.
Lemma D_797a8 : decode_any W_797a8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797ac : bv 32 := 0x00060493.
Lemma F_797ac : fetch_word Plain.M.loaded_segments (0x79804 : word) = Some W_797ac.
Proof. vm_refl. Qed.
Lemma D_797ac : decode_any W_797ac = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797b0 : bv 32 := 0x00068413.
Lemma F_797b0 : fetch_word Plain.M.loaded_segments (0x79808 : word) = Some W_797b0.
Proof. vm_refl. Qed.
Lemma D_797b0 : decode_any W_797b0 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797b4 : bv 32 := 0x0e013a83.
Lemma F_797b4 : fetch_word Plain.M.loaded_segments (0x7980c : word) = Some W_797b4.
Proof. vm_refl. Qed.
Lemma D_797b4 : decode_any W_797b4 = Some (Load SZ8 true 21 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797b8 : bv 32 := 0x07410593.
Lemma F_797b8 : fetch_word Plain.M.loaded_segments (0x79810 : word) = Some W_797b8.
Proof. vm_refl. Qed.
Lemma D_797b8 : decode_any W_797b8 = Some (OpImm ALU_ADD 11 2 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797bc : bv 32 := 0x07010613.
Lemma F_797bc : fetch_word Plain.M.loaded_segments (0x79814 : word) = Some W_797bc.
Proof. vm_refl. Qed.
Lemma D_797bc : decode_any W_797bc = Some (OpImm ALU_ADD 12 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797c0 : bv 32 := 0x06c10693.
Lemma F_797c0 : fetch_word Plain.M.loaded_segments (0x79818 : word) = Some W_797c0.
Proof. vm_refl. Qed.
Lemma D_797c0 : decode_any W_797c0 = Some (OpImm ALU_ADD 13 2 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797c4 : bv 32 := 0x00050a13.
Lemma F_797c4 : fetch_word Plain.M.loaded_segments (0x7981c : word) = Some W_797c4.
Proof. vm_refl. Qed.
Lemma D_797c4 : decode_any W_797c4 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797c8 : bv 32 := 0xdd8f30ef.
Lemma F_797c8 : fetch_word Plain.M.loaded_segments (0x79820 : word) = Some W_797c8.
Proof. vm_refl. Qed.
Lemma D_797c8 : decode_any W_797c8 = Some (Jal 1 2045400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797cc : bv 32 := 0x00f00513.
Lemma F_797cc : fetch_word Plain.M.loaded_segments (0x79824 : word) = Some W_797cc.
Proof. vm_refl. Qed.
Lemma D_797cc : decode_any W_797cc = Some (OpImm ALU_ADD 10 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797d0 : bv 32 := 0x0d356863.
Lemma F_797d0 : fetch_word Plain.M.loaded_segments (0x79828 : word) = Some W_797d0.
Proof. vm_refl. Qed.
Lemma D_797d0 : decode_any W_797d0 = Some (Branch BC_LTU 10 19 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797d4 : bv 32 := 0x00008537.
Lemma F_797d4 : fetch_word Plain.M.loaded_segments (0x7982c : word) = Some W_797d4.
Proof. vm_refl. Qed.
Lemma D_797d4 : decode_any W_797d4 = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797d8 : bv 32 := 0x0215051b.
Lemma F_797d8 : fetch_word Plain.M.loaded_segments (0x79830 : word) = Some W_797d8.
Proof. vm_refl. Qed.
Lemma D_797d8 : decode_any W_797d8 = Some (OpImm32 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797dc : bv 32 := 0x01355533.
Lemma F_797dc : fetch_word Plain.M.loaded_segments (0x79834 : word) = Some W_797dc.
Proof. vm_refl. Qed.
Lemma D_797dc : decode_any W_797dc = Some (Op ALU_SRL 10 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797e0 : bv 32 := 0x00157513.
Lemma F_797e0 : fetch_word Plain.M.loaded_segments (0x79838 : word) = Some W_797e0.
Proof. vm_refl. Qed.
Lemma D_797e0 : decode_any W_797e0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797e4 : bv 32 := 0x0a050e63.
Lemma F_797e4 : fetch_word Plain.M.loaded_segments (0x7983c : word) = Some W_797e4.
Proof. vm_refl. Qed.
Lemma D_797e4 : decode_any W_797e4 = Some (Branch BC_EQ 10 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797e8 : bv 32 := 0x000a0513.
Lemma F_797e8 : fetch_word Plain.M.loaded_segments (0x79840 : word) = Some W_797e8.
Proof. vm_refl. Qed.
Lemma D_797e8 : decode_any W_797e8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797ec : bv 32 := 0x9fcf40ef.
Lemma F_797ec : fetch_word Plain.M.loaded_segments (0x79844 : word) = Some W_797ec.
Proof. vm_refl. Qed.
Lemma D_797ec : decode_any W_797ec = Some (Jal 1 2048508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797f0 : bv 32 := 0x07412a83.
Lemma F_797f0 : fetch_word Plain.M.loaded_segments (0x79848 : word) = Some W_797f0.
Proof. vm_refl. Qed.
Lemma D_797f0 : decode_any W_797f0 = Some (Load SZ4 true 21 2 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797f4 : bv 32 := 0x07012b03.
Lemma F_797f4 : fetch_word Plain.M.loaded_segments (0x7984c : word) = Some W_797f4.
Proof. vm_refl. Qed.
Lemma D_797f4 : decode_any W_797f4 = Some (Load SZ4 true 22 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797f8 : bv 32 := 0x06c12b83.
Lemma F_797f8 : fetch_word Plain.M.loaded_segments (0x79850 : word) = Some W_797f8.
Proof. vm_refl. Qed.
Lemma D_797f8 : decode_any W_797f8 = Some (Load SZ4 true 23 2 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797fc : bv 32 := 0x00050c13.
Lemma F_797fc : fetch_word Plain.M.loaded_segments (0x79854 : word) = Some W_797fc.
Proof. vm_refl. Qed.
Lemma D_797fc : decode_any W_797fc = Some (OpImm ALU_ADD 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79800 : bv 32 := 0x000a0513.
Lemma F_79800 : fetch_word Plain.M.loaded_segments (0x79858 : word) = Some W_79800.
Proof. vm_refl. Qed.
Lemma D_79800 : decode_any W_79800 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79804 : bv 32 := 0xaa0f30ef.
Lemma F_79804 : fetch_word Plain.M.loaded_segments (0x7985c : word) = Some W_79804.
Proof. vm_refl. Qed.
Lemma D_79804 : decode_any W_79804 = Some (Jal 1 2044576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79808 : bv 32 := 0x00050713.
Lemma F_79808 : fetch_word Plain.M.loaded_segments (0x79860 : word) = Some W_79808.
Proof. vm_refl. Qed.
Lemma D_79808 : decode_any W_79808 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7980c : bv 32 := 0x01b13023.
Lemma F_7980c : fetch_word Plain.M.loaded_segments (0x79864 : word) = Some W_7980c.
Proof. vm_refl. Qed.
Lemma D_7980c : decode_any W_7980c = Some (Store SZ8 2 27 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79810 : bv 32 := 0x01313423.
Lemma F_79810 : fetch_word Plain.M.loaded_segments (0x79868 : word) = Some W_79810.
Proof. vm_refl. Qed.
Lemma D_79810 : decode_any W_79810 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79814 : bv 32 := 0x000c0513.
Lemma F_79814 : fetch_word Plain.M.loaded_segments (0x7986c : word) = Some W_79814.
Proof. vm_refl. Qed.
Lemma D_79814 : decode_any W_79814 = Some (OpImm ALU_ADD 10 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79818 : bv 32 := 0x000a8593.
Lemma F_79818 : fetch_word Plain.M.loaded_segments (0x79870 : word) = Some W_79818.
Proof. vm_refl. Qed.
Lemma D_79818 : decode_any W_79818 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7981c : bv 32 := 0x000b0613.
Lemma F_7981c : fetch_word Plain.M.loaded_segments (0x79874 : word) = Some W_7981c.
Proof. vm_refl. Qed.
Lemma D_7981c : decode_any W_7981c = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79820 : bv 32 := 0x000b8693.
Lemma F_79820 : fetch_word Plain.M.loaded_segments (0x79878 : word) = Some W_79820.
Proof. vm_refl. Qed.
Lemma D_79820 : decode_any W_79820 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79824 : bv 32 := 0x00090793.
Lemma F_79824 : fetch_word Plain.M.loaded_segments (0x7987c : word) = Some W_79824.
Proof. vm_refl. Qed.
Lemma D_79824 : decode_any W_79824 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79828 : bv 32 := 0x00048813.
Lemma F_79828 : fetch_word Plain.M.loaded_segments (0x79880 : word) = Some W_79828.
Proof. vm_refl. Qed.
Lemma D_79828 : decode_any W_79828 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7982c : bv 32 := 0x00040893.
Lemma F_7982c : fetch_word Plain.M.loaded_segments (0x79884 : word) = Some W_7982c.
Proof. vm_refl. Qed.
Lemma D_7982c : decode_any W_7982c = Some (OpImm ALU_ADD 17 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79830 : bv 32 := 0x1c0000ef.
Lemma F_79830 : fetch_word Plain.M.loaded_segments (0x79888 : word) = Some W_79830.
Proof. vm_refl. Qed.
Lemma D_79830 : decode_any W_79830 = Some (Jal 1 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79834 : bv 32 := 0x00000513.
Lemma F_79834 : fetch_word Plain.M.loaded_segments (0x7988c : word) = Some W_79834.
Proof. vm_refl. Qed.
Lemma D_79834 : decode_any W_79834 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79838 : bv 32 := 0x17c0006f.
Lemma F_79838 : fetch_word Plain.M.loaded_segments (0x79890 : word) = Some W_79838.
Proof. vm_refl. Qed.
Lemma D_79838 : decode_any W_79838 = Some (Jal 0 380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7983c : bv 32 := 0x00099517.
Lemma F_7983c : fetch_word Plain.M.loaded_segments (0x79894 : word) = Some W_7983c.
Proof. vm_refl. Qed.
Lemma D_7983c : decode_any W_7983c = Some (Auipc 10 153, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79840 : bv 32 := 0xd3453503.
Lemma F_79840 : fetch_word Plain.M.loaded_segments (0x79898 : word) = Some W_79840.
Proof. vm_refl. Qed.
Lemma D_79840 : decode_any W_79840 = Some (Load SZ8 true 10 10 3380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79844 : bv 32 := 0x00052503.
Lemma F_79844 : fetch_word Plain.M.loaded_segments (0x7989c : word) = Some W_79844.
Proof. vm_refl. Qed.
Lemma D_79844 : decode_any W_79844 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79848 : bv 32 := 0x00500593.
Lemma F_79848 : fetch_word Plain.M.loaded_segments (0x798a0 : word) = Some W_79848.
Proof. vm_refl. Qed.
Lemma D_79848 : decode_any W_79848 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7984c : bv 32 := 0x16a5c263.
Lemma F_7984c : fetch_word Plain.M.loaded_segments (0x798a4 : word) = Some W_7984c.
Proof. vm_refl. Qed.
Lemma D_7984c : decode_any W_7984c = Some (Branch BC_LT 11 10 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79850 : bv 32 := 0xfffa0517.
Lemma F_79850 : fetch_word Plain.M.loaded_segments (0x798a8 : word) = Some W_79850.
Proof. vm_refl. Qed.
Lemma D_79850 : decode_any W_79850 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79854 : bv 32 := 0xfff9f597.
Lemma F_79854 : fetch_word Plain.M.loaded_segments (0x798ac : word) = Some W_79854.
Proof. vm_refl. Qed.
Lemma D_79854 : decode_any W_79854 = Some (Auipc 11 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79858 : bv 32 := 0x1ed50513.
Lemma F_79858 : fetch_word Plain.M.loaded_segments (0x798b0 : word) = Some W_79858.
Proof. vm_refl. Qed.
Lemma D_79858 : decode_any W_79858 = Some (OpImm ALU_ADD 10 10 493, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7985c : bv 32 := 0x36258593.
Lemma F_7985c : fetch_word Plain.M.loaded_segments (0x798b4 : word) = Some W_7985c.
Proof. vm_refl. Qed.
Lemma D_7985c : decode_any W_7985c = Some (OpImm ALU_ADD 11 11 866, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79860 : bv 32 := 0x00100613.
Lemma F_79860 : fetch_word Plain.M.loaded_segments (0x798b8 : word) = Some W_79860.
Proof. vm_refl. Qed.
Lemma D_79860 : decode_any W_79860 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79864 : bv 32 := 0x0d813083.
Lemma F_79864 : fetch_word Plain.M.loaded_segments (0x798bc : word) = Some W_79864.
Proof. vm_refl. Qed.
Lemma D_79864 : decode_any W_79864 = Some (Load SZ8 true 1 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79868 : bv 32 := 0x0d013403.
Lemma F_79868 : fetch_word Plain.M.loaded_segments (0x798c0 : word) = Some W_79868.
Proof. vm_refl. Qed.
Lemma D_79868 : decode_any W_79868 = Some (Load SZ8 true 8 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7986c : bv 32 := 0x0c813483.
Lemma F_7986c : fetch_word Plain.M.loaded_segments (0x798c4 : word) = Some W_7986c.
Proof. vm_refl. Qed.
Lemma D_7986c : decode_any W_7986c = Some (Load SZ8 true 9 2 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79870 : bv 32 := 0x0c013903.
Lemma F_79870 : fetch_word Plain.M.loaded_segments (0x798c8 : word) = Some W_79870.
Proof. vm_refl. Qed.
Lemma D_79870 : decode_any W_79870 = Some (Load SZ8 true 18 2 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79874 : bv 32 := 0x0b813983.
Lemma F_79874 : fetch_word Plain.M.loaded_segments (0x798cc : word) = Some W_79874.
Proof. vm_refl. Qed.
Lemma D_79874 : decode_any W_79874 = Some (Load SZ8 true 19 2 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79878 : bv 32 := 0x0b013a03.
Lemma F_79878 : fetch_word Plain.M.loaded_segments (0x798d0 : word) = Some W_79878.
Proof. vm_refl. Qed.
Lemma D_79878 : decode_any W_79878 = Some (Load SZ8 true 20 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7987c : bv 32 := 0x0a813a83.
Lemma F_7987c : fetch_word Plain.M.loaded_segments (0x798d4 : word) = Some W_7987c.
Proof. vm_refl. Qed.
Lemma D_7987c : decode_any W_7987c = Some (Load SZ8 true 21 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79880 : bv 32 := 0x0a013b03.
Lemma F_79880 : fetch_word Plain.M.loaded_segments (0x798d8 : word) = Some W_79880.
Proof. vm_refl. Qed.
Lemma D_79880 : decode_any W_79880 = Some (Load SZ8 true 22 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79884 : bv 32 := 0x09813b83.
Lemma F_79884 : fetch_word Plain.M.loaded_segments (0x798dc : word) = Some W_79884.
Proof. vm_refl. Qed.
Lemma D_79884 : decode_any W_79884 = Some (Load SZ8 true 23 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79888 : bv 32 := 0x09013c03.
Lemma F_79888 : fetch_word Plain.M.loaded_segments (0x798e0 : word) = Some W_79888.
Proof. vm_refl. Qed.
Lemma D_79888 : decode_any W_79888 = Some (Load SZ8 true 24 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7988c : bv 32 := 0x08813c83.
Lemma F_7988c : fetch_word Plain.M.loaded_segments (0x798e4 : word) = Some W_7988c.
Proof. vm_refl. Qed.
Lemma D_7988c : decode_any W_7988c = Some (Load SZ8 true 25 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79890 : bv 32 := 0x08013d03.
Lemma F_79890 : fetch_word Plain.M.loaded_segments (0x798e8 : word) = Some W_79890.
Proof. vm_refl. Qed.
Lemma D_79890 : decode_any W_79890 = Some (Load SZ8 true 26 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79894 : bv 32 := 0x07813d83.
Lemma F_79894 : fetch_word Plain.M.loaded_segments (0x798ec : word) = Some W_79894.
Proof. vm_refl. Qed.
Lemma D_79894 : decode_any W_79894 = Some (Load SZ8 true 27 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79898 : bv 32 := 0x0e010113.
Lemma F_79898 : fetch_word Plain.M.loaded_segments (0x798f0 : word) = Some W_79898.
Proof. vm_refl. Qed.
Lemma D_79898 : decode_any W_79898 = Some (OpImm ALU_ADD 2 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7989c : bv 32 := 0xf58e906f.
Lemma F_7989c : fetch_word Plain.M.loaded_segments (0x798f4 : word) = Some W_7989c.
Proof. vm_refl. Qed.
Lemma D_7989c : decode_any W_7989c = Some (Jal 0 2004824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798a0 : bv 32 := 0x0a0c8c63.
Lemma F_798a0 : fetch_word Plain.M.loaded_segments (0x798f8 : word) = Some W_798a0.
Proof. vm_refl. Qed.
Lemma D_798a0 : decode_any W_798a0 = Some (Branch BC_EQ 25 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798a4 : bv 32 := 0x000c8513.
Lemma F_798a4 : fetch_word Plain.M.loaded_segments (0x798fc : word) = Some W_798a4.
Proof. vm_refl. Qed.
Lemma D_798a4 : decode_any W_798a4 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798a8 : bv 32 := 0x06810593.
Lemma F_798a8 : fetch_word Plain.M.loaded_segments (0x79900 : word) = Some W_798a8.
Proof. vm_refl. Qed.
Lemma D_798a8 : decode_any W_798a8 = Some (OpImm ALU_ADD 11 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798ac : bv 32 := 0x06410613.
Lemma F_798ac : fetch_word Plain.M.loaded_segments (0x79904 : word) = Some W_798ac.
Proof. vm_refl. Qed.
Lemma D_798ac : decode_any W_798ac = Some (OpImm ALU_ADD 12 2 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798b0 : bv 32 := 0x06010693.
Lemma F_798b0 : fetch_word Plain.M.loaded_segments (0x79908 : word) = Some W_798b0.
Proof. vm_refl. Qed.
Lemma D_798b0 : decode_any W_798b0 = Some (OpImm ALU_ADD 13 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798b4 : bv 32 := 0xcecf30ef.
Lemma F_798b4 : fetch_word Plain.M.loaded_segments (0x7990c : word) = Some W_798b4.
Proof. vm_refl. Qed.
Lemma D_798b4 : decode_any W_798b4 = Some (Jal 1 2045164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798b8 : bv 32 := 0x06c12503.
Lemma F_798b8 : fetch_word Plain.M.loaded_segments (0x79910 : word) = Some W_798b8.
Proof. vm_refl. Qed.
Lemma D_798b8 : decode_any W_798b8 = Some (Load SZ4 true 10 2 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798bc : bv 32 := 0x06012583.
Lemma F_798bc : fetch_word Plain.M.loaded_segments (0x79914 : word) = Some W_798bc.
Proof. vm_refl. Qed.
Lemma D_798bc : decode_any W_798bc = Some (Load SZ4 true 11 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798c0 : bv 32 := 0x0cb51063.
Lemma F_798c0 : fetch_word Plain.M.loaded_segments (0x79918 : word) = Some W_798c0.
Proof. vm_refl. Qed.
Lemma D_798c0 : decode_any W_798c0 = Some (Branch BC_NE 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798c4 : bv 32 := 0x000a0513.
Lemma F_798c4 : fetch_word Plain.M.loaded_segments (0x7991c : word) = Some W_798c4.
Proof. vm_refl. Qed.
Lemma D_798c4 : decode_any W_798c4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798c8 : bv 32 := 0x920f40ef.
Lemma F_798c8 : fetch_word Plain.M.loaded_segments (0x79920 : word) = Some W_798c8.
Proof. vm_refl. Qed.
Lemma D_798c8 : decode_any W_798c8 = Some (Jal 1 2048288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798cc : bv 32 := 0x07412583.
Lemma F_798cc : fetch_word Plain.M.loaded_segments (0x79924 : word) = Some W_798cc.
Proof. vm_refl. Qed.
Lemma D_798cc : decode_any W_798cc = Some (Load SZ4 true 11 2 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798d0 : bv 32 := 0x04b13c23.
Lemma F_798d0 : fetch_word Plain.M.loaded_segments (0x79928 : word) = Some W_798d0.
Proof. vm_refl. Qed.
Lemma D_798d0 : decode_any W_798d0 = Some (Store SZ8 2 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798d4 : bv 32 := 0x07012583.
Lemma F_798d4 : fetch_word Plain.M.loaded_segments (0x7992c : word) = Some W_798d4.
Proof. vm_refl. Qed.
Lemma D_798d4 : decode_any W_798d4 = Some (Load SZ4 true 11 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798d8 : bv 32 := 0x04b13823.
Lemma F_798d8 : fetch_word Plain.M.loaded_segments (0x79930 : word) = Some W_798d8.
Proof. vm_refl. Qed.
Lemma D_798d8 : decode_any W_798d8 = Some (Store SZ8 2 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798dc : bv 32 := 0x06c12583.
Lemma F_798dc : fetch_word Plain.M.loaded_segments (0x79934 : word) = Some W_798dc.
Proof. vm_refl. Qed.
Lemma D_798dc : decode_any W_798dc = Some (Load SZ4 true 11 2 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798e0 : bv 32 := 0x04b13423.
Lemma F_798e0 : fetch_word Plain.M.loaded_segments (0x79938 : word) = Some W_798e0.
Proof. vm_refl. Qed.
Lemma D_798e0 : decode_any W_798e0 = Some (Store SZ8 2 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798e4 : bv 32 := 0x04a13023.
Lemma F_798e4 : fetch_word Plain.M.loaded_segments (0x7993c : word) = Some W_798e4.
Proof. vm_refl. Qed.
Lemma D_798e4 : decode_any W_798e4 = Some (Store SZ8 2 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798e8 : bv 32 := 0x000a0513.
Lemma F_798e8 : fetch_word Plain.M.loaded_segments (0x79940 : word) = Some W_798e8.
Proof. vm_refl. Qed.
Lemma D_798e8 : decode_any W_798e8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798ec : bv 32 := 0x9b8f30ef.
Lemma F_798ec : fetch_word Plain.M.loaded_segments (0x79944 : word) = Some W_798ec.
Proof. vm_refl. Qed.
Lemma D_798ec : decode_any W_798ec = Some (Jal 1 2044344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798f0 : bv 32 := 0x00050a13.
Lemma F_798f0 : fetch_word Plain.M.loaded_segments (0x79948 : word) = Some W_798f0.
Proof. vm_refl. Qed.
Lemma D_798f0 : decode_any W_798f0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798f4 : bv 32 := 0x000c8513.
Lemma F_798f4 : fetch_word Plain.M.loaded_segments (0x7994c : word) = Some W_798f4.
Proof. vm_refl. Qed.
Lemma D_798f4 : decode_any W_798f4 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798f8 : bv 32 := 0x8f0f40ef.
Lemma F_798f8 : fetch_word Plain.M.loaded_segments (0x79950 : word) = Some W_798f8.
Proof. vm_refl. Qed.
Lemma D_798f8 : decode_any W_798f8 = Some (Jal 1 2048240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798fc : bv 32 := 0x06812b83.
Lemma F_798fc : fetch_word Plain.M.loaded_segments (0x79954 : word) = Some W_798fc.
Proof. vm_refl. Qed.
Lemma D_798fc : decode_any W_798fc = Some (Load SZ4 true 23 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79900 : bv 32 := 0x06412c03.
Lemma F_79900 : fetch_word Plain.M.loaded_segments (0x79958 : word) = Some W_79900.
Proof. vm_refl. Qed.
Lemma D_79900 : decode_any W_79900 = Some (Load SZ4 true 24 2 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79904 : bv 32 := 0x00050d13.
Lemma F_79904 : fetch_word Plain.M.loaded_segments (0x7995c : word) = Some W_79904.
Proof. vm_refl. Qed.
Lemma D_79904 : decode_any W_79904 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79908 : bv 32 := 0x000c8513.
Lemma F_79908 : fetch_word Plain.M.loaded_segments (0x79960 : word) = Some W_79908.
Proof. vm_refl. Qed.
Lemma D_79908 : decode_any W_79908 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7990c : bv 32 := 0x998f30ef.
Lemma F_7990c : fetch_word Plain.M.loaded_segments (0x79964 : word) = Some W_7990c.
Proof. vm_refl. Qed.
Lemma D_7990c : decode_any W_7990c = Some (Jal 1 2044312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79910 : bv 32 := 0x03813023.
Lemma F_79910 : fetch_word Plain.M.loaded_segments (0x79968 : word) = Some W_79910.
Proof. vm_refl. Qed.
Lemma D_79910 : decode_any W_79910 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79914 : bv 32 := 0x02a13423.
Lemma F_79914 : fetch_word Plain.M.loaded_segments (0x7996c : word) = Some W_79914.
Proof. vm_refl. Qed.
Lemma D_79914 : decode_any W_79914 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79918 : bv 32 := 0x03613823.
Lemma F_79918 : fetch_word Plain.M.loaded_segments (0x79970 : word) = Some W_79918.
Proof. vm_refl. Qed.
Lemma D_79918 : decode_any W_79918 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7991c : bv 32 := 0x03513c23.
Lemma F_7991c : fetch_word Plain.M.loaded_segments (0x79974 : word) = Some W_7991c.
Proof. vm_refl. Qed.
Lemma D_7991c : decode_any W_7991c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79920 : bv 32 := 0x01b13023.
Lemma F_79920 : fetch_word Plain.M.loaded_segments (0x79978 : word) = Some W_79920.
Proof. vm_refl. Qed.
Lemma D_79920 : decode_any W_79920 = Some (Store SZ8 2 27 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79924 : bv 32 := 0x01313423.
Lemma F_79924 : fetch_word Plain.M.loaded_segments (0x7997c : word) = Some W_79924.
Proof. vm_refl. Qed.
Lemma D_79924 : decode_any W_79924 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79928 : bv 32 := 0x01a13823.
Lemma F_79928 : fetch_word Plain.M.loaded_segments (0x79980 : word) = Some W_79928.
Proof. vm_refl. Qed.
Lemma D_79928 : decode_any W_79928 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7992c : bv 32 := 0x01713c23.
Lemma F_7992c : fetch_word Plain.M.loaded_segments (0x79984 : word) = Some W_7992c.
Proof. vm_refl. Qed.
Lemma D_7992c : decode_any W_7992c = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79930 : bv 32 := 0x04013503.
Lemma F_79930 : fetch_word Plain.M.loaded_segments (0x79988 : word) = Some W_79930.
Proof. vm_refl. Qed.
Lemma D_79930 : decode_any W_79930 = Some (Load SZ8 true 10 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79934 : bv 32 := 0x05813583.
Lemma F_79934 : fetch_word Plain.M.loaded_segments (0x7998c : word) = Some W_79934.
Proof. vm_refl. Qed.
Lemma D_79934 : decode_any W_79934 = Some (Load SZ8 true 11 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79938 : bv 32 := 0x05013603.
Lemma F_79938 : fetch_word Plain.M.loaded_segments (0x79990 : word) = Some W_79938.
Proof. vm_refl. Qed.
Lemma D_79938 : decode_any W_79938 = Some (Load SZ8 true 12 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7993c : bv 32 := 0x04813683.
Lemma F_7993c : fetch_word Plain.M.loaded_segments (0x79994 : word) = Some W_7993c.
Proof. vm_refl. Qed.
Lemma D_7993c : decode_any W_7993c = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79940 : bv 32 := 0x000a0713.
Lemma F_79940 : fetch_word Plain.M.loaded_segments (0x79998 : word) = Some W_79940.
Proof. vm_refl. Qed.
Lemma D_79940 : decode_any W_79940 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79944 : bv 32 := 0x00090793.
Lemma F_79944 : fetch_word Plain.M.loaded_segments (0x7999c : word) = Some W_79944.
Proof. vm_refl. Qed.
Lemma D_79944 : decode_any W_79944 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79948 : bv 32 := 0x00048813.
Lemma F_79948 : fetch_word Plain.M.loaded_segments (0x799a0 : word) = Some W_79948.
Proof. vm_refl. Qed.
Lemma D_79948 : decode_any W_79948 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7994c : bv 32 := 0x00040893.
Lemma F_7994c : fetch_word Plain.M.loaded_segments (0x799a4 : word) = Some W_7994c.
Proof. vm_refl. Qed.
Lemma D_7994c : decode_any W_7994c = Some (OpImm ALU_ADD 17 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79950 : bv 32 := 0x608000ef.
Lemma F_79950 : fetch_word Plain.M.loaded_segments (0x799a8 : word) = Some W_79950.
Proof. vm_refl. Qed.
Lemma D_79950 : decode_any W_79950 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79954 : bv 32 := 0xee1ff06f.
Lemma F_79954 : fetch_word Plain.M.loaded_segments (0x799ac : word) = Some W_79954.
Proof. vm_refl. Qed.
Lemma D_79954 : decode_any W_79954 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799b4 : bv 32 := 0x0d813083.
Lemma F_799b4 : fetch_word Plain.M.loaded_segments (0x79a0c : word) = Some W_799b4.
Proof. vm_refl. Qed.
Lemma D_799b4 : decode_any W_799b4 = Some (Load SZ8 true 1 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799b8 : bv 32 := 0x0d013403.
Lemma F_799b8 : fetch_word Plain.M.loaded_segments (0x79a10 : word) = Some W_799b8.
Proof. vm_refl. Qed.
Lemma D_799b8 : decode_any W_799b8 = Some (Load SZ8 true 8 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799bc : bv 32 := 0x0c813483.
Lemma F_799bc : fetch_word Plain.M.loaded_segments (0x79a14 : word) = Some W_799bc.
Proof. vm_refl. Qed.
Lemma D_799bc : decode_any W_799bc = Some (Load SZ8 true 9 2 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799c0 : bv 32 := 0x0c013903.
Lemma F_799c0 : fetch_word Plain.M.loaded_segments (0x79a18 : word) = Some W_799c0.
Proof. vm_refl. Qed.
Lemma D_799c0 : decode_any W_799c0 = Some (Load SZ8 true 18 2 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799c4 : bv 32 := 0x0b813983.
Lemma F_799c4 : fetch_word Plain.M.loaded_segments (0x79a1c : word) = Some W_799c4.
Proof. vm_refl. Qed.
Lemma D_799c4 : decode_any W_799c4 = Some (Load SZ8 true 19 2 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799c8 : bv 32 := 0x0b013a03.
Lemma F_799c8 : fetch_word Plain.M.loaded_segments (0x79a20 : word) = Some W_799c8.
Proof. vm_refl. Qed.
Lemma D_799c8 : decode_any W_799c8 = Some (Load SZ8 true 20 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799cc : bv 32 := 0x0a813a83.
Lemma F_799cc : fetch_word Plain.M.loaded_segments (0x79a24 : word) = Some W_799cc.
Proof. vm_refl. Qed.
Lemma D_799cc : decode_any W_799cc = Some (Load SZ8 true 21 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799d0 : bv 32 := 0x0a013b03.
Lemma F_799d0 : fetch_word Plain.M.loaded_segments (0x79a28 : word) = Some W_799d0.
Proof. vm_refl. Qed.
Lemma D_799d0 : decode_any W_799d0 = Some (Load SZ8 true 22 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799d4 : bv 32 := 0x09813b83.
Lemma F_799d4 : fetch_word Plain.M.loaded_segments (0x79a2c : word) = Some W_799d4.
Proof. vm_refl. Qed.
Lemma D_799d4 : decode_any W_799d4 = Some (Load SZ8 true 23 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799d8 : bv 32 := 0x09013c03.
Lemma F_799d8 : fetch_word Plain.M.loaded_segments (0x79a30 : word) = Some W_799d8.
Proof. vm_refl. Qed.
Lemma D_799d8 : decode_any W_799d8 = Some (Load SZ8 true 24 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799dc : bv 32 := 0x08813c83.
Lemma F_799dc : fetch_word Plain.M.loaded_segments (0x79a34 : word) = Some W_799dc.
Proof. vm_refl. Qed.
Lemma D_799dc : decode_any W_799dc = Some (Load SZ8 true 25 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799e0 : bv 32 := 0x08013d03.
Lemma F_799e0 : fetch_word Plain.M.loaded_segments (0x79a38 : word) = Some W_799e0.
Proof. vm_refl. Qed.
Lemma D_799e0 : decode_any W_799e0 = Some (Load SZ8 true 26 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799e4 : bv 32 := 0x07813d83.
Lemma F_799e4 : fetch_word Plain.M.loaded_segments (0x79a3c : word) = Some W_799e4.
Proof. vm_refl. Qed.
Lemma D_799e4 : decode_any W_799e4 = Some (Load SZ8 true 27 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799e8 : bv 32 := 0x0e010113.
Lemma F_799e8 : fetch_word Plain.M.loaded_segments (0x79a40 : word) = Some W_799e8.
Proof. vm_refl. Qed.
Lemma D_799e8 : decode_any W_799e8 = Some (OpImm ALU_ADD 2 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799ec : bv 32 := 0x00008067.
Lemma F_799ec : fetch_word Plain.M.loaded_segments (0x79a44 : word) = Some W_799ec.
Proof. vm_refl. Qed.
Lemma D_799ec : decode_any W_799ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f0 : bv 32 := 0xf9010113.
Lemma F_799f0 : fetch_word Plain.M.loaded_segments (0x79a48 : word) = Some W_799f0.
Proof. vm_refl. Qed.
Lemma D_799f0 : decode_any W_799f0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f4 : bv 32 := 0x06113423.
Lemma F_799f4 : fetch_word Plain.M.loaded_segments (0x79a4c : word) = Some W_799f4.
Proof. vm_refl. Qed.
Lemma D_799f4 : decode_any W_799f4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f8 : bv 32 := 0x06813023.
Lemma F_799f8 : fetch_word Plain.M.loaded_segments (0x79a50 : word) = Some W_799f8.
Proof. vm_refl. Qed.
Lemma D_799f8 : decode_any W_799f8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799fc : bv 32 := 0x04913c23.
Lemma F_799fc : fetch_word Plain.M.loaded_segments (0x79a54 : word) = Some W_799fc.
Proof. vm_refl. Qed.
Lemma D_799fc : decode_any W_799fc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a00 : bv 32 := 0x05213823.
Lemma F_79a00 : fetch_word Plain.M.loaded_segments (0x79a58 : word) = Some W_79a00.
Proof. vm_refl. Qed.
Lemma D_79a00 : decode_any W_79a00 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a04 : bv 32 := 0x05313423.
Lemma F_79a04 : fetch_word Plain.M.loaded_segments (0x79a5c : word) = Some W_79a04.
Proof. vm_refl. Qed.
Lemma D_79a04 : decode_any W_79a04 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a08 : bv 32 := 0x05413023.
Lemma F_79a08 : fetch_word Plain.M.loaded_segments (0x79a60 : word) = Some W_79a08.
Proof. vm_refl. Qed.
Lemma D_79a08 : decode_any W_79a08 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a0c : bv 32 := 0x03513c23.
Lemma F_79a0c : fetch_word Plain.M.loaded_segments (0x79a64 : word) = Some W_79a0c.
Proof. vm_refl. Qed.
Lemma D_79a0c : decode_any W_79a0c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a10 : bv 32 := 0x03613823.
Lemma F_79a10 : fetch_word Plain.M.loaded_segments (0x79a68 : word) = Some W_79a10.
Proof. vm_refl. Qed.
Lemma D_79a10 : decode_any W_79a10 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a14 : bv 32 := 0x03713423.
Lemma F_79a14 : fetch_word Plain.M.loaded_segments (0x79a6c : word) = Some W_79a14.
Proof. vm_refl. Qed.
Lemma D_79a14 : decode_any W_79a14 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a18 : bv 32 := 0x03813023.
Lemma F_79a18 : fetch_word Plain.M.loaded_segments (0x79a70 : word) = Some W_79a18.
Proof. vm_refl. Qed.
Lemma D_79a18 : decode_any W_79a18 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a1c : bv 32 := 0x01913c23.
Lemma F_79a1c : fetch_word Plain.M.loaded_segments (0x79a74 : word) = Some W_79a1c.
Proof. vm_refl. Qed.
Lemma D_79a1c : decode_any W_79a1c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a20 : bv 32 := 0x01a13823.
Lemma F_79a20 : fetch_word Plain.M.loaded_segments (0x79a78 : word) = Some W_79a20.
Proof. vm_refl. Qed.
Lemma D_79a20 : decode_any W_79a20 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a24 : bv 32 := 0x01b13423.
Lemma F_79a24 : fetch_word Plain.M.loaded_segments (0x79a7c : word) = Some W_79a24.
Proof. vm_refl. Qed.
Lemma D_79a24 : decode_any W_79a24 = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a28 : bv 32 := 0x00070413.
Lemma F_79a28 : fetch_word Plain.M.loaded_segments (0x79a80 : word) = Some W_79a28.
Proof. vm_refl. Qed.
Lemma D_79a28 : decode_any W_79a28 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a2c : bv 32 := 0x02b685b3.
Lemma F_79a2c : fetch_word Plain.M.loaded_segments (0x79a84 : word) = Some W_79a2c.
Proof. vm_refl. Qed.
Lemma D_79a2c : decode_any W_79a2c = Some (Mul M_MUL 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a30 : bv 32 := 0x02d7873b.
Lemma F_79a30 : fetch_word Plain.M.loaded_segments (0x79a88 : word) = Some W_79a30.
Proof. vm_refl. Qed.
Lemma D_79a30 : decode_any W_79a30 = Some (Mul32 M_MUL 14 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a34 : bv 32 := 0x02d886b3.
Lemma F_79a34 : fetch_word Plain.M.loaded_segments (0x79a8c : word) = Some W_79a34.
Proof. vm_refl. Qed.
Lemma D_79a34 : decode_any W_79a34 = Some (Mul M_MUL 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a38 : bv 32 := 0x43f75793.
Lemma F_79a38 : fetch_word Plain.M.loaded_segments (0x79a90 : word) = Some W_79a38.
Proof. vm_refl. Qed.
Lemma D_79a38 : decode_any W_79a38 = Some (ShiftImm ALU_SRA 15 14 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a3c : bv 32 := 0x00e7f7b3.
Lemma F_79a3c : fetch_word Plain.M.loaded_segments (0x79a94 : word) = Some W_79a3c.
Proof. vm_refl. Qed.
Lemma D_79a3c : decode_any W_79a3c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a40 : bv 32 := 0x00f687b3.
Lemma F_79a40 : fetch_word Plain.M.loaded_segments (0x79a98 : word) = Some W_79a40.
Proof. vm_refl. Qed.
Lemma D_79a40 : decode_any W_79a40 = Some (Op ALU_ADD 15 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a44 : bv 32 := 0x00e026b3.
Lemma F_79a44 : fetch_word Plain.M.loaded_segments (0x79a9c : word) = Some W_79a44.
Proof. vm_refl. Qed.
Lemma D_79a44 : decode_any W_79a44 = Some (Op ALU_SLT 13 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a48 : bv 32 := 0x40d006b3.
Lemma F_79a48 : fetch_word Plain.M.loaded_segments (0x79aa0 : word) = Some W_79a48.
Proof. vm_refl. Qed.
Lemma D_79a48 : decode_any W_79a48 = Some (Op ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a4c : bv 32 := 0x00e6f6b3.
Lemma F_79a4c : fetch_word Plain.M.loaded_segments (0x79aa4 : word) = Some W_79a4c.
Proof. vm_refl. Qed.
Lemma D_79a4c : decode_any W_79a4c = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a50 : bv 32 := 0x40b685bb.
Lemma F_79a50 : fetch_word Plain.M.loaded_segments (0x79aa8 : word) = Some W_79a50.
Proof. vm_refl. Qed.
Lemma D_79a50 : decode_any W_79a50 = Some (Op32 ALU_SUB 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a54 : bv 32 := 0x00f585bb.
Lemma F_79a54 : fetch_word Plain.M.loaded_segments (0x79aac : word) = Some W_79a54.
Proof. vm_refl. Qed.
Lemma D_79a54 : decode_any W_79a54 = Some (Op32 ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a58 : bv 32 := 0x00b02733.
Lemma F_79a58 : fetch_word Plain.M.loaded_segments (0x79ab0 : word) = Some W_79a58.
Proof. vm_refl. Qed.
Lemma D_79a58 : decode_any W_79a58 = Some (Op ALU_SLT 14 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a5c : bv 32 := 0x40e0073b.
Lemma F_79a5c : fetch_word Plain.M.loaded_segments (0x79ab4 : word) = Some W_79a5c.
Proof. vm_refl. Qed.
Lemma D_79a5c : decode_any W_79a5c = Some (Op32 ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a60 : bv 32 := 0x00b775b3.
Lemma F_79a60 : fetch_word Plain.M.loaded_segments (0x79ab8 : word) = Some W_79a60.
Proof. vm_refl. Qed.
Lemma D_79a60 : decode_any W_79a60 = Some (Op ALU_AND 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a64 : bv 32 := 0x40b7893b.
Lemma F_79a64 : fetch_word Plain.M.loaded_segments (0x79abc : word) = Some W_79a64.
Proof. vm_refl. Qed.
Lemma D_79a64 : decode_any W_79a64 = Some (Op32 ALU_SUB 18 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a68 : bv 32 := 0x21205663.
Lemma F_79a68 : fetch_word Plain.M.loaded_segments (0x79ac0 : word) = Some W_79a68.
Proof. vm_refl. Qed.
Lemma D_79a68 : decode_any W_79a68 = Some (Branch BC_GE 0 18 524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a6c : bv 32 := 0x07013583.
Lemma F_79a6c : fetch_word Plain.M.loaded_segments (0x79ac4 : word) = Some W_79a6c.
Proof. vm_refl. Qed.
Lemma D_79a6c : decode_any W_79a6c = Some (Load SZ8 true 11 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a70 : bv 32 := 0x43f85713.
Lemma F_79a70 : fetch_word Plain.M.loaded_segments (0x79ac8 : word) = Some W_79a70.
Proof. vm_refl. Qed.
Lemma D_79a70 : decode_any W_79a70 = Some (ShiftImm ALU_SRA 14 16 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a74 : bv 32 := 0x010027b3.
Lemma F_79a74 : fetch_word Plain.M.loaded_segments (0x79acc : word) = Some W_79a74.
Proof. vm_refl. Qed.
Lemma D_79a74 : decode_any W_79a74 = Some (Op ALU_SLT 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a78 : bv 32 := 0x010778b3.
Lemma F_79a78 : fetch_word Plain.M.loaded_segments (0x79ad0 : word) = Some W_79a78.
Proof. vm_refl. Qed.
Lemma D_79a78 : decode_any W_79a78 = Some (Op ALU_AND 17 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a7c : bv 32 := 0x40f00733.
Lemma F_79a7c : fetch_word Plain.M.loaded_segments (0x79ad4 : word) = Some W_79a7c.
Proof. vm_refl. Qed.
Lemma D_79a7c : decode_any W_79a7c = Some (Op ALU_SUB 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a80 : bv 32 := 0x01077733.
Lemma F_79a80 : fetch_word Plain.M.loaded_segments (0x79ad8 : word) = Some W_79a80.
Proof. vm_refl. Qed.
Lemma D_79a80 : decode_any W_79a80 = Some (Op ALU_AND 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a84 : bv 32 := 0x011585b3.
Lemma F_79a84 : fetch_word Plain.M.loaded_segments (0x79adc : word) = Some W_79a84.
Proof. vm_refl. Qed.
Lemma D_79a84 : decode_any W_79a84 = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a88 : bv 32 := 0x40c7063b.
Lemma F_79a88 : fetch_word Plain.M.loaded_segments (0x79ae0 : word) = Some W_79a88.
Proof. vm_refl. Qed.
Lemma D_79a88 : decode_any W_79a88 = Some (Op32 ALU_SUB 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a8c : bv 32 := 0x00b6063b.
Lemma F_79a8c : fetch_word Plain.M.loaded_segments (0x79ae4 : word) = Some W_79a8c.
Proof. vm_refl. Qed.
Lemma D_79a8c : decode_any W_79a8c = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a90 : bv 32 := 0x00c027b3.
Lemma F_79a90 : fetch_word Plain.M.loaded_segments (0x79ae8 : word) = Some W_79a90.
Proof. vm_refl. Qed.
Lemma D_79a90 : decode_any W_79a90 = Some (Op ALU_SLT 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a94 : bv 32 := 0x40f007bb.
Lemma F_79a94 : fetch_word Plain.M.loaded_segments (0x79aec : word) = Some W_79a94.
Proof. vm_refl. Qed.
Lemma D_79a94 : decode_any W_79a94 = Some (Op32 ALU_SUB 15 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a98 : bv 32 := 0x00c7f633.
Lemma F_79a98 : fetch_word Plain.M.loaded_segments (0x79af0 : word) = Some W_79a98.
Proof. vm_refl. Qed.
Lemma D_79a98 : decode_any W_79a98 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a9c : bv 32 := 0x40c589bb.
Lemma F_79a9c : fetch_word Plain.M.loaded_segments (0x79af4 : word) = Some W_79a9c.
Proof. vm_refl. Qed.
Lemma D_79a9c : decode_any W_79a9c = Some (Op32 ALU_SUB 19 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa0 : bv 32 := 0x1d305a63.
Lemma F_79aa0 : fetch_word Plain.M.loaded_segments (0x79af8 : word) = Some W_79aa0.
Proof. vm_refl. Qed.
Lemma D_79aa0 : decode_any W_79aa0 = Some (Branch BC_GE 0 19 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa4 : bv 32 := 0x07813583.
Lemma F_79aa4 : fetch_word Plain.M.loaded_segments (0x79afc : word) = Some W_79aa4.
Proof. vm_refl. Qed.
Lemma D_79aa4 : decode_any W_79aa4 = Some (Load SZ8 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa8 : bv 32 := 0x01f6f813.
Lemma F_79aa8 : fetch_word Plain.M.loaded_segments (0x79b00 : word) = Some W_79aa8.
Proof. vm_refl. Qed.
Lemma D_79aa8 : decode_any W_79aa8 = Some (OpImm ALU_AND 16 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aac : bv 32 := 0x028707bb.
Lemma F_79aac : fetch_word Plain.M.loaded_segments (0x79b04 : word) = Some W_79aac.
Proof. vm_refl. Qed.
Lemma D_79aac : decode_any W_79aac = Some (Mul32 M_MUL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ab0 : bv 32 := 0x0056d71b.
Lemma F_79ab0 : fetch_word Plain.M.loaded_segments (0x79b08 : word) = Some W_79ab0.
Proof. vm_refl. Qed.
Lemma D_79ab0 : decode_any W_79ab0 = Some (ShiftImm32 ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ab4 : bv 32 := 0x0c080463.
Lemma F_79ab4 : fetch_word Plain.M.loaded_segments (0x79b0c : word) = Some W_79ab4.
Proof. vm_refl. Qed.
Lemma D_79ab4 : decode_any W_79ab4 = Some (Branch BC_EQ 16 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ab8 : bv 32 := 0x02000613.
Lemma F_79ab8 : fetch_word Plain.M.loaded_segments (0x79b10 : word) = Some W_79ab8.
Proof. vm_refl. Qed.
Lemma D_79ab8 : decode_any W_79ab8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79abc : bv 32 := 0xfffa6297.
Lemma F_79abc : fetch_word Plain.M.loaded_segments (0x79b14 : word) = Some W_79abc.
Proof. vm_refl. Qed.
Lemma D_79abc : decode_any W_79abc = Some (Auipc 5 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ac0 : bv 32 := 0x410608b3.
Lemma F_79ac0 : fetch_word Plain.M.loaded_segments (0x79b18 : word) = Some W_79ac0.
Proof. vm_refl. Qed.
Lemma D_79ac0 : decode_any W_79ac0 = Some (Op ALU_SUB 17 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ac4 : bv 32 := 0x88c28613.
Lemma F_79ac4 : fetch_word Plain.M.loaded_segments (0x79b1c : word) = Some W_79ac4.
Proof. vm_refl. Qed.
Lemma D_79ac4 : decode_any W_79ac4 = Some (OpImm ALU_ADD 12 5 2188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ac8 : bv 32 := 0x00289293.
Lemma F_79ac8 : fetch_word Plain.M.loaded_segments (0x79b20 : word) = Some W_79ac8.
Proof. vm_refl. Qed.
Lemma D_79ac8 : decode_any W_79ac8 = Some (ShiftImm ALU_SLL 5 17 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79acc : bv 32 := 0x00560633.
Lemma F_79acc : fetch_word Plain.M.loaded_segments (0x79b24 : word) = Some W_79acc.
Proof. vm_refl. Qed.
Lemma D_79acc : decode_any W_79acc = Some (Op ALU_ADD 12 12 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ad0 : bv 32 := 0x00062603.
Lemma F_79ad0 : fetch_word Plain.M.loaded_segments (0x79b28 : word) = Some W_79ad0.
Proof. vm_refl. Qed.
Lemma D_79ad0 : decode_any W_79ad0 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ad4 : bv 32 := 0x00279793.
Lemma F_79ad4 : fetch_word Plain.M.loaded_segments (0x79b2c : word) = Some W_79ad4.
Proof. vm_refl. Qed.
Lemma D_79ad4 : decode_any W_79ad4 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ad8 : bv 32 := 0x00f50533.
Lemma F_79ad8 : fetch_word Plain.M.loaded_segments (0x79b30 : word) = Some W_79ad8.
Proof. vm_refl. Qed.
Lemma D_79ad8 : decode_any W_79ad8 = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79adc : bv 32 := 0x00271713.
Lemma F_79adc : fetch_word Plain.M.loaded_segments (0x79b34 : word) = Some W_79adc.
Proof. vm_refl. Qed.
Lemma D_79adc : decode_any W_79adc = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ae0 : bv 32 := 0x00e50533.
Lemma F_79ae0 : fetch_word Plain.M.loaded_segments (0x79b38 : word) = Some W_79ae0.
Proof. vm_refl. Qed.
Lemma D_79ae0 : decode_any W_79ae0 = Some (Op ALU_ADD 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ae4 : bv 32 := 0x0b197c63.
Lemma F_79ae4 : fetch_word Plain.M.loaded_segments (0x79b3c : word) = Some W_79ae4.
Proof. vm_refl. Qed.
Lemma D_79ae4 : decode_any W_79ae4 = Some (Branch BC_GEU 18 17 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ae8 : bv 32 := 0x00000493.
Lemma F_79ae8 : fetch_word Plain.M.loaded_segments (0x79b40 : word) = Some W_79ae8.
Proof. vm_refl. Qed.
Lemma D_79ae8 : decode_any W_79ae8 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aec : bv 32 := 0x00000b13.
Lemma F_79aec : fetch_word Plain.M.loaded_segments (0x79b44 : word) = Some W_79aec.
Proof. vm_refl. Qed.
Lemma D_79aec : decode_any W_79aec = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79af0 : bv 32 := 0x00000a13.
Lemma F_79af0 : fetch_word Plain.M.loaded_segments (0x79b48 : word) = Some W_79af0.
Proof. vm_refl. Qed.
Lemma D_79af0 : decode_any W_79af0 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79af4 : bv 32 := 0x010906bb.
Lemma F_79af4 : fetch_word Plain.M.loaded_segments (0x79b4c : word) = Some W_79af4.
Proof. vm_refl. Qed.
Lemma D_79af4 : decode_any W_79af4 = Some (Op32 ALU_ADD 13 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79af8 : bv 32 := 0xfffa6717.
Lemma F_79af8 : fetch_word Plain.M.loaded_segments (0x79b50 : word) = Some W_79af8.
Proof. vm_refl. Qed.
Lemma D_79af8 : decode_any W_79af8 = Some (Auipc 14 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79afc : bv 32 := 0x00269693.
Lemma F_79afc : fetch_word Plain.M.loaded_segments (0x79b54 : word) = Some W_79afc.
Proof. vm_refl. Qed.
Lemma D_79afc : decode_any W_79afc = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b00 : bv 32 := 0x8d470713.
Lemma F_79b00 : fetch_word Plain.M.loaded_segments (0x79b58 : word) = Some W_79b00.
Proof. vm_refl. Qed.
Lemma D_79b00 : decode_any W_79b00 = Some (OpImm ALU_ADD 14 14 2260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b04 : bv 32 := 0x00d706b3.
Lemma F_79b04 : fetch_word Plain.M.loaded_segments (0x79b5c : word) = Some W_79b04.
Proof. vm_refl. Qed.
Lemma D_79b04 : decode_any W_79b04 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b08 : bv 32 := 0x0006a683.
Lemma F_79b08 : fetch_word Plain.M.loaded_segments (0x79b60 : word) = Some W_79b08.
Proof. vm_refl. Qed.
Lemma D_79b08 : decode_any W_79b08 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b0c : bv 32 := 0x00100b93.
Lemma F_79b0c : fetch_word Plain.M.loaded_segments (0x79b64 : word) = Some W_79b0c.
Proof. vm_refl. Qed.
Lemma D_79b0c : decode_any W_79b0c = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b10 : bv 32 := 0x00c6f633.
Lemma F_79b10 : fetch_word Plain.M.loaded_segments (0x79b68 : word) = Some W_79b10.
Proof. vm_refl. Qed.
Lemma D_79b10 : decode_any W_79b10 = Some (Op ALU_AND 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b14 : bv 32 := 0x00100693.
Lemma F_79b14 : fetch_word Plain.M.loaded_segments (0x79b6c : word) = Some W_79b14.
Proof. vm_refl. Qed.
Lemma D_79b14 : decode_any W_79b14 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b18 : bv 32 := 0x00f00713.
Lemma F_79b18 : fetch_word Plain.M.loaded_segments (0x79b70 : word) = Some W_79b18.
Proof. vm_refl. Qed.
Lemma D_79b18 : decode_any W_79b18 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b1c : bv 32 := 0x0ce58663.
Lemma F_79b1c : fetch_word Plain.M.loaded_segments (0x79b74 : word) = Some W_79b1c.
Proof. vm_refl. Qed.
Lemma D_79b1c : decode_any W_79b1c = Some (Branch BC_EQ 11 14 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b20 : bv 32 := 0x00500713.
Lemma F_79b20 : fetch_word Plain.M.loaded_segments (0x79b78 : word) = Some W_79b20.
Proof. vm_refl. Qed.
Lemma D_79b20 : decode_any W_79b20 = Some (OpImm ALU_ADD 14 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b24 : bv 32 := 0x10e58663.
Lemma F_79b24 : fetch_word Plain.M.loaded_segments (0x79b7c : word) = Some W_79b24.
Proof. vm_refl. Qed.
Lemma D_79b24 : decode_any W_79b24 = Some (Branch BC_EQ 11 14 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b28 : bv 32 := 0x20059463.
Lemma F_79b28 : fetch_word Plain.M.loaded_segments (0x79b80 : word) = Some W_79b28.
Proof. vm_refl. Qed.
Lemma D_79b28 : decode_any W_79b28 = Some (Branch BC_NE 11 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b2c : bv 32 := 0xfff64593.
Lemma F_79b2c : fetch_word Plain.M.loaded_segments (0x79b84 : word) = Some W_79b2c.
Proof. vm_refl. Qed.
Lemma D_79b2c : decode_any W_79b2c = Some (OpImm ALU_XOR 11 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b30 : bv 32 := 0x00241613.
Lemma F_79b30 : fetch_word Plain.M.loaded_segments (0x79b88 : word) = Some W_79b30.
Proof. vm_refl. Qed.
Lemma D_79b30 : decode_any W_79b30 = Some (ShiftImm ALU_SLL 12 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b34 : bv 32 := 0x00098713.
Lemma F_79b34 : fetch_word Plain.M.loaded_segments (0x79b8c : word) = Some W_79b34.
Proof. vm_refl. Qed.
Lemma D_79b34 : decode_any W_79b34 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b38 : bv 32 := 0x00052783.
Lemma F_79b38 : fetch_word Plain.M.loaded_segments (0x79b90 : word) = Some W_79b38.
Proof. vm_refl. Qed.
Lemma D_79b38 : decode_any W_79b38 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b3c : bv 32 := 0xfff7071b.
Lemma F_79b3c : fetch_word Plain.M.loaded_segments (0x79b94 : word) = Some W_79b3c.
Proof. vm_refl. Qed.
Lemma D_79b3c : decode_any W_79b3c = Some (OpImm32 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b40 : bv 32 := 0x00b7f7b3.
Lemma F_79b40 : fetch_word Plain.M.loaded_segments (0x79b98 : word) = Some W_79b40.
Proof. vm_refl. Qed.
Lemma D_79b40 : decode_any W_79b40 = Some (Op ALU_AND 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b44 : bv 32 := 0x00f52023.
Lemma F_79b44 : fetch_word Plain.M.loaded_segments (0x79b9c : word) = Some W_79b44.
Proof. vm_refl. Qed.
Lemma D_79b44 : decode_any W_79b44 = Some (Store SZ4 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b48 : bv 32 := 0x00c50533.
Lemma F_79b48 : fetch_word Plain.M.loaded_segments (0x79ba0 : word) = Some W_79b48.
Proof. vm_refl. Qed.
Lemma D_79b48 : decode_any W_79b48 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b4c : bv 32 := 0xfe0716e3.
Lemma F_79b4c : fetch_word Plain.M.loaded_segments (0x79ba4 : word) = Some W_79b4c.
Proof. vm_refl. Qed.
Lemma D_79b4c : decode_any W_79b4c = Some (Branch BC_NE 14 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b50 : bv 32 := 0x3c068a63.
Lemma F_79b50 : fetch_word Plain.M.loaded_segments (0x79ba8 : word) = Some W_79b50.
Proof. vm_refl. Qed.
Lemma D_79b50 : decode_any W_79b50 = Some (Branch BC_EQ 13 0 980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b54 : bv 32 := 0x120b9063.
Lemma F_79b54 : fetch_word Plain.M.loaded_segments (0x79bac : word) = Some W_79b54.
Proof. vm_refl. Qed.
Lemma D_79b54 : decode_any W_79b54 = Some (Branch BC_NE 23 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b58 : bv 32 := 0xfffac513.
Lemma F_79b58 : fetch_word Plain.M.loaded_segments (0x79bb0 : word) = Some W_79b58.
Proof. vm_refl. Qed.
Lemma D_79b58 : decode_any W_79b58 = Some (OpImm ALU_XOR 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b5c : bv 32 := 0x00241413.
Lemma F_79b5c : fetch_word Plain.M.loaded_segments (0x79bb4 : word) = Some W_79b5c.
Proof. vm_refl. Qed.
Lemma D_79b5c : decode_any W_79b5c = Some (ShiftImm ALU_SLL 8 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b60 : bv 32 := 0x000a2583.
Lemma F_79b60 : fetch_word Plain.M.loaded_segments (0x79bb8 : word) = Some W_79b60.
Proof. vm_refl. Qed.
Lemma D_79b60 : decode_any W_79b60 = Some (Load SZ4 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b64 : bv 32 := 0xfff9899b.
Lemma F_79b64 : fetch_word Plain.M.loaded_segments (0x79bbc : word) = Some W_79b64.
Proof. vm_refl. Qed.
Lemma D_79b64 : decode_any W_79b64 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b68 : bv 32 := 0x00a5f5b3.
Lemma F_79b68 : fetch_word Plain.M.loaded_segments (0x79bc0 : word) = Some W_79b68.
Proof. vm_refl. Qed.
Lemma D_79b68 : decode_any W_79b68 = Some (Op ALU_AND 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b6c : bv 32 := 0x00ba2023.
Lemma F_79b6c : fetch_word Plain.M.loaded_segments (0x79bc4 : word) = Some W_79b6c.
Proof. vm_refl. Qed.
Lemma D_79b6c : decode_any W_79b6c = Some (Store SZ4 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b70 : bv 32 := 0x008a0a33.
Lemma F_79b70 : fetch_word Plain.M.loaded_segments (0x79bc8 : word) = Some W_79b70.
Proof. vm_refl. Qed.
Lemma D_79b70 : decode_any W_79b70 = Some (Op ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b74 : bv 32 := 0xfe0996e3.
Lemma F_79b74 : fetch_word Plain.M.loaded_segments (0x79bcc : word) = Some W_79b74.
Proof. vm_refl. Qed.
Lemma D_79b74 : decode_any W_79b74 = Some (Branch BC_NE 19 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b78 : bv 32 := 0x0fc0006f.
Lemma F_79b78 : fetch_word Plain.M.loaded_segments (0x79bd0 : word) = Some W_79b78.
Proof. vm_refl. Qed.
Lemma D_79b78 : decode_any W_79b78 = Some (Jal 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b7c : bv 32 := 0x01f97a13.
Lemma F_79b7c : fetch_word Plain.M.loaded_segments (0x79bd4 : word) = Some W_79b7c.
Proof. vm_refl. Qed.
Lemma D_79b7c : decode_any W_79b7c = Some (OpImm ALU_AND 20 18 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b80 : bv 32 := 0x120a0863.
Lemma F_79b80 : fetch_word Plain.M.loaded_segments (0x79bd8 : word) = Some W_79b80.
Proof. vm_refl. Qed.
Lemma D_79b80 : decode_any W_79b80 = Some (Branch BC_EQ 20 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b84 : bv 32 := 0x002a1613.
Lemma F_79b84 : fetch_word Plain.M.loaded_segments (0x79bdc : word) = Some W_79b84.
Proof. vm_refl. Qed.
Lemma D_79b84 : decode_any W_79b84 = Some (ShiftImm ALU_SLL 12 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b88 : bv 32 := 0xfffa6697.
Lemma F_79b88 : fetch_word Plain.M.loaded_segments (0x79be0 : word) = Some W_79b88.
Proof. vm_refl. Qed.
Lemma D_79b88 : decode_any W_79b88 = Some (Auipc 13 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b8c : bv 32 := 0x84468693.
Lemma F_79b8c : fetch_word Plain.M.loaded_segments (0x79be4 : word) = Some W_79b8c.
Proof. vm_refl. Qed.
Lemma D_79b8c : decode_any W_79b8c = Some (OpImm ALU_ADD 13 13 2116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b90 : bv 32 := 0x00c68633.
Lemma F_79b90 : fetch_word Plain.M.loaded_segments (0x79be8 : word) = Some W_79b90.
Proof. vm_refl. Qed.
Lemma D_79b90 : decode_any W_79b90 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b94 : bv 32 := 0x00062b03.
Lemma F_79b94 : fetch_word Plain.M.loaded_segments (0x79bec : word) = Some W_79b94.
Proof. vm_refl. Qed.
Lemma D_79b94 : decode_any W_79b94 = Some (Load SZ4 true 22 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b98 : bv 32 := 0x1180006f.
Lemma F_79b98 : fetch_word Plain.M.loaded_segments (0x79bf0 : word) = Some W_79b98.
Proof. vm_refl. Qed.
Lemma D_79b98 : decode_any W_79b98 = Some (Jal 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b9c : bv 32 := 0x4119073b.
Lemma F_79b9c : fetch_word Plain.M.loaded_segments (0x79bf4 : word) = Some W_79b9c.
Proof. vm_refl. Qed.
Lemma D_79b9c : decode_any W_79b9c = Some (Op32 ALU_SUB 14 18 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba0 : bv 32 := 0x00450a13.
Lemma F_79ba0 : fetch_word Plain.M.loaded_segments (0x79bf8 : word) = Some W_79ba0.
Proof. vm_refl. Qed.
Lemma D_79ba0 : decode_any W_79ba0 = Some (OpImm ALU_ADD 20 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba4 : bv 32 := 0x00d90933.
Lemma F_79ba4 : fetch_word Plain.M.loaded_segments (0x79bfc : word) = Some W_79ba4.
Proof. vm_refl. Qed.
Lemma D_79ba4 : decode_any W_79ba4 = Some (Op ALU_ADD 18 18 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba8 : bv 32 := 0x02073693.
Lemma F_79ba8 : fetch_word Plain.M.loaded_segments (0x79c00 : word) = Some W_79ba8.
Proof. vm_refl. Qed.
Lemma D_79ba8 : decode_any W_79ba8 = Some (OpImm ALU_SLTU 13 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bac : bv 32 := 0x00575b1b.
Lemma F_79bac : fetch_word Plain.M.loaded_segments (0x79c04 : word) = Some W_79bac.
Proof. vm_refl. Qed.
Lemma D_79bac : decode_any W_79bac = Some (ShiftImm32 ALU_SRL 22 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bb0 : bv 32 := 0xfff68793.
Lemma F_79bb0 : fetch_word Plain.M.loaded_segments (0x79c08 : word) = Some W_79bb0.
Proof. vm_refl. Qed.
Lemma D_79bb0 : decode_any W_79bb0 = Some (OpImm ALU_ADD 15 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bb4 : bv 32 := 0x01f97713.
Lemma F_79bb4 : fetch_word Plain.M.loaded_segments (0x79c0c : word) = Some W_79bb4.
Proof. vm_refl. Qed.
Lemma D_79bb4 : decode_any W_79bb4 = Some (OpImm ALU_AND 14 18 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bb8 : bv 32 := 0x0147f4b3.
Lemma F_79bb8 : fetch_word Plain.M.loaded_segments (0x79c10 : word) = Some W_79bb8.
Proof. vm_refl. Qed.
Lemma D_79bb8 : decode_any W_79bb8 = Some (Op ALU_AND 9 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bbc : bv 32 := 0x1a070c63.
Lemma F_79bbc : fetch_word Plain.M.loaded_segments (0x79c14 : word) = Some W_79bbc.
Proof. vm_refl. Qed.
Lemma D_79bbc : decode_any W_79bbc = Some (Branch BC_EQ 14 0 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bc0 : bv 32 := 0x00000b93.
Lemma F_79bc0 : fetch_word Plain.M.loaded_segments (0x79c18 : word) = Some W_79bc0.
Proof. vm_refl. Qed.
Lemma D_79bc0 : decode_any W_79bc0 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bc4 : bv 32 := 0x00271713.
Lemma F_79bc4 : fetch_word Plain.M.loaded_segments (0x79c1c : word) = Some W_79bc4.
Proof. vm_refl. Qed.
Lemma D_79bc4 : decode_any W_79bc4 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bc8 : bv 32 := 0xfffa6797.
Lemma F_79bc8 : fetch_word Plain.M.loaded_segments (0x79c20 : word) = Some W_79bc8.
Proof. vm_refl. Qed.
Lemma D_79bc8 : decode_any W_79bc8 = Some (Auipc 15 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bcc : bv 32 := 0x80478793.
Lemma F_79bcc : fetch_word Plain.M.loaded_segments (0x79c24 : word) = Some W_79bcc.
Proof. vm_refl. Qed.
Lemma D_79bcc : decode_any W_79bcc = Some (OpImm ALU_ADD 15 15 2052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bd0 : bv 32 := 0x00e78733.
Lemma F_79bd0 : fetch_word Plain.M.loaded_segments (0x79c28 : word) = Some W_79bd0.
Proof. vm_refl. Qed.
Lemma D_79bd0 : decode_any W_79bd0 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bd4 : bv 32 := 0x00072a83.
Lemma F_79bd4 : fetch_word Plain.M.loaded_segments (0x79c2c : word) = Some W_79bd4.
Proof. vm_refl. Qed.
Lemma D_79bd4 : decode_any W_79bd4 = Some (Load SZ4 true 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bd8 : bv 32 := 0x002b1713.
Lemma F_79bd8 : fetch_word Plain.M.loaded_segments (0x79c30 : word) = Some W_79bd8.
Proof. vm_refl. Qed.
Lemma D_79bd8 : decode_any W_79bd8 = Some (ShiftImm ALU_SLL 14 22 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bdc : bv 32 := 0x00ea0a33.
Lemma F_79bdc : fetch_word Plain.M.loaded_segments (0x79c34 : word) = Some W_79bdc.
Proof. vm_refl. Qed.
Lemma D_79bdc : decode_any W_79bdc = Some (Op ALU_ADD 20 20 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be0 : bv 32 := 0x00f00713.
Lemma F_79be0 : fetch_word Plain.M.loaded_segments (0x79c38 : word) = Some W_79be0.
Proof. vm_refl. Qed.
Lemma D_79be0 : decode_any W_79be0 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be4 : bv 32 := 0xf2e59ee3.
Lemma F_79be4 : fetch_word Plain.M.loaded_segments (0x79c3c : word) = Some W_79be4.
Proof. vm_refl. Qed.
Lemma D_79be4 : decode_any W_79be4 = Some (Branch BC_NE 11 14 7996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be8 : bv 32 := 0x00241593.
Lemma F_79be8 : fetch_word Plain.M.loaded_segments (0x79c40 : word) = Some W_79be8.
Proof. vm_refl. Qed.
Lemma D_79be8 : decode_any W_79be8 = Some (ShiftImm ALU_SLL 11 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bec : bv 32 := 0x00098713.
Lemma F_79bec : fetch_word Plain.M.loaded_segments (0x79c44 : word) = Some W_79bec.
Proof. vm_refl. Qed.
Lemma D_79bec : decode_any W_79bec = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf0 : bv 32 := 0x00052783.
Lemma F_79bf0 : fetch_word Plain.M.loaded_segments (0x79c48 : word) = Some W_79bf0.
Proof. vm_refl. Qed.
Lemma D_79bf0 : decode_any W_79bf0 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf4 : bv 32 := 0xfff7071b.
Lemma F_79bf4 : fetch_word Plain.M.loaded_segments (0x79c4c : word) = Some W_79bf4.
Proof. vm_refl. Qed.
Lemma D_79bf4 : decode_any W_79bf4 = Some (OpImm32 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf8 : bv 32 := 0x00c7e7b3.
Lemma F_79bf8 : fetch_word Plain.M.loaded_segments (0x79c50 : word) = Some W_79bf8.
Proof. vm_refl. Qed.
Lemma D_79bf8 : decode_any W_79bf8 = Some (Op ALU_OR 15 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bfc : bv 32 := 0x00f52023.
Lemma F_79bfc : fetch_word Plain.M.loaded_segments (0x79c54 : word) = Some W_79bfc.
Proof. vm_refl. Qed.
Lemma D_79bfc : decode_any W_79bfc = Some (Store SZ4 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c00 : bv 32 := 0x00b50533.
Lemma F_79c00 : fetch_word Plain.M.loaded_segments (0x79c58 : word) = Some W_79c00.
Proof. vm_refl. Qed.
Lemma D_79c00 : decode_any W_79c00 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c04 : bv 32 := 0xfe0716e3.
Lemma F_79c04 : fetch_word Plain.M.loaded_segments (0x79c5c : word) = Some W_79c04.
Proof. vm_refl. Qed.
Lemma D_79c04 : decode_any W_79c04 = Some (Branch BC_NE 14 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c08 : bv 32 := 0x00241913.
Lemma F_79c08 : fetch_word Plain.M.loaded_segments (0x79c60 : word) = Some W_79c08.
Proof. vm_refl. Qed.
Lemma D_79c08 : decode_any W_79c08 = Some (ShiftImm ALU_SLL 18 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c0c : bv 32 := 0x2e068463.
Lemma F_79c0c : fetch_word Plain.M.loaded_segments (0x79c64 : word) = Some W_79c0c.
Proof. vm_refl. Qed.
Lemma D_79c0c : decode_any W_79c0c = Some (Branch BC_EQ 13 0 744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c10 : bv 32 := 0x060b9263.
Lemma F_79c10 : fetch_word Plain.M.loaded_segments (0x79c68 : word) = Some W_79c10.
Proof. vm_refl. Qed.
Lemma D_79c10 : decode_any W_79c10 = Some (Branch BC_NE 23 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c14 : bv 32 := 0x000a2503.
Lemma F_79c14 : fetch_word Plain.M.loaded_segments (0x79c6c : word) = Some W_79c14.
Proof. vm_refl. Qed.
Lemma D_79c14 : decode_any W_79c14 = Some (Load SZ4 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c18 : bv 32 := 0xfff9899b.
Lemma F_79c18 : fetch_word Plain.M.loaded_segments (0x79c70 : word) = Some W_79c18.
Proof. vm_refl. Qed.
Lemma D_79c18 : decode_any W_79c18 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c1c : bv 32 := 0x01556533.
Lemma F_79c1c : fetch_word Plain.M.loaded_segments (0x79c74 : word) = Some W_79c1c.
Proof. vm_refl. Qed.
Lemma D_79c1c : decode_any W_79c1c = Some (Op ALU_OR 10 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c20 : bv 32 := 0x00aa2023.
Lemma F_79c20 : fetch_word Plain.M.loaded_segments (0x79c78 : word) = Some W_79c20.
Proof. vm_refl. Qed.
Lemma D_79c20 : decode_any W_79c20 = Some (Store SZ4 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c24 : bv 32 := 0x012a0a33.
Lemma F_79c24 : fetch_word Plain.M.loaded_segments (0x79c7c : word) = Some W_79c24.
Proof. vm_refl. Qed.
Lemma D_79c24 : decode_any W_79c24 = Some (Op ALU_ADD 20 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c28 : bv 32 := 0xfe0996e3.
Lemma F_79c28 : fetch_word Plain.M.loaded_segments (0x79c80 : word) = Some W_79c28.
Proof. vm_refl. Qed.
Lemma D_79c28 : decode_any W_79c28 = Some (Branch BC_NE 19 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c2c : bv 32 := 0x0480006f.
Lemma F_79c2c : fetch_word Plain.M.loaded_segments (0x79c84 : word) = Some W_79c2c.
Proof. vm_refl. Qed.
Lemma D_79c2c : decode_any W_79c2c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c74 : bv 32 := 0x06813083.
Lemma F_79c74 : fetch_word Plain.M.loaded_segments (0x79ccc : word) = Some W_79c74.
Proof. vm_refl. Qed.
Lemma D_79c74 : decode_any W_79c74 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c78 : bv 32 := 0x06013403.
Lemma F_79c78 : fetch_word Plain.M.loaded_segments (0x79cd0 : word) = Some W_79c78.
Proof. vm_refl. Qed.
Lemma D_79c78 : decode_any W_79c78 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c7c : bv 32 := 0x05813483.
Lemma F_79c7c : fetch_word Plain.M.loaded_segments (0x79cd4 : word) = Some W_79c7c.
Proof. vm_refl. Qed.
Lemma D_79c7c : decode_any W_79c7c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c80 : bv 32 := 0x05013903.
Lemma F_79c80 : fetch_word Plain.M.loaded_segments (0x79cd8 : word) = Some W_79c80.
Proof. vm_refl. Qed.
Lemma D_79c80 : decode_any W_79c80 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c84 : bv 32 := 0x04813983.
Lemma F_79c84 : fetch_word Plain.M.loaded_segments (0x79cdc : word) = Some W_79c84.
Proof. vm_refl. Qed.
Lemma D_79c84 : decode_any W_79c84 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c88 : bv 32 := 0x04013a03.
Lemma F_79c88 : fetch_word Plain.M.loaded_segments (0x79ce0 : word) = Some W_79c88.
Proof. vm_refl. Qed.
Lemma D_79c88 : decode_any W_79c88 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c8c : bv 32 := 0x03813a83.
Lemma F_79c8c : fetch_word Plain.M.loaded_segments (0x79ce4 : word) = Some W_79c8c.
Proof. vm_refl. Qed.
Lemma D_79c8c : decode_any W_79c8c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c90 : bv 32 := 0x03013b03.
Lemma F_79c90 : fetch_word Plain.M.loaded_segments (0x79ce8 : word) = Some W_79c90.
Proof. vm_refl. Qed.
Lemma D_79c90 : decode_any W_79c90 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c94 : bv 32 := 0x02813b83.
Lemma F_79c94 : fetch_word Plain.M.loaded_segments (0x79cec : word) = Some W_79c94.
Proof. vm_refl. Qed.
Lemma D_79c94 : decode_any W_79c94 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c98 : bv 32 := 0x02013c03.
Lemma F_79c98 : fetch_word Plain.M.loaded_segments (0x79cf0 : word) = Some W_79c98.
Proof. vm_refl. Qed.
Lemma D_79c98 : decode_any W_79c98 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c9c : bv 32 := 0x01813c83.
Lemma F_79c9c : fetch_word Plain.M.loaded_segments (0x79cf4 : word) = Some W_79c9c.
Proof. vm_refl. Qed.
Lemma D_79c9c : decode_any W_79c9c = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ca0 : bv 32 := 0x01013d03.
Lemma F_79ca0 : fetch_word Plain.M.loaded_segments (0x79cf8 : word) = Some W_79ca0.
Proof. vm_refl. Qed.
Lemma D_79ca0 : decode_any W_79ca0 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ca4 : bv 32 := 0x00813d83.
Lemma F_79ca4 : fetch_word Plain.M.loaded_segments (0x79cfc : word) = Some W_79ca4.
Proof. vm_refl. Qed.
Lemma D_79ca4 : decode_any W_79ca4 = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ca8 : bv 32 := 0x07010113.
Lemma F_79ca8 : fetch_word Plain.M.loaded_segments (0x79d00 : word) = Some W_79ca8.
Proof. vm_refl. Qed.
Lemma D_79ca8 : decode_any W_79ca8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cac : bv 32 := 0x00008067.
Lemma F_79cac : fetch_word Plain.M.loaded_segments (0x79d04 : word) = Some W_79cac.
Proof. vm_refl. Qed.
Lemma D_79cac : decode_any W_79cac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cb0 : bv 32 := 0x0059561b.
Lemma F_79cb0 : fetch_word Plain.M.loaded_segments (0x79d08 : word) = Some W_79cb0.
Proof. vm_refl. Qed.
Lemma D_79cb0 : decode_any W_79cb0 = Some (ShiftImm32 ALU_SRL 12 18 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cb4 : bv 32 := 0x00279693.
Lemma F_79cb4 : fetch_word Plain.M.loaded_segments (0x79d0c : word) = Some W_79cb4.
Proof. vm_refl. Qed.
Lemma D_79cb4 : decode_any W_79cb4 = Some (ShiftImm ALU_SLL 13 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cb8 : bv 32 := 0x00d506b3.
Lemma F_79cb8 : fetch_word Plain.M.loaded_segments (0x79d10 : word) = Some W_79cb8.
Proof. vm_refl. Qed.
Lemma D_79cb8 : decode_any W_79cb8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cbc : bv 32 := 0x00271a93.
Lemma F_79cbc : fetch_word Plain.M.loaded_segments (0x79d14 : word) = Some W_79cbc.
Proof. vm_refl. Qed.
Lemma D_79cbc : decode_any W_79cbc = Some (ShiftImm ALU_SLL 21 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cc0 : bv 32 := 0x01568ab3.
Lemma F_79cc0 : fetch_word Plain.M.loaded_segments (0x79d18 : word) = Some W_79cc0.
Proof. vm_refl. Qed.
Lemma D_79cc0 : decode_any W_79cc0 = Some (Op ALU_ADD 21 13 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cc4 : bv 32 := 0x14058863.
Lemma F_79cc4 : fetch_word Plain.M.loaded_segments (0x79d1c : word) = Some W_79cc4.
Proof. vm_refl. Qed.
Lemma D_79cc4 : decode_any W_79cc4 = Some (Branch BC_EQ 11 0 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cc8 : bv 32 := 0x00f00693.
Lemma F_79cc8 : fetch_word Plain.M.loaded_segments (0x79d20 : word) = Some W_79cc8.
Proof. vm_refl. Qed.
Lemma D_79cc8 : decode_any W_79cc8 = Some (OpImm ALU_ADD 13 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ccc : bv 32 := 0x0ad58e63.
Lemma F_79ccc : fetch_word Plain.M.loaded_segments (0x79d24 : word) = Some W_79ccc.
Proof. vm_refl. Qed.
Lemma D_79ccc : decode_any W_79ccc = Some (Branch BC_EQ 11 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d74 : bv 32 := 0x00000a13.
Lemma F_79d74 : fetch_word Plain.M.loaded_segments (0x79dcc : word) = Some W_79d74.
Proof. vm_refl. Qed.
Lemma D_79d74 : decode_any W_79d74 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d78 : bv 32 := 0x00100b93.
Lemma F_79d78 : fetch_word Plain.M.loaded_segments (0x79dd0 : word) = Some W_79d78.
Proof. vm_refl. Qed.
Lemma D_79d78 : decode_any W_79d78 = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d7c : bv 32 := 0x00f00713.
Lemma F_79d7c : fetch_word Plain.M.loaded_segments (0x79dd4 : word) = Some W_79d7c.
Proof. vm_refl. Qed.
Lemma D_79d7c : decode_any W_79d7c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d80 : bv 32 := 0xdae590e3.
Lemma F_79d80 : fetch_word Plain.M.loaded_segments (0x79dd8 : word) = Some W_79d80.
Proof. vm_refl. Qed.
Lemma D_79d80 : decode_any W_79d80 = Some (Branch BC_NE 11 14 7584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d84 : bv 32 := 0xe65ff06f.
Lemma F_79d84 : fetch_word Plain.M.loaded_segments (0x79ddc : word) = Some W_79d84.
Proof. vm_refl. Qed.
Lemma D_79d84 : decode_any W_79d84 = Some (Jal 0 2096740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d88 : bv 32 := 0x00000b93.
Lemma F_79d88 : fetch_word Plain.M.loaded_segments (0x79de0 : word) = Some W_79d88.
Proof. vm_refl. Qed.
Lemma D_79d88 : decode_any W_79d88 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d8c : bv 32 := 0x00f70733.
Lemma F_79d8c : fetch_word Plain.M.loaded_segments (0x79de4 : word) = Some W_79d8c.
Proof. vm_refl. Qed.
Lemma D_79d8c : decode_any W_79d8c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d90 : bv 32 := 0xfff60613.
Lemma F_79d90 : fetch_word Plain.M.loaded_segments (0x79de8 : word) = Some W_79d90.
Proof. vm_refl. Qed.
Lemma D_79d90 : decode_any W_79d90 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d94 : bv 32 := 0x02099593.
Lemma F_79d94 : fetch_word Plain.M.loaded_segments (0x79dec : word) = Some W_79d94.
Proof. vm_refl. Qed.
Lemma D_79d94 : decode_any W_79d94 = Some (ShiftImm ALU_SLL 11 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d98 : bv 32 := 0x00241993.
Lemma F_79d98 : fetch_word Plain.M.loaded_segments (0x79df0 : word) = Some W_79d98.
Proof. vm_refl. Qed.
Lemma D_79d98 : decode_any W_79d98 = Some (ShiftImm ALU_SLL 19 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d9c : bv 32 := 0x00271713.
Lemma F_79d9c : fetch_word Plain.M.loaded_segments (0x79df4 : word) = Some W_79d9c.
Proof. vm_refl. Qed.
Lemma D_79d9c : decode_any W_79d9c = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79da0 : bv 32 := 0x02061613.
Lemma F_79da0 : fetch_word Plain.M.loaded_segments (0x79df8 : word) = Some W_79da0.
Proof. vm_refl. Qed.
Lemma D_79da0 : decode_any W_79da0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79da4 : bv 32 := 0x0205d593.
Lemma F_79da4 : fetch_word Plain.M.loaded_segments (0x79dfc : word) = Some W_79da4.
Proof. vm_refl. Qed.
Lemma D_79da4 : decode_any W_79da4 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79da8 : bv 32 := 0x00e50533.
Lemma F_79da8 : fetch_word Plain.M.loaded_segments (0x79e00 : word) = Some W_79da8.
Proof. vm_refl. Qed.
Lemma D_79da8 : decode_any W_79da8 = Some (Op ALU_ADD 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dac : bv 32 := 0x01e65613.
Lemma F_79dac : fetch_word Plain.M.loaded_segments (0x79e04 : word) = Some W_79dac.
Proof. vm_refl. Qed.
Lemma D_79dac : decode_any W_79dac = Some (ShiftImm ALU_SRL 12 12 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79db0 : bv 32 := 0x40b00cb3.
Lemma F_79db0 : fetch_word Plain.M.loaded_segments (0x79e08 : word) = Some W_79db0.
Proof. vm_refl. Qed.
Lemma D_79db0 : decode_any W_79db0 = Some (Op ALU_SUB 25 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79db4 : bv 32 := 0x00460493.
Lemma F_79db4 : fetch_word Plain.M.loaded_segments (0x79e0c : word) = Some W_79db4.
Proof. vm_refl. Qed.
Lemma D_79db4 : decode_any W_79db4 = Some (OpImm ALU_ADD 9 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79db8 : bv 32 := 0x00050c13.
Lemma F_79db8 : fetch_word Plain.M.loaded_segments (0x79e10 : word) = Some W_79db8.
Proof. vm_refl. Qed.
Lemma D_79db8 : decode_any W_79db8 = Some (OpImm ALU_ADD 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dbc : bv 32 := 0x00a48533.
Lemma F_79dbc : fetch_word Plain.M.loaded_segments (0x79e14 : word) = Some W_79dbc.
Proof. vm_refl. Qed.
Lemma D_79dbc : decode_any W_79dbc = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dc0 : bv 32 := 0x00a13023.
Lemma F_79dc0 : fetch_word Plain.M.loaded_segments (0x79e18 : word) = Some W_79dc0.
Proof. vm_refl. Qed.
Lemma D_79dc0 : decode_any W_79dc0 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dc4 : bv 32 := 0x02000d93.
Lemma F_79dc4 : fetch_word Plain.M.loaded_segments (0x79e1c : word) = Some W_79dc4.
Proof. vm_refl. Qed.
Lemma D_79dc4 : decode_any W_79dc4 = Some (OpImm ALU_ADD 27 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dc8 : bv 32 := 0x0140006f.
Lemma F_79dc8 : fetch_word Plain.M.loaded_segments (0x79e20 : word) = Some W_79dc8.
Proof. vm_refl. Qed.
Lemma D_79dc8 : decode_any W_79dc8 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dcc : bv 32 := 0x008b8bbb.
Lemma F_79dcc : fetch_word Plain.M.loaded_segments (0x79e24 : word) = Some W_79dcc.
Proof. vm_refl. Qed.
Lemma D_79dcc : decode_any W_79dcc = Some (Op32 ALU_ADD 23 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dd0 : bv 32 := 0x001c8c93.
Lemma F_79dd0 : fetch_word Plain.M.loaded_segments (0x79e28 : word) = Some W_79dd0.
Proof. vm_refl. Qed.
Lemma D_79dd0 : decode_any W_79dd0 = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dd4 : bv 32 := 0x013a8ab3.
Lemma F_79dd4 : fetch_word Plain.M.loaded_segments (0x79e2c : word) = Some W_79dd4.
Proof. vm_refl. Qed.
Lemma D_79dd4 : decode_any W_79dd4 = Some (Op ALU_ADD 21 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dd8 : bv 32 := 0xe80c8ee3.
Lemma F_79dd8 : fetch_word Plain.M.loaded_segments (0x79e30 : word) = Some W_79dd8.
Proof. vm_refl. Qed.
Lemma D_79dd8 : decode_any W_79dd8 = Some (Branch BC_EQ 25 0 7836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ddc : bv 32 := 0x000a8d13.
Lemma F_79ddc : fetch_word Plain.M.loaded_segments (0x79e34 : word) = Some W_79ddc.
Proof. vm_refl. Qed.
Lemma D_79ddc : decode_any W_79ddc = Some (OpImm ALU_ADD 26 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79de0 : bv 32 := 0x03b96063.
Lemma F_79de0 : fetch_word Plain.M.loaded_segments (0x79e38 : word) = Some W_79de0.
Proof. vm_refl. Qed.
Lemma D_79de0 : decode_any W_79de0 = Some (Branch BC_LTU 18 27 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79de4 : bv 32 := 0x002b9d13.
Lemma F_79de4 : fetch_word Plain.M.loaded_segments (0x79e3c : word) = Some W_79de4.
Proof. vm_refl. Qed.
Lemma D_79de4 : decode_any W_79de4 = Some (ShiftImm ALU_SLL 26 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79de8 : bv 32 := 0x01ac0533.
Lemma F_79de8 : fetch_word Plain.M.loaded_segments (0x79e40 : word) = Some W_79de8.
Proof. vm_refl. Qed.
Lemma D_79de8 : decode_any W_79de8 = Some (Op ALU_ADD 10 24 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dec : bv 32 := 0x00013583.
Lemma F_79dec : fetch_word Plain.M.loaded_segments (0x79e44 : word) = Some W_79dec.
Proof. vm_refl. Qed.
Lemma D_79dec : decode_any W_79dec = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79df0 : bv 32 := 0x01a58d33.
Lemma F_79df0 : fetch_word Plain.M.loaded_segments (0x79e48 : word) = Some W_79df0.
Proof. vm_refl. Qed.
Lemma D_79df0 : decode_any W_79df0 = Some (Op ALU_ADD 26 11 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79df4 : bv 32 := 0x0ff00593.
Lemma F_79df4 : fetch_word Plain.M.loaded_segments (0x79e4c : word) = Some W_79df4.
Proof. vm_refl. Qed.
Lemma D_79df4 : decode_any W_79df4 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79df8 : bv 32 := 0x00048613.
Lemma F_79df8 : fetch_word Plain.M.loaded_segments (0x79e50 : word) = Some W_79df8.
Proof. vm_refl. Qed.
Lemma D_79df8 : decode_any W_79df8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dfc : bv 32 := 0x3dc900ef.
Lemma F_79dfc : fetch_word Plain.M.loaded_segments (0x79e54 : word) = Some W_79dfc.
Proof. vm_refl. Qed.
Lemma D_79dfc : decode_any W_79dfc = Some (Jal 1 590812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e00 : bv 32 := 0xfc0a06e3.
Lemma F_79e00 : fetch_word Plain.M.loaded_segments (0x79e58 : word) = Some W_79e00.
Proof. vm_refl. Qed.
Lemma D_79e00 : decode_any W_79e00 = Some (Branch BC_EQ 20 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e04 : bv 32 := 0x000d2503.
Lemma F_79e04 : fetch_word Plain.M.loaded_segments (0x79e5c : word) = Some W_79e04.
Proof. vm_refl. Qed.
Lemma D_79e04 : decode_any W_79e04 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e08 : bv 32 := 0x01656533.
Lemma F_79e08 : fetch_word Plain.M.loaded_segments (0x79e60 : word) = Some W_79e08.
Proof. vm_refl. Qed.
Lemma D_79e08 : decode_any W_79e08 = Some (Op ALU_OR 10 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e0c : bv 32 := 0x00ad2023.
Lemma F_79e0c : fetch_word Plain.M.loaded_segments (0x79e64 : word) = Some W_79e0c.
Proof. vm_refl. Qed.
Lemma D_79e0c : decode_any W_79e0c = Some (Store SZ4 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e10 : bv 32 := 0xfbdff06f.
Lemma F_79e10 : fetch_word Plain.M.loaded_segments (0x79e68 : word) = Some W_79e10.
Proof. vm_refl. Qed.
Lemma D_79e10 : decode_any W_79e10 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e14 : bv 32 := 0x00000b93.
Lemma F_79e14 : fetch_word Plain.M.loaded_segments (0x79e6c : word) = Some W_79e14.
Proof. vm_refl. Qed.
Lemma D_79e14 : decode_any W_79e14 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e18 : bv 32 := 0xfffb4593.
Lemma F_79e18 : fetch_word Plain.M.loaded_segments (0x79e70 : word) = Some W_79e18.
Proof. vm_refl. Qed.
Lemma D_79e18 : decode_any W_79e18 = Some (OpImm ALU_XOR 11 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e1c : bv 32 := 0x00b13023.
Lemma F_79e1c : fetch_word Plain.M.loaded_segments (0x79e74 : word) = Some W_79e1c.
Proof. vm_refl. Qed.
Lemma D_79e1c : decode_any W_79e1c = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e20 : bv 32 := 0x00f70733.
Lemma F_79e20 : fetch_word Plain.M.loaded_segments (0x79e78 : word) = Some W_79e20.
Proof. vm_refl. Qed.
Lemma D_79e20 : decode_any W_79e20 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e24 : bv 32 := 0xfff60613.
Lemma F_79e24 : fetch_word Plain.M.loaded_segments (0x79e7c : word) = Some W_79e24.
Proof. vm_refl. Qed.
Lemma D_79e24 : decode_any W_79e24 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e28 : bv 32 := 0x02099593.
Lemma F_79e28 : fetch_word Plain.M.loaded_segments (0x79e80 : word) = Some W_79e28.
Proof. vm_refl. Qed.
Lemma D_79e28 : decode_any W_79e28 = Some (ShiftImm ALU_SLL 11 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e2c : bv 32 := 0x00241993.
Lemma F_79e2c : fetch_word Plain.M.loaded_segments (0x79e84 : word) = Some W_79e2c.
Proof. vm_refl. Qed.
Lemma D_79e2c : decode_any W_79e2c = Some (ShiftImm ALU_SLL 19 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e30 : bv 32 := 0x00271713.
Lemma F_79e30 : fetch_word Plain.M.loaded_segments (0x79e88 : word) = Some W_79e30.
Proof. vm_refl. Qed.
Lemma D_79e30 : decode_any W_79e30 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e34 : bv 32 := 0x02061613.
Lemma F_79e34 : fetch_word Plain.M.loaded_segments (0x79e8c : word) = Some W_79e34.
Proof. vm_refl. Qed.
Lemma D_79e34 : decode_any W_79e34 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e38 : bv 32 := 0x0205d593.
Lemma F_79e38 : fetch_word Plain.M.loaded_segments (0x79e90 : word) = Some W_79e38.
Proof. vm_refl. Qed.
Lemma D_79e38 : decode_any W_79e38 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e3c : bv 32 := 0x00e50b33.
Lemma F_79e3c : fetch_word Plain.M.loaded_segments (0x79e94 : word) = Some W_79e3c.
Proof. vm_refl. Qed.
Lemma D_79e3c : decode_any W_79e3c = Some (Op ALU_ADD 22 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e40 : bv 32 := 0x01e65613.
Lemma F_79e40 : fetch_word Plain.M.loaded_segments (0x79e98 : word) = Some W_79e40.
Proof. vm_refl. Qed.
Lemma D_79e40 : decode_any W_79e40 = Some (ShiftImm ALU_SRL 12 12 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e44 : bv 32 := 0x40b00cb3.
Lemma F_79e44 : fetch_word Plain.M.loaded_segments (0x79e9c : word) = Some W_79e44.
Proof. vm_refl. Qed.
Lemma D_79e44 : decode_any W_79e44 = Some (Op ALU_SUB 25 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e48 : bv 32 := 0x00460493.
Lemma F_79e48 : fetch_word Plain.M.loaded_segments (0x79ea0 : word) = Some W_79e48.
Proof. vm_refl. Qed.
Lemma D_79e48 : decode_any W_79e48 = Some (OpImm ALU_ADD 9 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e4c : bv 32 := 0x01648c33.
Lemma F_79e4c : fetch_word Plain.M.loaded_segments (0x79ea4 : word) = Some W_79e4c.
Proof. vm_refl. Qed.
Lemma D_79e4c : decode_any W_79e4c = Some (Op ALU_ADD 24 9 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e50 : bv 32 := 0x02000d93.
Lemma F_79e50 : fetch_word Plain.M.loaded_segments (0x79ea8 : word) = Some W_79e50.
Proof. vm_refl. Qed.
Lemma D_79e50 : decode_any W_79e50 = Some (OpImm ALU_ADD 27 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e54 : bv 32 := 0x0140006f.
Lemma F_79e54 : fetch_word Plain.M.loaded_segments (0x79eac : word) = Some W_79e54.
Proof. vm_refl. Qed.
Lemma D_79e54 : decode_any W_79e54 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e58 : bv 32 := 0x008b8bbb.
Lemma F_79e58 : fetch_word Plain.M.loaded_segments (0x79eb0 : word) = Some W_79e58.
Proof. vm_refl. Qed.
Lemma D_79e58 : decode_any W_79e58 = Some (Op32 ALU_ADD 23 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e5c : bv 32 := 0x001c8c93.
Lemma F_79e5c : fetch_word Plain.M.loaded_segments (0x79eb4 : word) = Some W_79e5c.
Proof. vm_refl. Qed.
Lemma D_79e5c : decode_any W_79e5c = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e60 : bv 32 := 0x013a8ab3.
Lemma F_79e60 : fetch_word Plain.M.loaded_segments (0x79eb8 : word) = Some W_79e60.
Proof. vm_refl. Qed.
Lemma D_79e60 : decode_any W_79e60 = Some (Op ALU_ADD 21 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e64 : bv 32 := 0xe00c88e3.
Lemma F_79e64 : fetch_word Plain.M.loaded_segments (0x79ebc : word) = Some W_79e64.
Proof. vm_refl. Qed.
Lemma D_79e64 : decode_any W_79e64 = Some (Branch BC_EQ 25 0 7696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e68 : bv 32 := 0x000a8d13.
Lemma F_79e68 : fetch_word Plain.M.loaded_segments (0x79ec0 : word) = Some W_79e68.
Proof. vm_refl. Qed.
Lemma D_79e68 : decode_any W_79e68 = Some (OpImm ALU_ADD 26 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e6c : bv 32 := 0x01b96e63.
Lemma F_79e6c : fetch_word Plain.M.loaded_segments (0x79ec4 : word) = Some W_79e6c.
Proof. vm_refl. Qed.
Lemma D_79e6c : decode_any W_79e6c = Some (Branch BC_LTU 18 27 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e70 : bv 32 := 0x002b9d13.
Lemma F_79e70 : fetch_word Plain.M.loaded_segments (0x79ec8 : word) = Some W_79e70.
Proof. vm_refl. Qed.
Lemma D_79e70 : decode_any W_79e70 = Some (ShiftImm ALU_SLL 26 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e74 : bv 32 := 0x01ab0533.
Lemma F_79e74 : fetch_word Plain.M.loaded_segments (0x79ecc : word) = Some W_79e74.
Proof. vm_refl. Qed.
Lemma D_79e74 : decode_any W_79e74 = Some (Op ALU_ADD 10 22 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e78 : bv 32 := 0x01ac0d33.
Lemma F_79e78 : fetch_word Plain.M.loaded_segments (0x79ed0 : word) = Some W_79e78.
Proof. vm_refl. Qed.
Lemma D_79e78 : decode_any W_79e78 = Some (Op ALU_ADD 26 24 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e7c : bv 32 := 0x00000593.
Lemma F_79e7c : fetch_word Plain.M.loaded_segments (0x79ed4 : word) = Some W_79e7c.
Proof. vm_refl. Qed.
Lemma D_79e7c : decode_any W_79e7c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e80 : bv 32 := 0x00048613.
Lemma F_79e80 : fetch_word Plain.M.loaded_segments (0x79ed8 : word) = Some W_79e80.
Proof. vm_refl. Qed.
Lemma D_79e80 : decode_any W_79e80 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e84 : bv 32 := 0x354900ef.
Lemma F_79e84 : fetch_word Plain.M.loaded_segments (0x79edc : word) = Some W_79e84.
Proof. vm_refl. Qed.
Lemma D_79e84 : decode_any W_79e84 = Some (Jal 1 590676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e88 : bv 32 := 0xfc0a08e3.
Lemma F_79e88 : fetch_word Plain.M.loaded_segments (0x79ee0 : word) = Some W_79e88.
Proof. vm_refl. Qed.
Lemma D_79e88 : decode_any W_79e88 = Some (Branch BC_EQ 20 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e8c : bv 32 := 0x000d2503.
Lemma F_79e8c : fetch_word Plain.M.loaded_segments (0x79ee4 : word) = Some W_79e8c.
Proof. vm_refl. Qed.
Lemma D_79e8c : decode_any W_79e8c = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e90 : bv 32 := 0x00013583.
Lemma F_79e90 : fetch_word Plain.M.loaded_segments (0x79ee8 : word) = Some W_79e90.
Proof. vm_refl. Qed.
Lemma D_79e90 : decode_any W_79e90 = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e94 : bv 32 := 0x00b57533.
Lemma F_79e94 : fetch_word Plain.M.loaded_segments (0x79eec : word) = Some W_79e94.
Proof. vm_refl. Qed.
Lemma D_79e94 : decode_any W_79e94 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e98 : bv 32 := 0x00ad2023.
Lemma F_79e98 : fetch_word Plain.M.loaded_segments (0x79ef0 : word) = Some W_79e98.
Proof. vm_refl. Qed.
Lemma D_79e98 : decode_any W_79e98 = Some (Store SZ4 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e9c : bv 32 := 0xfbdff06f.
Lemma F_79e9c : fetch_word Plain.M.loaded_segments (0x79ef4 : word) = Some W_79e9c.
Proof. vm_refl. Qed.
Lemma D_79e9c : decode_any W_79e9c = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ef4 : bv 32 := 0x002b1413.
Lemma F_79ef4 : fetch_word Plain.M.loaded_segments (0x79f4c : word) = Some W_79ef4.
Proof. vm_refl. Qed.
Lemma D_79ef4 : decode_any W_79ef4 = Some (ShiftImm ALU_SLL 8 22 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ef8 : bv 32 := 0x00098c13.
Lemma F_79ef8 : fetch_word Plain.M.loaded_segments (0x79f50 : word) = Some W_79ef8.
Proof. vm_refl. Qed.
Lemma D_79ef8 : decode_any W_79ef8 = Some (OpImm ALU_ADD 24 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79efc : bv 32 := 0x0100006f.
Lemma F_79efc : fetch_word Plain.M.loaded_segments (0x79f54 : word) = Some W_79efc.
Proof. vm_refl. Qed.
Lemma D_79efc : decode_any W_79efc = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f00 : bv 32 := 0xfffc0c1b.
Lemma F_79f00 : fetch_word Plain.M.loaded_segments (0x79f58 : word) = Some W_79f00.
Proof. vm_refl. Qed.
Lemma D_79f00 : decode_any W_79f00 = Some (OpImm32 24 24 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f04 : bv 32 := 0x012484b3.
Lemma F_79f04 : fetch_word Plain.M.loaded_segments (0x79f5c : word) = Some W_79f04.
Proof. vm_refl. Qed.
Lemma D_79f04 : decode_any W_79f04 = Some (Op ALU_ADD 9 9 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f08 : bv 32 := 0xd00c04e3.
Lemma F_79f08 : fetch_word Plain.M.loaded_segments (0x79f60 : word) = Some W_79f08.
Proof. vm_refl. Qed.
Lemma D_79f08 : decode_any W_79f08 = Some (Branch BC_EQ 24 0 7432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f0c : bv 32 := 0xfe0b0ae3.
Lemma F_79f0c : fetch_word Plain.M.loaded_segments (0x79f64 : word) = Some W_79f0c.
Proof. vm_refl. Qed.
Lemma D_79f0c : decode_any W_79f0c = Some (Branch BC_EQ 22 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f10 : bv 32 := 0x0ff00593.
Lemma F_79f10 : fetch_word Plain.M.loaded_segments (0x79f68 : word) = Some W_79f10.
Proof. vm_refl. Qed.
Lemma D_79f10 : decode_any W_79f10 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f14 : bv 32 := 0x00048513.
Lemma F_79f14 : fetch_word Plain.M.loaded_segments (0x79f6c : word) = Some W_79f14.
Proof. vm_refl. Qed.
Lemma D_79f14 : decode_any W_79f14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f18 : bv 32 := 0x00040613.
Lemma F_79f18 : fetch_word Plain.M.loaded_segments (0x79f70 : word) = Some W_79f18.
Proof. vm_refl. Qed.
Lemma D_79f18 : decode_any W_79f18 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f1c : bv 32 := 0x2bc900ef.
Lemma F_79f1c : fetch_word Plain.M.loaded_segments (0x79f74 : word) = Some W_79f1c.
Proof. vm_refl. Qed.
Lemma D_79f1c : decode_any W_79f1c = Some (Jal 1 590524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f20 : bv 32 := 0xfe1ff06f.
Lemma F_79f20 : fetch_word Plain.M.loaded_segments (0x79f78 : word) = Some W_79f20.
Proof. vm_refl. Qed.
Lemma D_79f20 : decode_any W_79f20 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f24 : bv 32 := 0x002b1913.
Lemma F_79f24 : fetch_word Plain.M.loaded_segments (0x79f7c : word) = Some W_79f24.
Proof. vm_refl. Qed.
Lemma D_79f24 : decode_any W_79f24 = Some (ShiftImm ALU_SLL 18 22 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f28 : bv 32 := 0x00241c13.
Lemma F_79f28 : fetch_word Plain.M.loaded_segments (0x79f80 : word) = Some W_79f28.
Proof. vm_refl. Qed.
Lemma D_79f28 : decode_any W_79f28 = Some (ShiftImm ALU_SLL 24 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f2c : bv 32 := 0x00098c93.
Lemma F_79f2c : fetch_word Plain.M.loaded_segments (0x79f84 : word) = Some W_79f2c.
Proof. vm_refl. Qed.
Lemma D_79f2c : decode_any W_79f2c = Some (OpImm ALU_ADD 25 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f30 : bv 32 := 0x0100006f.
Lemma F_79f30 : fetch_word Plain.M.loaded_segments (0x79f88 : word) = Some W_79f30.
Proof. vm_refl. Qed.
Lemma D_79f30 : decode_any W_79f30 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f34 : bv 32 := 0xfffc8c9b.
Lemma F_79f34 : fetch_word Plain.M.loaded_segments (0x79f8c : word) = Some W_79f34.
Proof. vm_refl. Qed.
Lemma D_79f34 : decode_any W_79f34 = Some (OpImm32 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f38 : bv 32 := 0x018484b3.
Lemma F_79f38 : fetch_word Plain.M.loaded_segments (0x79f90 : word) = Some W_79f38.
Proof. vm_refl. Qed.
Lemma D_79f38 : decode_any W_79f38 = Some (Op ALU_ADD 9 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f3c : bv 32 := 0xc00c8ce3.
Lemma F_79f3c : fetch_word Plain.M.loaded_segments (0x79f94 : word) = Some W_79f3c.
Proof. vm_refl. Qed.
Lemma D_79f3c : decode_any W_79f3c = Some (Branch BC_EQ 25 0 7192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f40 : bv 32 := 0xfe0b0ae3.
Lemma F_79f40 : fetch_word Plain.M.loaded_segments (0x79f98 : word) = Some W_79f40.
Proof. vm_refl. Qed.
Lemma D_79f40 : decode_any W_79f40 = Some (Branch BC_EQ 22 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f44 : bv 32 := 0x00048513.
Lemma F_79f44 : fetch_word Plain.M.loaded_segments (0x79f9c : word) = Some W_79f44.
Proof. vm_refl. Qed.
Lemma D_79f44 : decode_any W_79f44 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f48 : bv 32 := 0x00000593.
Lemma F_79f48 : fetch_word Plain.M.loaded_segments (0x79fa0 : word) = Some W_79f48.
Proof. vm_refl. Qed.
Lemma D_79f48 : decode_any W_79f48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f4c : bv 32 := 0x00090613.
Lemma F_79f4c : fetch_word Plain.M.loaded_segments (0x79fa4 : word) = Some W_79f4c.
Proof. vm_refl. Qed.
Lemma D_79f4c : decode_any W_79f4c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f50 : bv 32 := 0x288900ef.
Lemma F_79f50 : fetch_word Plain.M.loaded_segments (0x79fa8 : word) = Some W_79f50.
Proof. vm_refl. Qed.
Lemma D_79f50 : decode_any W_79f50 = Some (Jal 1 590472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f54 : bv 32 := 0xfe1ff06f.
Lemma F_79f54 : fetch_word Plain.M.loaded_segments (0x79fac : word) = Some W_79f54.
Proof. vm_refl. Qed.
Lemma D_79f54 : decode_any W_79f54 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f58 : bv 32 := 0xf9010113.
Lemma F_79f58 : fetch_word Plain.M.loaded_segments (0x79fb0 : word) = Some W_79f58.
Proof. vm_refl. Qed.
Lemma D_79f58 : decode_any W_79f58 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f5c : bv 32 := 0x06113423.
Lemma F_79f5c : fetch_word Plain.M.loaded_segments (0x79fb4 : word) = Some W_79f5c.
Proof. vm_refl. Qed.
Lemma D_79f5c : decode_any W_79f5c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f60 : bv 32 := 0x06813023.
Lemma F_79f60 : fetch_word Plain.M.loaded_segments (0x79fb8 : word) = Some W_79f60.
Proof. vm_refl. Qed.
Lemma D_79f60 : decode_any W_79f60 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f64 : bv 32 := 0x04913c23.
Lemma F_79f64 : fetch_word Plain.M.loaded_segments (0x79fbc : word) = Some W_79f64.
Proof. vm_refl. Qed.
Lemma D_79f64 : decode_any W_79f64 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f68 : bv 32 := 0x05213823.
Lemma F_79f68 : fetch_word Plain.M.loaded_segments (0x79fc0 : word) = Some W_79f68.
Proof. vm_refl. Qed.
Lemma D_79f68 : decode_any W_79f68 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f6c : bv 32 := 0x05313423.
Lemma F_79f6c : fetch_word Plain.M.loaded_segments (0x79fc4 : word) = Some W_79f6c.
Proof. vm_refl. Qed.
Lemma D_79f6c : decode_any W_79f6c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f70 : bv 32 := 0x05413023.
Lemma F_79f70 : fetch_word Plain.M.loaded_segments (0x79fc8 : word) = Some W_79f70.
Proof. vm_refl. Qed.
Lemma D_79f70 : decode_any W_79f70 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f74 : bv 32 := 0x03513c23.
Lemma F_79f74 : fetch_word Plain.M.loaded_segments (0x79fcc : word) = Some W_79f74.
Proof. vm_refl. Qed.
Lemma D_79f74 : decode_any W_79f74 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f78 : bv 32 := 0x03613823.
Lemma F_79f78 : fetch_word Plain.M.loaded_segments (0x79fd0 : word) = Some W_79f78.
Proof. vm_refl. Qed.
Lemma D_79f78 : decode_any W_79f78 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f7c : bv 32 := 0x03713423.
Lemma F_79f7c : fetch_word Plain.M.loaded_segments (0x79fd4 : word) = Some W_79f7c.
Proof. vm_refl. Qed.
Lemma D_79f7c : decode_any W_79f7c = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f80 : bv 32 := 0x03813023.
Lemma F_79f80 : fetch_word Plain.M.loaded_segments (0x79fd8 : word) = Some W_79f80.
Proof. vm_refl. Qed.
Lemma D_79f80 : decode_any W_79f80 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f84 : bv 32 := 0x01913c23.
Lemma F_79f84 : fetch_word Plain.M.loaded_segments (0x79fdc : word) = Some W_79f84.
Proof. vm_refl. Qed.
Lemma D_79f84 : decode_any W_79f84 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f88 : bv 32 := 0x01a13823.
Lemma F_79f88 : fetch_word Plain.M.loaded_segments (0x79fe0 : word) = Some W_79f88.
Proof. vm_refl. Qed.
Lemma D_79f88 : decode_any W_79f88 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f8c : bv 32 := 0x01b13423.
Lemma F_79f8c : fetch_word Plain.M.loaded_segments (0x79fe4 : word) = Some W_79f8c.
Proof. vm_refl. Qed.
Lemma D_79f8c : decode_any W_79f8c = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f90 : bv 32 := 0x0a013383.
Lemma F_79f90 : fetch_word Plain.M.loaded_segments (0x79fe8 : word) = Some W_79f90.
Proof. vm_refl. Qed.
Lemma D_79f90 : decode_any W_79f90 = Some (Load SZ8 true 7 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f94 : bv 32 := 0x08813303.
Lemma F_79f94 : fetch_word Plain.M.loaded_segments (0x79fec : word) = Some W_79f94.
Proof. vm_refl. Qed.
Lemma D_79f94 : decode_any W_79f94 = Some (Load SZ8 true 6 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f98 : bv 32 := 0x00100e13.
Lemma F_79f98 : fetch_word Plain.M.loaded_segments (0x79ff0 : word) = Some W_79f98.
Proof. vm_refl. Qed.
Lemma D_79f98 : decode_any W_79f98 = Some (OpImm ALU_ADD 28 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f9c : bv 32 := 0x00050293.
Lemma F_79f9c : fetch_word Plain.M.loaded_segments (0x79ff4 : word) = Some W_79f9c.
Proof. vm_refl. Qed.
Lemma D_79f9c : decode_any W_79f9c = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa0 : bv 32 := 0x01c68c63.
Lemma F_79fa0 : fetch_word Plain.M.loaded_segments (0x79ff8 : word) = Some W_79fa0.
Proof. vm_refl. Qed.
Lemma D_79fa0 : decode_any W_79fa0 = Some (Branch BC_EQ 13 28 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa4 : bv 32 := 0x02b685b3.
Lemma F_79fa4 : fetch_word Plain.M.loaded_segments (0x79ffc : word) = Some W_79fa4.
Proof. vm_refl. Qed.
Lemma D_79fa4 : decode_any W_79fa4 = Some (Mul M_MUL 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa8 : bv 32 := 0x02d787bb.
Lemma F_79fa8 : fetch_word Plain.M.loaded_segments (0x7a000 : word) = Some W_79fa8.
Proof. vm_refl. Qed.
Lemma D_79fa8 : decode_any W_79fa8 = Some (Mul32 M_MUL 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fac : bv 32 := 0x02d888b3.
Lemma F_79fac : fetch_word Plain.M.loaded_segments (0x7a004 : word) = Some W_79fac.
Proof. vm_refl. Qed.
Lemma D_79fac : decode_any W_79fac = Some (Mul M_MUL 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb0 : bv 32 := 0x02d30333.
Lemma F_79fb0 : fetch_word Plain.M.loaded_segments (0x7a008 : word) = Some W_79fb0.
Proof. vm_refl. Qed.
Lemma D_79fb0 : decode_any W_79fb0 = Some (Mul M_MUL 6 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb4 : bv 32 := 0x02d383b3.
Lemma F_79fb4 : fetch_word Plain.M.loaded_segments (0x7a00c : word) = Some W_79fb4.
Proof. vm_refl. Qed.
Lemma D_79fb4 : decode_any W_79fb4 = Some (Mul M_MUL 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb8 : bv 32 := 0x43f7d513.
Lemma F_79fb8 : fetch_word Plain.M.loaded_segments (0x7a010 : word) = Some W_79fb8.
Proof. vm_refl. Qed.
Lemma D_79fb8 : decode_any W_79fb8 = Some (ShiftImm ALU_SRA 10 15 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fbc : bv 32 := 0x00f026b3.
Lemma F_79fbc : fetch_word Plain.M.loaded_segments (0x7a014 : word) = Some W_79fbc.
Proof. vm_refl. Qed.
Lemma D_79fbc : decode_any W_79fbc = Some (Op ALU_SLT 13 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc0 : bv 32 := 0x00f57533.
Lemma F_79fc0 : fetch_word Plain.M.loaded_segments (0x7a018 : word) = Some W_79fc0.
Proof. vm_refl. Qed.
Lemma D_79fc0 : decode_any W_79fc0 = Some (Op ALU_AND 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc4 : bv 32 := 0x40d006bb.
Lemma F_79fc4 : fetch_word Plain.M.loaded_segments (0x7a01c : word) = Some W_79fc4.
Proof. vm_refl. Qed.
Lemma D_79fc4 : decode_any W_79fc4 = Some (Op32 ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc8 : bv 32 := 0x40a383bb.
Lemma F_79fc8 : fetch_word Plain.M.loaded_segments (0x7a020 : word) = Some W_79fc8.
Proof. vm_refl. Qed.
Lemma D_79fc8 : decode_any W_79fc8 = Some (Op32 ALU_SUB 7 7 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fcc : bv 32 := 0x01150533.
Lemma F_79fcc : fetch_word Plain.M.loaded_segments (0x7a024 : word) = Some W_79fcc.
Proof. vm_refl. Qed.
Lemma D_79fcc : decode_any W_79fcc = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd0 : bv 32 := 0x00f6f6b3.
Lemma F_79fd0 : fetch_word Plain.M.loaded_segments (0x7a028 : word) = Some W_79fd0.
Proof. vm_refl. Qed.
Lemma D_79fd0 : decode_any W_79fd0 = Some (Op ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd4 : bv 32 := 0x007027b3.
Lemma F_79fd4 : fetch_word Plain.M.loaded_segments (0x7a02c : word) = Some W_79fd4.
Proof. vm_refl. Qed.
Lemma D_79fd4 : decode_any W_79fd4 = Some (Op ALU_SLT 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd8 : bv 32 := 0x43f3d893.
Lemma F_79fd8 : fetch_word Plain.M.loaded_segments (0x7a030 : word) = Some W_79fd8.
Proof. vm_refl. Qed.
Lemma D_79fd8 : decode_any W_79fd8 = Some (ShiftImm ALU_SRA 17 7 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fdc : bv 32 := 0x40f007b3.
Lemma F_79fdc : fetch_word Plain.M.loaded_segments (0x7a034 : word) = Some W_79fdc.
Proof. vm_refl. Qed.
Lemma D_79fdc : decode_any W_79fdc = Some (Op ALU_SUB 15 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe0 : bv 32 := 0x0078f8b3.
Lemma F_79fe0 : fetch_word Plain.M.loaded_segments (0x7a038 : word) = Some W_79fe0.
Proof. vm_refl. Qed.
Lemma D_79fe0 : decode_any W_79fe0 = Some (Op ALU_AND 17 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe4 : bv 32 := 0x0077fd33.
Lemma F_79fe4 : fetch_word Plain.M.loaded_segments (0x7a03c : word) = Some W_79fe4.
Proof. vm_refl. Qed.
Lemma D_79fe4 : decode_any W_79fe4 = Some (Op ALU_AND 26 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe8 : bv 32 := 0x01150533.
Lemma F_79fe8 : fetch_word Plain.M.loaded_segments (0x7a040 : word) = Some W_79fe8.
Proof. vm_refl. Qed.
Lemma D_79fe8 : decode_any W_79fe8 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fec : bv 32 := 0x411689bb.
Lemma F_79fec : fetch_word Plain.M.loaded_segments (0x7a044 : word) = Some W_79fec.
Proof. vm_refl. Qed.
Lemma D_79fec : decode_any W_79fec = Some (Op32 ALU_SUB 19 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff0 : bv 32 := 0x40b505bb.
Lemma F_79ff0 : fetch_word Plain.M.loaded_segments (0x7a048 : word) = Some W_79ff0.
Proof. vm_refl. Qed.
Lemma D_79ff0 : decode_any W_79ff0 = Some (Op32 ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff4 : bv 32 := 0x013585bb.
Lemma F_79ff4 : fetch_word Plain.M.loaded_segments (0x7a04c : word) = Some W_79ff4.
Proof. vm_refl. Qed.
Lemma D_79ff4 : decode_any W_79ff4 = Some (Op32 ALU_ADD 11 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff8 : bv 32 := 0x00b026b3.
Lemma F_79ff8 : fetch_word Plain.M.loaded_segments (0x7a050 : word) = Some W_79ff8.
Proof. vm_refl. Qed.
Lemma D_79ff8 : decode_any W_79ff8 = Some (Op ALU_SLT 13 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ffc : bv 32 := 0x40d006bb.
Lemma F_79ffc : fetch_word Plain.M.loaded_segments (0x7a054 : word) = Some W_79ffc.
Proof. vm_refl. Qed.
Lemma D_79ffc : decode_any W_79ffc = Some (Op32 ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.
