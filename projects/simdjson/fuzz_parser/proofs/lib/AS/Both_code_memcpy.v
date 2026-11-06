(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_parser.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1086dc : bv 32 := 0x0035f693.
Lemma F_1086dc : fetch_word AsanUbsan.M.loaded_segments (0x108898 : word) = Some W_1086dc.
Proof. vm_refl. Qed.
Lemma D_1086dc : decode_any W_1086dc = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086e0 : bv 32 := 0x10068863.
Lemma F_1086e0 : fetch_word AsanUbsan.M.loaded_segments (0x10889c : word) = Some W_1086e0.
Proof. vm_refl. Qed.
Lemma D_1086e0 : decode_any W_1086e0 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086e4 : bv 32 := 0x02060e63.
Lemma F_1086e4 : fetch_word AsanUbsan.M.loaded_segments (0x1088a0 : word) = Some W_1086e4.
Proof. vm_refl. Qed.
Lemma D_1086e4 : decode_any W_1086e4 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086e8 : bv 32 := 0x00158713.
Lemma F_1086e8 : fetch_word AsanUbsan.M.loaded_segments (0x1088a4 : word) = Some W_1086e8.
Proof. vm_refl. Qed.
Lemma D_1086e8 : decode_any W_1086e8 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086ec : bv 32 := 0x00100793.
Lemma F_1086ec : fetch_word AsanUbsan.M.loaded_segments (0x1088a8 : word) = Some W_1086ec.
Proof. vm_refl. Qed.
Lemma D_1086ec : decode_any W_1086ec = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086f0 : bv 32 := 0x00050693.
Lemma F_1086f0 : fetch_word AsanUbsan.M.loaded_segments (0x1088ac : word) = Some W_1086f0.
Proof. vm_refl. Qed.
Lemma D_1086f0 : decode_any W_1086f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086f4 : bv 32 := 0x0005c883.
Lemma F_1086f4 : fetch_word AsanUbsan.M.loaded_segments (0x1088b0 : word) = Some W_1086f4.
Proof. vm_refl. Qed.
Lemma D_1086f4 : decode_any W_1086f4 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086f8 : bv 32 := 0x00060813.
Lemma F_1086f8 : fetch_word AsanUbsan.M.loaded_segments (0x1088b4 : word) = Some W_1086f8.
Proof. vm_refl. Qed.
Lemma D_1086f8 : decode_any W_1086f8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1086fc : bv 32 := 0x00158593.
Lemma F_1086fc : fetch_word AsanUbsan.M.loaded_segments (0x1088b8 : word) = Some W_1086fc.
Proof. vm_refl. Qed.
Lemma D_1086fc : decode_any W_1086fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108700 : bv 32 := 0x00377293.
Lemma F_108700 : fetch_word AsanUbsan.M.loaded_segments (0x1088bc : word) = Some W_108700.
Proof. vm_refl. Qed.
Lemma D_108700 : decode_any W_108700 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108704 : bv 32 := 0x01168023.
Lemma F_108704 : fetch_word AsanUbsan.M.loaded_segments (0x1088c0 : word) = Some W_108704.
Proof. vm_refl. Qed.
Lemma D_108704 : decode_any W_108704 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108708 : bv 32 := 0x00168693.
Lemma F_108708 : fetch_word AsanUbsan.M.loaded_segments (0x1088c4 : word) = Some W_108708.
Proof. vm_refl. Qed.
Lemma D_108708 : decode_any W_108708 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10870c : bv 32 := 0xfff60613.
Lemma F_10870c : fetch_word AsanUbsan.M.loaded_segments (0x1088c8 : word) = Some W_10870c.
Proof. vm_refl. Qed.
Lemma D_10870c : decode_any W_10870c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108710 : bv 32 := 0x00028a63.
Lemma F_108710 : fetch_word AsanUbsan.M.loaded_segments (0x1088cc : word) = Some W_108710.
Proof. vm_refl. Qed.
Lemma D_108710 : decode_any W_108710 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108714 : bv 32 := 0x00170713.
Lemma F_108714 : fetch_word AsanUbsan.M.loaded_segments (0x1088d0 : word) = Some W_108714.
Proof. vm_refl. Qed.
Lemma D_108714 : decode_any W_108714 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108718 : bv 32 := 0xfcf81ee3.
Lemma F_108718 : fetch_word AsanUbsan.M.loaded_segments (0x1088d4 : word) = Some W_108718.
Proof. vm_refl. Qed.
Lemma D_108718 : decode_any W_108718 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10871c : bv 32 := 0x0080006f.
Lemma F_10871c : fetch_word AsanUbsan.M.loaded_segments (0x1088d8 : word) = Some W_10871c.
Proof. vm_refl. Qed.
Lemma D_10871c : decode_any W_10871c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108720 : bv 32 := 0x00050693.
Lemma F_108720 : fetch_word AsanUbsan.M.loaded_segments (0x1088dc : word) = Some W_108720.
Proof. vm_refl. Qed.
Lemma D_108720 : decode_any W_108720 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108724 : bv 32 := 0x0036f793.
Lemma F_108724 : fetch_word AsanUbsan.M.loaded_segments (0x1088e0 : word) = Some W_108724.
Proof. vm_refl. Qed.
Lemma D_108724 : decode_any W_108724 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108728 : bv 32 := 0x0c078a63.
Lemma F_108728 : fetch_word AsanUbsan.M.loaded_segments (0x1088e4 : word) = Some W_108728.
Proof. vm_refl. Qed.
Lemma D_108728 : decode_any W_108728 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10872c : bv 32 := 0x02000713.
Lemma F_10872c : fetch_word AsanUbsan.M.loaded_segments (0x1088e8 : word) = Some W_10872c.
Proof. vm_refl. Qed.
Lemma D_10872c : decode_any W_10872c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108730 : bv 32 := 0x02e67063.
Lemma F_108730 : fetch_word AsanUbsan.M.loaded_segments (0x1088ec : word) = Some W_108730.
Proof. vm_refl. Qed.
Lemma D_108730 : decode_any W_108730 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108734 : bv 32 := 0x01000713.
Lemma F_108734 : fetch_word AsanUbsan.M.loaded_segments (0x1088f0 : word) = Some W_108734.
Proof. vm_refl. Qed.
Lemma D_108734 : decode_any W_108734 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108738 : bv 32 := 0x24e67863.
Lemma F_108738 : fetch_word AsanUbsan.M.loaded_segments (0x1088f4 : word) = Some W_108738.
Proof. vm_refl. Qed.
Lemma D_108738 : decode_any W_108738 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10873c : bv 32 := 0x00867713.
Lemma F_10873c : fetch_word AsanUbsan.M.loaded_segments (0x1088f8 : word) = Some W_10873c.
Proof. vm_refl. Qed.
Lemma D_10873c : decode_any W_10873c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108740 : bv 32 := 0x2c071e63.
Lemma F_108740 : fetch_word AsanUbsan.M.loaded_segments (0x1088fc : word) = Some W_108740.
Proof. vm_refl. Qed.
Lemma D_108740 : decode_any W_108740 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108744 : bv 32 := 0x00467713.
Lemma F_108744 : fetch_word AsanUbsan.M.loaded_segments (0x108900 : word) = Some W_108744.
Proof. vm_refl. Qed.
Lemma D_108744 : decode_any W_108744 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108748 : bv 32 := 0x32071463.
Lemma F_108748 : fetch_word AsanUbsan.M.loaded_segments (0x108904 : word) = Some W_108748.
Proof. vm_refl. Qed.
Lemma D_108748 : decode_any W_108748 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10874c : bv 32 := 0x3500006f.
Lemma F_10874c : fetch_word AsanUbsan.M.loaded_segments (0x108908 : word) = Some W_10874c.
Proof. vm_refl. Qed.
Lemma D_10874c : decode_any W_10874c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108750 : bv 32 := 0x0005a703.
Lemma F_108750 : fetch_word AsanUbsan.M.loaded_segments (0x10890c : word) = Some W_108750.
Proof. vm_refl. Qed.
Lemma D_108750 : decode_any W_108750 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108754 : bv 32 := 0x00300813.
Lemma F_108754 : fetch_word AsanUbsan.M.loaded_segments (0x108910 : word) = Some W_108754.
Proof. vm_refl. Qed.
Lemma D_108754 : decode_any W_108754 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108758 : bv 32 := 0x11078e63.
Lemma F_108758 : fetch_word AsanUbsan.M.loaded_segments (0x108914 : word) = Some W_108758.
Proof. vm_refl. Qed.
Lemma D_108758 : decode_any W_108758 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10875c : bv 32 := 0x00200813.
Lemma F_10875c : fetch_word AsanUbsan.M.loaded_segments (0x108918 : word) = Some W_10875c.
Proof. vm_refl. Qed.
Lemma D_10875c : decode_any W_10875c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108760 : bv 32 := 0x19079c63.
Lemma F_108760 : fetch_word AsanUbsan.M.loaded_segments (0x10891c : word) = Some W_108760.
Proof. vm_refl. Qed.
Lemma D_108760 : decode_any W_108760 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108764 : bv 32 := 0x00875793.
Lemma F_108764 : fetch_word AsanUbsan.M.loaded_segments (0x108920 : word) = Some W_108764.
Proof. vm_refl. Qed.
Lemma D_108764 : decode_any W_108764 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108768 : bv 32 := 0xffe60613.
Lemma F_108768 : fetch_word AsanUbsan.M.loaded_segments (0x108924 : word) = Some W_108768.
Proof. vm_refl. Qed.
Lemma D_108768 : decode_any W_108768 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10876c : bv 32 := 0x00e68023.
Lemma F_10876c : fetch_word AsanUbsan.M.loaded_segments (0x108928 : word) = Some W_10876c.
Proof. vm_refl. Qed.
Lemma D_10876c : decode_any W_10876c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108770 : bv 32 := 0x00f680a3.
Lemma F_108770 : fetch_word AsanUbsan.M.loaded_segments (0x10892c : word) = Some W_108770.
Proof. vm_refl. Qed.
Lemma D_108770 : decode_any W_108770 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108774 : bv 32 := 0x00268693.
Lemma F_108774 : fetch_word AsanUbsan.M.loaded_segments (0x108930 : word) = Some W_108774.
Proof. vm_refl. Qed.
Lemma D_108774 : decode_any W_108774 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108778 : bv 32 := 0x01058593.
Lemma F_108778 : fetch_word AsanUbsan.M.loaded_segments (0x108934 : word) = Some W_108778.
Proof. vm_refl. Qed.
Lemma D_108778 : decode_any W_108778 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10877c : bv 32 := 0x01100793.
Lemma F_10877c : fetch_word AsanUbsan.M.loaded_segments (0x108938 : word) = Some W_10877c.
Proof. vm_refl. Qed.
Lemma D_10877c : decode_any W_10877c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108780 : bv 32 := 0x0107581b.
Lemma F_108780 : fetch_word AsanUbsan.M.loaded_segments (0x10893c : word) = Some W_108780.
Proof. vm_refl. Qed.
Lemma D_108780 : decode_any W_108780 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108784 : bv 32 := 0xff45a883.
Lemma F_108784 : fetch_word AsanUbsan.M.loaded_segments (0x108940 : word) = Some W_108784.
Proof. vm_refl. Qed.
Lemma D_108784 : decode_any W_108784 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108788 : bv 32 := 0xff85a283.
Lemma F_108788 : fetch_word AsanUbsan.M.loaded_segments (0x108944 : word) = Some W_108788.
Proof. vm_refl. Qed.
Lemma D_108788 : decode_any W_108788 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10878c : bv 32 := 0xffc5a303.
Lemma F_10878c : fetch_word AsanUbsan.M.loaded_segments (0x108948 : word) = Some W_10878c.
Proof. vm_refl. Qed.
Lemma D_10878c : decode_any W_10878c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108790 : bv 32 := 0x0005a703.
Lemma F_108790 : fetch_word AsanUbsan.M.loaded_segments (0x10894c : word) = Some W_108790.
Proof. vm_refl. Qed.
Lemma D_108790 : decode_any W_108790 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108794 : bv 32 := 0x01089393.
Lemma F_108794 : fetch_word AsanUbsan.M.loaded_segments (0x108950 : word) = Some W_108794.
Proof. vm_refl. Qed.
Lemma D_108794 : decode_any W_108794 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108798 : bv 32 := 0x0108d89b.
Lemma F_108798 : fetch_word AsanUbsan.M.loaded_segments (0x108954 : word) = Some W_108798.
Proof. vm_refl. Qed.
Lemma D_108798 : decode_any W_108798 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10879c : bv 32 := 0x0103e833.
Lemma F_10879c : fetch_word AsanUbsan.M.loaded_segments (0x108958 : word) = Some W_10879c.
Proof. vm_refl. Qed.
Lemma D_10879c : decode_any W_10879c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087a0 : bv 32 := 0x01029393.
Lemma F_1087a0 : fetch_word AsanUbsan.M.loaded_segments (0x10895c : word) = Some W_1087a0.
Proof. vm_refl. Qed.
Lemma D_1087a0 : decode_any W_1087a0 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087a4 : bv 32 := 0x0102d29b.
Lemma F_1087a4 : fetch_word AsanUbsan.M.loaded_segments (0x108960 : word) = Some W_1087a4.
Proof. vm_refl. Qed.
Lemma D_1087a4 : decode_any W_1087a4 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087a8 : bv 32 := 0x0113e8b3.
Lemma F_1087a8 : fetch_word AsanUbsan.M.loaded_segments (0x108964 : word) = Some W_1087a8.
Proof. vm_refl. Qed.
Lemma D_1087a8 : decode_any W_1087a8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087ac : bv 32 := 0x01031393.
Lemma F_1087ac : fetch_word AsanUbsan.M.loaded_segments (0x108968 : word) = Some W_1087ac.
Proof. vm_refl. Qed.
Lemma D_1087ac : decode_any W_1087ac = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087b0 : bv 32 := 0x0103531b.
Lemma F_1087b0 : fetch_word AsanUbsan.M.loaded_segments (0x10896c : word) = Some W_1087b0.
Proof. vm_refl. Qed.
Lemma D_1087b0 : decode_any W_1087b0 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087b4 : bv 32 := 0x0053e2b3.
Lemma F_1087b4 : fetch_word AsanUbsan.M.loaded_segments (0x108970 : word) = Some W_1087b4.
Proof. vm_refl. Qed.
Lemma D_1087b4 : decode_any W_1087b4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087b8 : bv 32 := 0x01071393.
Lemma F_1087b8 : fetch_word AsanUbsan.M.loaded_segments (0x108974 : word) = Some W_1087b8.
Proof. vm_refl. Qed.
Lemma D_1087b8 : decode_any W_1087b8 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087bc : bv 32 := 0x0063e333.
Lemma F_1087bc : fetch_word AsanUbsan.M.loaded_segments (0x108978 : word) = Some W_1087bc.
Proof. vm_refl. Qed.
Lemma D_1087bc : decode_any W_1087bc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087c0 : bv 32 := 0xff060613.
Lemma F_1087c0 : fetch_word AsanUbsan.M.loaded_segments (0x10897c : word) = Some W_1087c0.
Proof. vm_refl. Qed.
Lemma D_1087c0 : decode_any W_1087c0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087c4 : bv 32 := 0x0106a023.
Lemma F_1087c4 : fetch_word AsanUbsan.M.loaded_segments (0x108980 : word) = Some W_1087c4.
Proof. vm_refl. Qed.
Lemma D_1087c4 : decode_any W_1087c4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087c8 : bv 32 := 0x0116a223.
Lemma F_1087c8 : fetch_word AsanUbsan.M.loaded_segments (0x108984 : word) = Some W_1087c8.
Proof. vm_refl. Qed.
Lemma D_1087c8 : decode_any W_1087c8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087cc : bv 32 := 0x0056a423.
Lemma F_1087cc : fetch_word AsanUbsan.M.loaded_segments (0x108988 : word) = Some W_1087cc.
Proof. vm_refl. Qed.
Lemma D_1087cc : decode_any W_1087cc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087d0 : bv 32 := 0x0066a623.
Lemma F_1087d0 : fetch_word AsanUbsan.M.loaded_segments (0x10898c : word) = Some W_1087d0.
Proof. vm_refl. Qed.
Lemma D_1087d0 : decode_any W_1087d0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087d4 : bv 32 := 0x01068693.
Lemma F_1087d4 : fetch_word AsanUbsan.M.loaded_segments (0x108990 : word) = Some W_1087d4.
Proof. vm_refl. Qed.
Lemma D_1087d4 : decode_any W_1087d4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087d8 : bv 32 := 0x01058593.
Lemma F_1087d8 : fetch_word AsanUbsan.M.loaded_segments (0x108994 : word) = Some W_1087d8.
Proof. vm_refl. Qed.
Lemma D_1087d8 : decode_any W_1087d8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087dc : bv 32 := 0xfac7e2e3.
Lemma F_1087dc : fetch_word AsanUbsan.M.loaded_segments (0x108998 : word) = Some W_1087dc.
Proof. vm_refl. Qed.
Lemma D_1087dc : decode_any W_1087dc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087e0 : bv 32 := 0xff258593.
Lemma F_1087e0 : fetch_word AsanUbsan.M.loaded_segments (0x10899c : word) = Some W_1087e0.
Proof. vm_refl. Qed.
Lemma D_1087e0 : decode_any W_1087e0 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087e4 : bv 32 := 0x01000713.
Lemma F_1087e4 : fetch_word AsanUbsan.M.loaded_segments (0x1089a0 : word) = Some W_1087e4.
Proof. vm_refl. Qed.
Lemma D_1087e4 : decode_any W_1087e4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087e8 : bv 32 := 0xf4e66ae3.
Lemma F_1087e8 : fetch_word AsanUbsan.M.loaded_segments (0x1089a4 : word) = Some W_1087e8.
Proof. vm_refl. Qed.
Lemma D_1087e8 : decode_any W_1087e8 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087ec : bv 32 := 0x19c0006f.
Lemma F_1087ec : fetch_word AsanUbsan.M.loaded_segments (0x1089a8 : word) = Some W_1087ec.
Proof. vm_refl. Qed.
Lemma D_1087ec : decode_any W_1087ec = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087f0 : bv 32 := 0x00050693.
Lemma F_1087f0 : fetch_word AsanUbsan.M.loaded_segments (0x1089ac : word) = Some W_1087f0.
Proof. vm_refl. Qed.
Lemma D_1087f0 : decode_any W_1087f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087f4 : bv 32 := 0x00357793.
Lemma F_1087f4 : fetch_word AsanUbsan.M.loaded_segments (0x1089b0 : word) = Some W_1087f4.
Proof. vm_refl. Qed.
Lemma D_1087f4 : decode_any W_1087f4 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087f8 : bv 32 := 0xf2079ae3.
Lemma F_1087f8 : fetch_word AsanUbsan.M.loaded_segments (0x1089b4 : word) = Some W_1087f8.
Proof. vm_refl. Qed.
Lemma D_1087f8 : decode_any W_1087f8 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1087fc : bv 32 := 0x01000713.
Lemma F_1087fc : fetch_word AsanUbsan.M.loaded_segments (0x1089b8 : word) = Some W_1087fc.
Proof. vm_refl. Qed.
Lemma D_1087fc : decode_any W_1087fc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108800 : bv 32 := 0x02e66c63.
Lemma F_108800 : fetch_word AsanUbsan.M.loaded_segments (0x1089bc : word) = Some W_108800.
Proof. vm_refl. Qed.
Lemma D_108800 : decode_any W_108800 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108804 : bv 32 := 0x00f00713.
Lemma F_108804 : fetch_word AsanUbsan.M.loaded_segments (0x1089c0 : word) = Some W_108804.
Proof. vm_refl. Qed.
Lemma D_108804 : decode_any W_108804 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108808 : bv 32 := 0x0005a783.
Lemma F_108808 : fetch_word AsanUbsan.M.loaded_segments (0x1089c4 : word) = Some W_108808.
Proof. vm_refl. Qed.
Lemma D_108808 : decode_any W_108808 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10880c : bv 32 := 0x0045a803.
Lemma F_10880c : fetch_word AsanUbsan.M.loaded_segments (0x1089c8 : word) = Some W_10880c.
Proof. vm_refl. Qed.
Lemma D_10880c : decode_any W_10880c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108810 : bv 32 := 0x0085a883.
Lemma F_108810 : fetch_word AsanUbsan.M.loaded_segments (0x1089cc : word) = Some W_108810.
Proof. vm_refl. Qed.
Lemma D_108810 : decode_any W_108810 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108814 : bv 32 := 0x00c5a283.
Lemma F_108814 : fetch_word AsanUbsan.M.loaded_segments (0x1089d0 : word) = Some W_108814.
Proof. vm_refl. Qed.
Lemma D_108814 : decode_any W_108814 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108818 : bv 32 := 0x01058593.
Lemma F_108818 : fetch_word AsanUbsan.M.loaded_segments (0x1089d4 : word) = Some W_108818.
Proof. vm_refl. Qed.
Lemma D_108818 : decode_any W_108818 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10881c : bv 32 := 0xff060613.
Lemma F_10881c : fetch_word AsanUbsan.M.loaded_segments (0x1089d8 : word) = Some W_10881c.
Proof. vm_refl. Qed.
Lemma D_10881c : decode_any W_10881c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108820 : bv 32 := 0x00f6a023.
Lemma F_108820 : fetch_word AsanUbsan.M.loaded_segments (0x1089dc : word) = Some W_108820.
Proof. vm_refl. Qed.
Lemma D_108820 : decode_any W_108820 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108824 : bv 32 := 0x0106a223.
Lemma F_108824 : fetch_word AsanUbsan.M.loaded_segments (0x1089e0 : word) = Some W_108824.
Proof. vm_refl. Qed.
Lemma D_108824 : decode_any W_108824 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108828 : bv 32 := 0x0116a423.
Lemma F_108828 : fetch_word AsanUbsan.M.loaded_segments (0x1089e4 : word) = Some W_108828.
Proof. vm_refl. Qed.
Lemma D_108828 : decode_any W_108828 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10882c : bv 32 := 0x0056a623.
Lemma F_10882c : fetch_word AsanUbsan.M.loaded_segments (0x1089e8 : word) = Some W_10882c.
Proof. vm_refl. Qed.
Lemma D_10882c : decode_any W_10882c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108830 : bv 32 := 0x01068693.
Lemma F_108830 : fetch_word AsanUbsan.M.loaded_segments (0x1089ec : word) = Some W_108830.
Proof. vm_refl. Qed.
Lemma D_108830 : decode_any W_108830 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108834 : bv 32 := 0xfcc76ae3.
Lemma F_108834 : fetch_word AsanUbsan.M.loaded_segments (0x1089f0 : word) = Some W_108834.
Proof. vm_refl. Qed.
Lemma D_108834 : decode_any W_108834 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108838 : bv 32 := 0x00800713.
Lemma F_108838 : fetch_word AsanUbsan.M.loaded_segments (0x1089f4 : word) = Some W_108838.
Proof. vm_refl. Qed.
Lemma D_108838 : decode_any W_108838 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10883c : bv 32 := 0x00e66e63.
Lemma F_10883c : fetch_word AsanUbsan.M.loaded_segments (0x1089f8 : word) = Some W_10883c.
Proof. vm_refl. Qed.
Lemma D_10883c : decode_any W_10883c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108840 : bv 32 := 0x0005a703.
Lemma F_108840 : fetch_word AsanUbsan.M.loaded_segments (0x1089fc : word) = Some W_108840.
Proof. vm_refl. Qed.
Lemma D_108840 : decode_any W_108840 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108844 : bv 32 := 0x0045a783.
Lemma F_108844 : fetch_word AsanUbsan.M.loaded_segments (0x108a00 : word) = Some W_108844.
Proof. vm_refl. Qed.
Lemma D_108844 : decode_any W_108844 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108848 : bv 32 := 0x00e6a023.
Lemma F_108848 : fetch_word AsanUbsan.M.loaded_segments (0x108a04 : word) = Some W_108848.
Proof. vm_refl. Qed.
Lemma D_108848 : decode_any W_108848 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10884c : bv 32 := 0x00f6a223.
Lemma F_10884c : fetch_word AsanUbsan.M.loaded_segments (0x108a08 : word) = Some W_10884c.
Proof. vm_refl. Qed.
Lemma D_10884c : decode_any W_10884c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108850 : bv 32 := 0x00868693.
Lemma F_108850 : fetch_word AsanUbsan.M.loaded_segments (0x108a0c : word) = Some W_108850.
Proof. vm_refl. Qed.
Lemma D_108850 : decode_any W_108850 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108854 : bv 32 := 0x00858593.
Lemma F_108854 : fetch_word AsanUbsan.M.loaded_segments (0x108a10 : word) = Some W_108854.
Proof. vm_refl. Qed.
Lemma D_108854 : decode_any W_108854 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108858 : bv 32 := 0x00467713.
Lemma F_108858 : fetch_word AsanUbsan.M.loaded_segments (0x108a14 : word) = Some W_108858.
Proof. vm_refl. Qed.
Lemma D_108858 : decode_any W_108858 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10885c : bv 32 := 0x24070063.
Lemma F_10885c : fetch_word AsanUbsan.M.loaded_segments (0x108a18 : word) = Some W_10885c.
Proof. vm_refl. Qed.
Lemma D_10885c : decode_any W_10885c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108860 : bv 32 := 0x0005a703.
Lemma F_108860 : fetch_word AsanUbsan.M.loaded_segments (0x108a1c : word) = Some W_108860.
Proof. vm_refl. Qed.
Lemma D_108860 : decode_any W_108860 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108864 : bv 32 := 0x00458593.
Lemma F_108864 : fetch_word AsanUbsan.M.loaded_segments (0x108a20 : word) = Some W_108864.
Proof. vm_refl. Qed.
Lemma D_108864 : decode_any W_108864 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108868 : bv 32 := 0x00e6a023.
Lemma F_108868 : fetch_word AsanUbsan.M.loaded_segments (0x108a24 : word) = Some W_108868.
Proof. vm_refl. Qed.
Lemma D_108868 : decode_any W_108868 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10886c : bv 32 := 0x00468693.
Lemma F_10886c : fetch_word AsanUbsan.M.loaded_segments (0x108a28 : word) = Some W_10886c.
Proof. vm_refl. Qed.
Lemma D_10886c : decode_any W_10886c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108870 : bv 32 := 0x22c0006f.
Lemma F_108870 : fetch_word AsanUbsan.M.loaded_segments (0x108a2c : word) = Some W_108870.
Proof. vm_refl. Qed.
Lemma D_108870 : decode_any W_108870 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108874 : bv 32 := 0x00e68023.
Lemma F_108874 : fetch_word AsanUbsan.M.loaded_segments (0x108a30 : word) = Some W_108874.
Proof. vm_refl. Qed.
Lemma D_108874 : decode_any W_108874 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108878 : bv 32 := 0x00168693.
Lemma F_108878 : fetch_word AsanUbsan.M.loaded_segments (0x108a34 : word) = Some W_108878.
Proof. vm_refl. Qed.
Lemma D_108878 : decode_any W_108878 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10887c : bv 32 := 0xfff60613.
Lemma F_10887c : fetch_word AsanUbsan.M.loaded_segments (0x108a38 : word) = Some W_10887c.
Proof. vm_refl. Qed.
Lemma D_10887c : decode_any W_10887c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108880 : bv 32 := 0x01058593.
Lemma F_108880 : fetch_word AsanUbsan.M.loaded_segments (0x108a3c : word) = Some W_108880.
Proof. vm_refl. Qed.
Lemma D_108880 : decode_any W_108880 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108884 : bv 32 := 0x01200793.
Lemma F_108884 : fetch_word AsanUbsan.M.loaded_segments (0x108a40 : word) = Some W_108884.
Proof. vm_refl. Qed.
Lemma D_108884 : decode_any W_108884 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108888 : bv 32 := 0x0087581b.
Lemma F_108888 : fetch_word AsanUbsan.M.loaded_segments (0x108a44 : word) = Some W_108888.
Proof. vm_refl. Qed.
Lemma D_108888 : decode_any W_108888 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10888c : bv 32 := 0xff45a883.
Lemma F_10888c : fetch_word AsanUbsan.M.loaded_segments (0x108a48 : word) = Some W_10888c.
Proof. vm_refl. Qed.
Lemma D_10888c : decode_any W_10888c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108890 : bv 32 := 0xff85a283.
Lemma F_108890 : fetch_word AsanUbsan.M.loaded_segments (0x108a4c : word) = Some W_108890.
Proof. vm_refl. Qed.
Lemma D_108890 : decode_any W_108890 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108894 : bv 32 := 0xffc5a303.
Lemma F_108894 : fetch_word AsanUbsan.M.loaded_segments (0x108a50 : word) = Some W_108894.
Proof. vm_refl. Qed.
Lemma D_108894 : decode_any W_108894 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108898 : bv 32 := 0x0005a703.
Lemma F_108898 : fetch_word AsanUbsan.M.loaded_segments (0x108a54 : word) = Some W_108898.
Proof. vm_refl. Qed.
Lemma D_108898 : decode_any W_108898 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10889c : bv 32 := 0x01889393.
Lemma F_10889c : fetch_word AsanUbsan.M.loaded_segments (0x108a58 : word) = Some W_10889c.
Proof. vm_refl. Qed.
Lemma D_10889c : decode_any W_10889c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088a0 : bv 32 := 0x0088d89b.
Lemma F_1088a0 : fetch_word AsanUbsan.M.loaded_segments (0x108a5c : word) = Some W_1088a0.
Proof. vm_refl. Qed.
Lemma D_1088a0 : decode_any W_1088a0 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088a4 : bv 32 := 0x0103e833.
Lemma F_1088a4 : fetch_word AsanUbsan.M.loaded_segments (0x108a60 : word) = Some W_1088a4.
Proof. vm_refl. Qed.
Lemma D_1088a4 : decode_any W_1088a4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088a8 : bv 32 := 0x01829393.
Lemma F_1088a8 : fetch_word AsanUbsan.M.loaded_segments (0x108a64 : word) = Some W_1088a8.
Proof. vm_refl. Qed.
Lemma D_1088a8 : decode_any W_1088a8 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088ac : bv 32 := 0x0082d29b.
Lemma F_1088ac : fetch_word AsanUbsan.M.loaded_segments (0x108a68 : word) = Some W_1088ac.
Proof. vm_refl. Qed.
Lemma D_1088ac : decode_any W_1088ac = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088b0 : bv 32 := 0x0113e8b3.
Lemma F_1088b0 : fetch_word AsanUbsan.M.loaded_segments (0x108a6c : word) = Some W_1088b0.
Proof. vm_refl. Qed.
Lemma D_1088b0 : decode_any W_1088b0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088b4 : bv 32 := 0x01831393.
Lemma F_1088b4 : fetch_word AsanUbsan.M.loaded_segments (0x108a70 : word) = Some W_1088b4.
Proof. vm_refl. Qed.
Lemma D_1088b4 : decode_any W_1088b4 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088b8 : bv 32 := 0x0083531b.
Lemma F_1088b8 : fetch_word AsanUbsan.M.loaded_segments (0x108a74 : word) = Some W_1088b8.
Proof. vm_refl. Qed.
Lemma D_1088b8 : decode_any W_1088b8 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088bc : bv 32 := 0x0053e2b3.
Lemma F_1088bc : fetch_word AsanUbsan.M.loaded_segments (0x108a78 : word) = Some W_1088bc.
Proof. vm_refl. Qed.
Lemma D_1088bc : decode_any W_1088bc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088c0 : bv 32 := 0x01871393.
Lemma F_1088c0 : fetch_word AsanUbsan.M.loaded_segments (0x108a7c : word) = Some W_1088c0.
Proof. vm_refl. Qed.
Lemma D_1088c0 : decode_any W_1088c0 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088c4 : bv 32 := 0x0063e333.
Lemma F_1088c4 : fetch_word AsanUbsan.M.loaded_segments (0x108a80 : word) = Some W_1088c4.
Proof. vm_refl. Qed.
Lemma D_1088c4 : decode_any W_1088c4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088c8 : bv 32 := 0xff060613.
Lemma F_1088c8 : fetch_word AsanUbsan.M.loaded_segments (0x108a84 : word) = Some W_1088c8.
Proof. vm_refl. Qed.
Lemma D_1088c8 : decode_any W_1088c8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088cc : bv 32 := 0x0106a023.
Lemma F_1088cc : fetch_word AsanUbsan.M.loaded_segments (0x108a88 : word) = Some W_1088cc.
Proof. vm_refl. Qed.
Lemma D_1088cc : decode_any W_1088cc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088d0 : bv 32 := 0x0116a223.
Lemma F_1088d0 : fetch_word AsanUbsan.M.loaded_segments (0x108a8c : word) = Some W_1088d0.
Proof. vm_refl. Qed.
Lemma D_1088d0 : decode_any W_1088d0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088d4 : bv 32 := 0x0056a423.
Lemma F_1088d4 : fetch_word AsanUbsan.M.loaded_segments (0x108a90 : word) = Some W_1088d4.
Proof. vm_refl. Qed.
Lemma D_1088d4 : decode_any W_1088d4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088d8 : bv 32 := 0x0066a623.
Lemma F_1088d8 : fetch_word AsanUbsan.M.loaded_segments (0x108a94 : word) = Some W_1088d8.
Proof. vm_refl. Qed.
Lemma D_1088d8 : decode_any W_1088d8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088dc : bv 32 := 0x01068693.
Lemma F_1088dc : fetch_word AsanUbsan.M.loaded_segments (0x108a98 : word) = Some W_1088dc.
Proof. vm_refl. Qed.
Lemma D_1088dc : decode_any W_1088dc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088e0 : bv 32 := 0x01058593.
Lemma F_1088e0 : fetch_word AsanUbsan.M.loaded_segments (0x108a9c : word) = Some W_1088e0.
Proof. vm_refl. Qed.
Lemma D_1088e0 : decode_any W_1088e0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088e4 : bv 32 := 0xfac7e2e3.
Lemma F_1088e4 : fetch_word AsanUbsan.M.loaded_segments (0x108aa0 : word) = Some W_1088e4.
Proof. vm_refl. Qed.
Lemma D_1088e4 : decode_any W_1088e4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088e8 : bv 32 := 0xff158593.
Lemma F_1088e8 : fetch_word AsanUbsan.M.loaded_segments (0x108aa4 : word) = Some W_1088e8.
Proof. vm_refl. Qed.
Lemma D_1088e8 : decode_any W_1088e8 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088ec : bv 32 := 0x01000713.
Lemma F_1088ec : fetch_word AsanUbsan.M.loaded_segments (0x108aa8 : word) = Some W_1088ec.
Proof. vm_refl. Qed.
Lemma D_1088ec : decode_any W_1088ec = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088f0 : bv 32 := 0xe4e666e3.
Lemma F_1088f0 : fetch_word AsanUbsan.M.loaded_segments (0x108aac : word) = Some W_1088f0.
Proof. vm_refl. Qed.
Lemma D_1088f0 : decode_any W_1088f0 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088f4 : bv 32 := 0x0940006f.
Lemma F_1088f4 : fetch_word AsanUbsan.M.loaded_segments (0x108ab0 : word) = Some W_1088f4.
Proof. vm_refl. Qed.
Lemma D_1088f4 : decode_any W_1088f4 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088f8 : bv 32 := 0x00875793.
Lemma F_1088f8 : fetch_word AsanUbsan.M.loaded_segments (0x108ab4 : word) = Some W_1088f8.
Proof. vm_refl. Qed.
Lemma D_1088f8 : decode_any W_1088f8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1088fc : bv 32 := 0x01075813.
Lemma F_1088fc : fetch_word AsanUbsan.M.loaded_segments (0x108ab8 : word) = Some W_1088fc.
Proof. vm_refl. Qed.
Lemma D_1088fc : decode_any W_1088fc = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108900 : bv 32 := 0xffd60613.
Lemma F_108900 : fetch_word AsanUbsan.M.loaded_segments (0x108abc : word) = Some W_108900.
Proof. vm_refl. Qed.
Lemma D_108900 : decode_any W_108900 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108904 : bv 32 := 0x00e68023.
Lemma F_108904 : fetch_word AsanUbsan.M.loaded_segments (0x108ac0 : word) = Some W_108904.
Proof. vm_refl. Qed.
Lemma D_108904 : decode_any W_108904 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108908 : bv 32 := 0x00f680a3.
Lemma F_108908 : fetch_word AsanUbsan.M.loaded_segments (0x108ac4 : word) = Some W_108908.
Proof. vm_refl. Qed.
Lemma D_108908 : decode_any W_108908 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10890c : bv 32 := 0x01068123.
Lemma F_10890c : fetch_word AsanUbsan.M.loaded_segments (0x108ac8 : word) = Some W_10890c.
Proof. vm_refl. Qed.
Lemma D_10890c : decode_any W_10890c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108910 : bv 32 := 0x00368693.
Lemma F_108910 : fetch_word AsanUbsan.M.loaded_segments (0x108acc : word) = Some W_108910.
Proof. vm_refl. Qed.
Lemma D_108910 : decode_any W_108910 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108914 : bv 32 := 0x01058593.
Lemma F_108914 : fetch_word AsanUbsan.M.loaded_segments (0x108ad0 : word) = Some W_108914.
Proof. vm_refl. Qed.
Lemma D_108914 : decode_any W_108914 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108918 : bv 32 := 0x01000793.
Lemma F_108918 : fetch_word AsanUbsan.M.loaded_segments (0x108ad4 : word) = Some W_108918.
Proof. vm_refl. Qed.
Lemma D_108918 : decode_any W_108918 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10891c : bv 32 := 0x0187581b.
Lemma F_10891c : fetch_word AsanUbsan.M.loaded_segments (0x108ad8 : word) = Some W_10891c.
Proof. vm_refl. Qed.
Lemma D_10891c : decode_any W_10891c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108920 : bv 32 := 0xff45a883.
Lemma F_108920 : fetch_word AsanUbsan.M.loaded_segments (0x108adc : word) = Some W_108920.
Proof. vm_refl. Qed.
Lemma D_108920 : decode_any W_108920 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108924 : bv 32 := 0xff85a283.
Lemma F_108924 : fetch_word AsanUbsan.M.loaded_segments (0x108ae0 : word) = Some W_108924.
Proof. vm_refl. Qed.
Lemma D_108924 : decode_any W_108924 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108928 : bv 32 := 0xffc5a303.
Lemma F_108928 : fetch_word AsanUbsan.M.loaded_segments (0x108ae4 : word) = Some W_108928.
Proof. vm_refl. Qed.
Lemma D_108928 : decode_any W_108928 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10892c : bv 32 := 0x0005a703.
Lemma F_10892c : fetch_word AsanUbsan.M.loaded_segments (0x108ae8 : word) = Some W_10892c.
Proof. vm_refl. Qed.
Lemma D_10892c : decode_any W_10892c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108930 : bv 32 := 0x00889393.
Lemma F_108930 : fetch_word AsanUbsan.M.loaded_segments (0x108aec : word) = Some W_108930.
Proof. vm_refl. Qed.
Lemma D_108930 : decode_any W_108930 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108934 : bv 32 := 0x0188d89b.
Lemma F_108934 : fetch_word AsanUbsan.M.loaded_segments (0x108af0 : word) = Some W_108934.
Proof. vm_refl. Qed.
Lemma D_108934 : decode_any W_108934 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108938 : bv 32 := 0x0103e833.
Lemma F_108938 : fetch_word AsanUbsan.M.loaded_segments (0x108af4 : word) = Some W_108938.
Proof. vm_refl. Qed.
Lemma D_108938 : decode_any W_108938 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10893c : bv 32 := 0x00829393.
Lemma F_10893c : fetch_word AsanUbsan.M.loaded_segments (0x108af8 : word) = Some W_10893c.
Proof. vm_refl. Qed.
Lemma D_10893c : decode_any W_10893c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108940 : bv 32 := 0x0182d29b.
Lemma F_108940 : fetch_word AsanUbsan.M.loaded_segments (0x108afc : word) = Some W_108940.
Proof. vm_refl. Qed.
Lemma D_108940 : decode_any W_108940 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108944 : bv 32 := 0x0113e8b3.
Lemma F_108944 : fetch_word AsanUbsan.M.loaded_segments (0x108b00 : word) = Some W_108944.
Proof. vm_refl. Qed.
Lemma D_108944 : decode_any W_108944 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108948 : bv 32 := 0x00831393.
Lemma F_108948 : fetch_word AsanUbsan.M.loaded_segments (0x108b04 : word) = Some W_108948.
Proof. vm_refl. Qed.
Lemma D_108948 : decode_any W_108948 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10894c : bv 32 := 0x0183531b.
Lemma F_10894c : fetch_word AsanUbsan.M.loaded_segments (0x108b08 : word) = Some W_10894c.
Proof. vm_refl. Qed.
Lemma D_10894c : decode_any W_10894c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108950 : bv 32 := 0x0053e2b3.
Lemma F_108950 : fetch_word AsanUbsan.M.loaded_segments (0x108b0c : word) = Some W_108950.
Proof. vm_refl. Qed.
Lemma D_108950 : decode_any W_108950 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108954 : bv 32 := 0x00871393.
Lemma F_108954 : fetch_word AsanUbsan.M.loaded_segments (0x108b10 : word) = Some W_108954.
Proof. vm_refl. Qed.
Lemma D_108954 : decode_any W_108954 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108958 : bv 32 := 0x0063e333.
Lemma F_108958 : fetch_word AsanUbsan.M.loaded_segments (0x108b14 : word) = Some W_108958.
Proof. vm_refl. Qed.
Lemma D_108958 : decode_any W_108958 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10895c : bv 32 := 0xff060613.
Lemma F_10895c : fetch_word AsanUbsan.M.loaded_segments (0x108b18 : word) = Some W_10895c.
Proof. vm_refl. Qed.
Lemma D_10895c : decode_any W_10895c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108960 : bv 32 := 0x0106a023.
Lemma F_108960 : fetch_word AsanUbsan.M.loaded_segments (0x108b1c : word) = Some W_108960.
Proof. vm_refl. Qed.
Lemma D_108960 : decode_any W_108960 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108964 : bv 32 := 0x0116a223.
Lemma F_108964 : fetch_word AsanUbsan.M.loaded_segments (0x108b20 : word) = Some W_108964.
Proof. vm_refl. Qed.
Lemma D_108964 : decode_any W_108964 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108968 : bv 32 := 0x0056a423.
Lemma F_108968 : fetch_word AsanUbsan.M.loaded_segments (0x108b24 : word) = Some W_108968.
Proof. vm_refl. Qed.
Lemma D_108968 : decode_any W_108968 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10896c : bv 32 := 0x0066a623.
Lemma F_10896c : fetch_word AsanUbsan.M.loaded_segments (0x108b28 : word) = Some W_10896c.
Proof. vm_refl. Qed.
Lemma D_10896c : decode_any W_10896c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108970 : bv 32 := 0x01068693.
Lemma F_108970 : fetch_word AsanUbsan.M.loaded_segments (0x108b2c : word) = Some W_108970.
Proof. vm_refl. Qed.
Lemma D_108970 : decode_any W_108970 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108974 : bv 32 := 0x01058593.
Lemma F_108974 : fetch_word AsanUbsan.M.loaded_segments (0x108b30 : word) = Some W_108974.
Proof. vm_refl. Qed.
Lemma D_108974 : decode_any W_108974 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108978 : bv 32 := 0xfac7e2e3.
Lemma F_108978 : fetch_word AsanUbsan.M.loaded_segments (0x108b34 : word) = Some W_108978.
Proof. vm_refl. Qed.
Lemma D_108978 : decode_any W_108978 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10897c : bv 32 := 0xff358593.
Lemma F_10897c : fetch_word AsanUbsan.M.loaded_segments (0x108b38 : word) = Some W_10897c.
Proof. vm_refl. Qed.
Lemma D_10897c : decode_any W_10897c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108980 : bv 32 := 0x01000713.
Lemma F_108980 : fetch_word AsanUbsan.M.loaded_segments (0x108b3c : word) = Some W_108980.
Proof. vm_refl. Qed.
Lemma D_108980 : decode_any W_108980 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108984 : bv 32 := 0xdae66ce3.
Lemma F_108984 : fetch_word AsanUbsan.M.loaded_segments (0x108b40 : word) = Some W_108984.
Proof. vm_refl. Qed.
Lemma D_108984 : decode_any W_108984 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108988 : bv 32 := 0x0005c703.
Lemma F_108988 : fetch_word AsanUbsan.M.loaded_segments (0x108b44 : word) = Some W_108988.
Proof. vm_refl. Qed.
Lemma D_108988 : decode_any W_108988 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10898c : bv 32 := 0x0015c783.
Lemma F_10898c : fetch_word AsanUbsan.M.loaded_segments (0x108b48 : word) = Some W_10898c.
Proof. vm_refl. Qed.
Lemma D_10898c : decode_any W_10898c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108990 : bv 32 := 0x0025c803.
Lemma F_108990 : fetch_word AsanUbsan.M.loaded_segments (0x108b4c : word) = Some W_108990.
Proof. vm_refl. Qed.
Lemma D_108990 : decode_any W_108990 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108994 : bv 32 := 0x0035c883.
Lemma F_108994 : fetch_word AsanUbsan.M.loaded_segments (0x108b50 : word) = Some W_108994.
Proof. vm_refl. Qed.
Lemma D_108994 : decode_any W_108994 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108998 : bv 32 := 0x0045c283.
Lemma F_108998 : fetch_word AsanUbsan.M.loaded_segments (0x108b54 : word) = Some W_108998.
Proof. vm_refl. Qed.
Lemma D_108998 : decode_any W_108998 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10899c : bv 32 := 0x0055c303.
Lemma F_10899c : fetch_word AsanUbsan.M.loaded_segments (0x108b58 : word) = Some W_10899c.
Proof. vm_refl. Qed.
Lemma D_10899c : decode_any W_10899c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089a0 : bv 32 := 0x0065c383.
Lemma F_1089a0 : fetch_word AsanUbsan.M.loaded_segments (0x108b5c : word) = Some W_1089a0.
Proof. vm_refl. Qed.
Lemma D_1089a0 : decode_any W_1089a0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089a4 : bv 32 := 0x0075ce03.
Lemma F_1089a4 : fetch_word AsanUbsan.M.loaded_segments (0x108b60 : word) = Some W_1089a4.
Proof. vm_refl. Qed.
Lemma D_1089a4 : decode_any W_1089a4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089a8 : bv 32 := 0x00e68023.
Lemma F_1089a8 : fetch_word AsanUbsan.M.loaded_segments (0x108b64 : word) = Some W_1089a8.
Proof. vm_refl. Qed.
Lemma D_1089a8 : decode_any W_1089a8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089ac : bv 32 := 0x00f680a3.
Lemma F_1089ac : fetch_word AsanUbsan.M.loaded_segments (0x108b68 : word) = Some W_1089ac.
Proof. vm_refl. Qed.
Lemma D_1089ac : decode_any W_1089ac = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089b0 : bv 32 := 0x01068123.
Lemma F_1089b0 : fetch_word AsanUbsan.M.loaded_segments (0x108b6c : word) = Some W_1089b0.
Proof. vm_refl. Qed.
Lemma D_1089b0 : decode_any W_1089b0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089b4 : bv 32 := 0x011681a3.
Lemma F_1089b4 : fetch_word AsanUbsan.M.loaded_segments (0x108b70 : word) = Some W_1089b4.
Proof. vm_refl. Qed.
Lemma D_1089b4 : decode_any W_1089b4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089b8 : bv 32 := 0x0085c703.
Lemma F_1089b8 : fetch_word AsanUbsan.M.loaded_segments (0x108b74 : word) = Some W_1089b8.
Proof. vm_refl. Qed.
Lemma D_1089b8 : decode_any W_1089b8 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089bc : bv 32 := 0x0095c783.
Lemma F_1089bc : fetch_word AsanUbsan.M.loaded_segments (0x108b78 : word) = Some W_1089bc.
Proof. vm_refl. Qed.
Lemma D_1089bc : decode_any W_1089bc = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089c0 : bv 32 := 0x00a5c803.
Lemma F_1089c0 : fetch_word AsanUbsan.M.loaded_segments (0x108b7c : word) = Some W_1089c0.
Proof. vm_refl. Qed.
Lemma D_1089c0 : decode_any W_1089c0 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089c4 : bv 32 := 0x00b5c883.
Lemma F_1089c4 : fetch_word AsanUbsan.M.loaded_segments (0x108b80 : word) = Some W_1089c4.
Proof. vm_refl. Qed.
Lemma D_1089c4 : decode_any W_1089c4 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089c8 : bv 32 := 0x00568223.
Lemma F_1089c8 : fetch_word AsanUbsan.M.loaded_segments (0x108b84 : word) = Some W_1089c8.
Proof. vm_refl. Qed.
Lemma D_1089c8 : decode_any W_1089c8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089cc : bv 32 := 0x006682a3.
Lemma F_1089cc : fetch_word AsanUbsan.M.loaded_segments (0x108b88 : word) = Some W_1089cc.
Proof. vm_refl. Qed.
Lemma D_1089cc : decode_any W_1089cc = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089d0 : bv 32 := 0x00768323.
Lemma F_1089d0 : fetch_word AsanUbsan.M.loaded_segments (0x108b8c : word) = Some W_1089d0.
Proof. vm_refl. Qed.
Lemma D_1089d0 : decode_any W_1089d0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089d4 : bv 32 := 0x01c683a3.
Lemma F_1089d4 : fetch_word AsanUbsan.M.loaded_segments (0x108b90 : word) = Some W_1089d4.
Proof. vm_refl. Qed.
Lemma D_1089d4 : decode_any W_1089d4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089d8 : bv 32 := 0x00c5c283.
Lemma F_1089d8 : fetch_word AsanUbsan.M.loaded_segments (0x108b94 : word) = Some W_1089d8.
Proof. vm_refl. Qed.
Lemma D_1089d8 : decode_any W_1089d8 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089dc : bv 32 := 0x00d5c303.
Lemma F_1089dc : fetch_word AsanUbsan.M.loaded_segments (0x108b98 : word) = Some W_1089dc.
Proof. vm_refl. Qed.
Lemma D_1089dc : decode_any W_1089dc = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089e0 : bv 32 := 0x00e5c383.
Lemma F_1089e0 : fetch_word AsanUbsan.M.loaded_segments (0x108b9c : word) = Some W_1089e0.
Proof. vm_refl. Qed.
Lemma D_1089e0 : decode_any W_1089e0 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089e4 : bv 32 := 0x00f5ce03.
Lemma F_1089e4 : fetch_word AsanUbsan.M.loaded_segments (0x108ba0 : word) = Some W_1089e4.
Proof. vm_refl. Qed.
Lemma D_1089e4 : decode_any W_1089e4 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089e8 : bv 32 := 0x01058593.
Lemma F_1089e8 : fetch_word AsanUbsan.M.loaded_segments (0x108ba4 : word) = Some W_1089e8.
Proof. vm_refl. Qed.
Lemma D_1089e8 : decode_any W_1089e8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089ec : bv 32 := 0x00e68423.
Lemma F_1089ec : fetch_word AsanUbsan.M.loaded_segments (0x108ba8 : word) = Some W_1089ec.
Proof. vm_refl. Qed.
Lemma D_1089ec : decode_any W_1089ec = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089f0 : bv 32 := 0x00f684a3.
Lemma F_1089f0 : fetch_word AsanUbsan.M.loaded_segments (0x108bac : word) = Some W_1089f0.
Proof. vm_refl. Qed.
Lemma D_1089f0 : decode_any W_1089f0 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089f4 : bv 32 := 0x01068523.
Lemma F_1089f4 : fetch_word AsanUbsan.M.loaded_segments (0x108bb0 : word) = Some W_1089f4.
Proof. vm_refl. Qed.
Lemma D_1089f4 : decode_any W_1089f4 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089f8 : bv 32 := 0x011685a3.
Lemma F_1089f8 : fetch_word AsanUbsan.M.loaded_segments (0x108bb4 : word) = Some W_1089f8.
Proof. vm_refl. Qed.
Lemma D_1089f8 : decode_any W_1089f8 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1089fc : bv 32 := 0x01068713.
Lemma F_1089fc : fetch_word AsanUbsan.M.loaded_segments (0x108bb8 : word) = Some W_1089fc.
Proof. vm_refl. Qed.
Lemma D_1089fc : decode_any W_1089fc = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a00 : bv 32 := 0x00568623.
Lemma F_108a00 : fetch_word AsanUbsan.M.loaded_segments (0x108bbc : word) = Some W_108a00.
Proof. vm_refl. Qed.
Lemma D_108a00 : decode_any W_108a00 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a04 : bv 32 := 0x006686a3.
Lemma F_108a04 : fetch_word AsanUbsan.M.loaded_segments (0x108bc0 : word) = Some W_108a04.
Proof. vm_refl. Qed.
Lemma D_108a04 : decode_any W_108a04 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a08 : bv 32 := 0x00768723.
Lemma F_108a08 : fetch_word AsanUbsan.M.loaded_segments (0x108bc4 : word) = Some W_108a08.
Proof. vm_refl. Qed.
Lemma D_108a08 : decode_any W_108a08 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a0c : bv 32 := 0x01c687a3.
Lemma F_108a0c : fetch_word AsanUbsan.M.loaded_segments (0x108bc8 : word) = Some W_108a0c.
Proof. vm_refl. Qed.
Lemma D_108a0c : decode_any W_108a0c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a10 : bv 32 := 0x00070693.
Lemma F_108a10 : fetch_word AsanUbsan.M.loaded_segments (0x108bcc : word) = Some W_108a10.
Proof. vm_refl. Qed.
Lemma D_108a10 : decode_any W_108a10 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a14 : bv 32 := 0x00867713.
Lemma F_108a14 : fetch_word AsanUbsan.M.loaded_segments (0x108bd0 : word) = Some W_108a14.
Proof. vm_refl. Qed.
Lemma D_108a14 : decode_any W_108a14 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a18 : bv 32 := 0xd20706e3.
Lemma F_108a18 : fetch_word AsanUbsan.M.loaded_segments (0x108bd4 : word) = Some W_108a18.
Proof. vm_refl. Qed.
Lemma D_108a18 : decode_any W_108a18 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a1c : bv 32 := 0x0005c703.
Lemma F_108a1c : fetch_word AsanUbsan.M.loaded_segments (0x108bd8 : word) = Some W_108a1c.
Proof. vm_refl. Qed.
Lemma D_108a1c : decode_any W_108a1c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a20 : bv 32 := 0x0015c783.
Lemma F_108a20 : fetch_word AsanUbsan.M.loaded_segments (0x108bdc : word) = Some W_108a20.
Proof. vm_refl. Qed.
Lemma D_108a20 : decode_any W_108a20 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a24 : bv 32 := 0x0025c803.
Lemma F_108a24 : fetch_word AsanUbsan.M.loaded_segments (0x108be0 : word) = Some W_108a24.
Proof. vm_refl. Qed.
Lemma D_108a24 : decode_any W_108a24 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a28 : bv 32 := 0x0035c883.
Lemma F_108a28 : fetch_word AsanUbsan.M.loaded_segments (0x108be4 : word) = Some W_108a28.
Proof. vm_refl. Qed.
Lemma D_108a28 : decode_any W_108a28 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a2c : bv 32 := 0x0045c283.
Lemma F_108a2c : fetch_word AsanUbsan.M.loaded_segments (0x108be8 : word) = Some W_108a2c.
Proof. vm_refl. Qed.
Lemma D_108a2c : decode_any W_108a2c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a30 : bv 32 := 0x0055c303.
Lemma F_108a30 : fetch_word AsanUbsan.M.loaded_segments (0x108bec : word) = Some W_108a30.
Proof. vm_refl. Qed.
Lemma D_108a30 : decode_any W_108a30 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a34 : bv 32 := 0x0065c383.
Lemma F_108a34 : fetch_word AsanUbsan.M.loaded_segments (0x108bf0 : word) = Some W_108a34.
Proof. vm_refl. Qed.
Lemma D_108a34 : decode_any W_108a34 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a38 : bv 32 := 0x0075ce03.
Lemma F_108a38 : fetch_word AsanUbsan.M.loaded_segments (0x108bf4 : word) = Some W_108a38.
Proof. vm_refl. Qed.
Lemma D_108a38 : decode_any W_108a38 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a3c : bv 32 := 0x00858593.
Lemma F_108a3c : fetch_word AsanUbsan.M.loaded_segments (0x108bf8 : word) = Some W_108a3c.
Proof. vm_refl. Qed.
Lemma D_108a3c : decode_any W_108a3c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a40 : bv 32 := 0x00e68023.
Lemma F_108a40 : fetch_word AsanUbsan.M.loaded_segments (0x108bfc : word) = Some W_108a40.
Proof. vm_refl. Qed.
Lemma D_108a40 : decode_any W_108a40 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a44 : bv 32 := 0x00f680a3.
Lemma F_108a44 : fetch_word AsanUbsan.M.loaded_segments (0x108c00 : word) = Some W_108a44.
Proof. vm_refl. Qed.
Lemma D_108a44 : decode_any W_108a44 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a48 : bv 32 := 0x01068123.
Lemma F_108a48 : fetch_word AsanUbsan.M.loaded_segments (0x108c04 : word) = Some W_108a48.
Proof. vm_refl. Qed.
Lemma D_108a48 : decode_any W_108a48 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a4c : bv 32 := 0x011681a3.
Lemma F_108a4c : fetch_word AsanUbsan.M.loaded_segments (0x108c08 : word) = Some W_108a4c.
Proof. vm_refl. Qed.
Lemma D_108a4c : decode_any W_108a4c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a50 : bv 32 := 0x00868713.
Lemma F_108a50 : fetch_word AsanUbsan.M.loaded_segments (0x108c0c : word) = Some W_108a50.
Proof. vm_refl. Qed.
Lemma D_108a50 : decode_any W_108a50 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a54 : bv 32 := 0x00568223.
Lemma F_108a54 : fetch_word AsanUbsan.M.loaded_segments (0x108c10 : word) = Some W_108a54.
Proof. vm_refl. Qed.
Lemma D_108a54 : decode_any W_108a54 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a58 : bv 32 := 0x006682a3.
Lemma F_108a58 : fetch_word AsanUbsan.M.loaded_segments (0x108c14 : word) = Some W_108a58.
Proof. vm_refl. Qed.
Lemma D_108a58 : decode_any W_108a58 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a5c : bv 32 := 0x00768323.
Lemma F_108a5c : fetch_word AsanUbsan.M.loaded_segments (0x108c18 : word) = Some W_108a5c.
Proof. vm_refl. Qed.
Lemma D_108a5c : decode_any W_108a5c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a60 : bv 32 := 0x01c683a3.
Lemma F_108a60 : fetch_word AsanUbsan.M.loaded_segments (0x108c1c : word) = Some W_108a60.
Proof. vm_refl. Qed.
Lemma D_108a60 : decode_any W_108a60 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a64 : bv 32 := 0x00070693.
Lemma F_108a64 : fetch_word AsanUbsan.M.loaded_segments (0x108c20 : word) = Some W_108a64.
Proof. vm_refl. Qed.
Lemma D_108a64 : decode_any W_108a64 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a68 : bv 32 := 0x00467713.
Lemma F_108a68 : fetch_word AsanUbsan.M.loaded_segments (0x108c24 : word) = Some W_108a68.
Proof. vm_refl. Qed.
Lemma D_108a68 : decode_any W_108a68 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a6c : bv 32 := 0x02070863.
Lemma F_108a6c : fetch_word AsanUbsan.M.loaded_segments (0x108c28 : word) = Some W_108a6c.
Proof. vm_refl. Qed.
Lemma D_108a6c : decode_any W_108a6c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a70 : bv 32 := 0x0005c703.
Lemma F_108a70 : fetch_word AsanUbsan.M.loaded_segments (0x108c2c : word) = Some W_108a70.
Proof. vm_refl. Qed.
Lemma D_108a70 : decode_any W_108a70 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a74 : bv 32 := 0x0015c783.
Lemma F_108a74 : fetch_word AsanUbsan.M.loaded_segments (0x108c30 : word) = Some W_108a74.
Proof. vm_refl. Qed.
Lemma D_108a74 : decode_any W_108a74 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a78 : bv 32 := 0x0025c803.
Lemma F_108a78 : fetch_word AsanUbsan.M.loaded_segments (0x108c34 : word) = Some W_108a78.
Proof. vm_refl. Qed.
Lemma D_108a78 : decode_any W_108a78 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a7c : bv 32 := 0x0035c883.
Lemma F_108a7c : fetch_word AsanUbsan.M.loaded_segments (0x108c38 : word) = Some W_108a7c.
Proof. vm_refl. Qed.
Lemma D_108a7c : decode_any W_108a7c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a80 : bv 32 := 0x00458593.
Lemma F_108a80 : fetch_word AsanUbsan.M.loaded_segments (0x108c3c : word) = Some W_108a80.
Proof. vm_refl. Qed.
Lemma D_108a80 : decode_any W_108a80 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a84 : bv 32 := 0x00468293.
Lemma F_108a84 : fetch_word AsanUbsan.M.loaded_segments (0x108c40 : word) = Some W_108a84.
Proof. vm_refl. Qed.
Lemma D_108a84 : decode_any W_108a84 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a88 : bv 32 := 0x00e68023.
Lemma F_108a88 : fetch_word AsanUbsan.M.loaded_segments (0x108c44 : word) = Some W_108a88.
Proof. vm_refl. Qed.
Lemma D_108a88 : decode_any W_108a88 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a8c : bv 32 := 0x00f680a3.
Lemma F_108a8c : fetch_word AsanUbsan.M.loaded_segments (0x108c48 : word) = Some W_108a8c.
Proof. vm_refl. Qed.
Lemma D_108a8c : decode_any W_108a8c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a90 : bv 32 := 0x01068123.
Lemma F_108a90 : fetch_word AsanUbsan.M.loaded_segments (0x108c4c : word) = Some W_108a90.
Proof. vm_refl. Qed.
Lemma D_108a90 : decode_any W_108a90 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a94 : bv 32 := 0x011681a3.
Lemma F_108a94 : fetch_word AsanUbsan.M.loaded_segments (0x108c50 : word) = Some W_108a94.
Proof. vm_refl. Qed.
Lemma D_108a94 : decode_any W_108a94 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a98 : bv 32 := 0x00028693.
Lemma F_108a98 : fetch_word AsanUbsan.M.loaded_segments (0x108c54 : word) = Some W_108a98.
Proof. vm_refl. Qed.
Lemma D_108a98 : decode_any W_108a98 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108a9c : bv 32 := 0x00267713.
Lemma F_108a9c : fetch_word AsanUbsan.M.loaded_segments (0x108c58 : word) = Some W_108a9c.
Proof. vm_refl. Qed.
Lemma D_108a9c : decode_any W_108a9c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108aa0 : bv 32 := 0x00071863.
Lemma F_108aa0 : fetch_word AsanUbsan.M.loaded_segments (0x108c5c : word) = Some W_108aa0.
Proof. vm_refl. Qed.
Lemma D_108aa0 : decode_any W_108aa0 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108aa4 : bv 32 := 0x00167613.
Lemma F_108aa4 : fetch_word AsanUbsan.M.loaded_segments (0x108c60 : word) = Some W_108aa4.
Proof. vm_refl. Qed.
Lemma D_108aa4 : decode_any W_108aa4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108aa8 : bv 32 := 0x02061663.
Lemma F_108aa8 : fetch_word AsanUbsan.M.loaded_segments (0x108c64 : word) = Some W_108aa8.
Proof. vm_refl. Qed.
Lemma D_108aa8 : decode_any W_108aa8 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108aac : bv 32 := 0x00008067.
Lemma F_108aac : fetch_word AsanUbsan.M.loaded_segments (0x108c68 : word) = Some W_108aac.
Proof. vm_refl. Qed.
Lemma D_108aac : decode_any W_108aac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ab0 : bv 32 := 0x0005c703.
Lemma F_108ab0 : fetch_word AsanUbsan.M.loaded_segments (0x108c6c : word) = Some W_108ab0.
Proof. vm_refl. Qed.
Lemma D_108ab0 : decode_any W_108ab0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ab4 : bv 32 := 0x0015c783.
Lemma F_108ab4 : fetch_word AsanUbsan.M.loaded_segments (0x108c70 : word) = Some W_108ab4.
Proof. vm_refl. Qed.
Lemma D_108ab4 : decode_any W_108ab4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ab8 : bv 32 := 0x00258593.
Lemma F_108ab8 : fetch_word AsanUbsan.M.loaded_segments (0x108c74 : word) = Some W_108ab8.
Proof. vm_refl. Qed.
Lemma D_108ab8 : decode_any W_108ab8 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108abc : bv 32 := 0x00268813.
Lemma F_108abc : fetch_word AsanUbsan.M.loaded_segments (0x108c78 : word) = Some W_108abc.
Proof. vm_refl. Qed.
Lemma D_108abc : decode_any W_108abc = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ac0 : bv 32 := 0x00e68023.
Lemma F_108ac0 : fetch_word AsanUbsan.M.loaded_segments (0x108c7c : word) = Some W_108ac0.
Proof. vm_refl. Qed.
Lemma D_108ac0 : decode_any W_108ac0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ac4 : bv 32 := 0x00f680a3.
Lemma F_108ac4 : fetch_word AsanUbsan.M.loaded_segments (0x108c80 : word) = Some W_108ac4.
Proof. vm_refl. Qed.
Lemma D_108ac4 : decode_any W_108ac4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ac8 : bv 32 := 0x00080693.
Lemma F_108ac8 : fetch_word AsanUbsan.M.loaded_segments (0x108c84 : word) = Some W_108ac8.
Proof. vm_refl. Qed.
Lemma D_108ac8 : decode_any W_108ac8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108acc : bv 32 := 0x00167613.
Lemma F_108acc : fetch_word AsanUbsan.M.loaded_segments (0x108c88 : word) = Some W_108acc.
Proof. vm_refl. Qed.
Lemma D_108acc : decode_any W_108acc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ad0 : bv 32 := 0xfc060ee3.
Lemma F_108ad0 : fetch_word AsanUbsan.M.loaded_segments (0x108c8c : word) = Some W_108ad0.
Proof. vm_refl. Qed.
Lemma D_108ad0 : decode_any W_108ad0 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ad4 : bv 32 := 0x0005c583.
Lemma F_108ad4 : fetch_word AsanUbsan.M.loaded_segments (0x108c90 : word) = Some W_108ad4.
Proof. vm_refl. Qed.
Lemma D_108ad4 : decode_any W_108ad4 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ad8 : bv 32 := 0x00b68023.
Lemma F_108ad8 : fetch_word AsanUbsan.M.loaded_segments (0x108c94 : word) = Some W_108ad8.
Proof. vm_refl. Qed.
Lemma D_108ad8 : decode_any W_108ad8 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108adc : bv 32 := 0x00008067.
Lemma F_108adc : fetch_word AsanUbsan.M.loaded_segments (0x108c98 : word) = Some W_108adc.
Proof. vm_refl. Qed.
Lemma D_108adc : decode_any W_108adc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
