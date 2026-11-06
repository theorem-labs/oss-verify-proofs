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
Definition W_22780 : bv 32 := 0xfffee197.
Lemma F_22780 : fetch_word Ubsan.M.loaded_segments (0x22780 : word) = Some W_22780.
Proof. vm_refl. Qed.
Lemma D_22780 : decode_any W_22780 = Some (Auipc 3 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22784 : bv 32 := 0x08018193.
Lemma F_22784 : fetch_word Ubsan.M.loaded_segments (0x22784 : word) = Some W_22784.
Proof. vm_refl. Qed.
Lemma D_22784 : decode_any W_22784 = Some (OpImm ALU_ADD 3 3 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22788 : bv 32 := 0x00010513.
Lemma F_22788 : fetch_word Ubsan.M.loaded_segments (0x22788 : word) = Some W_22788.
Proof. vm_refl. Qed.
Lemma D_22788 : decode_any W_22788 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2278c : bv 32 := 0xfffde597.
Lemma F_2278c : fetch_word Ubsan.M.loaded_segments (0x2278c : word) = Some W_2278c.
Proof. vm_refl. Qed.
Lemma D_2278c : decode_any W_2278c = Some (Auipc 11 1048542, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22790 : bv 32 := 0x87458593.
Lemma F_22790 : fetch_word Ubsan.M.loaded_segments (0x22790 : word) = Some W_22790.
Proof. vm_refl. Qed.
Lemma D_22790 : decode_any W_22790 = Some (OpImm ALU_ADD 11 11 2164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22794 : bv 32 := 0xff017113.
Lemma F_22794 : fetch_word Ubsan.M.loaded_segments (0x22794 : word) = Some W_22794.
Proof. vm_refl. Qed.
Lemma D_22794 : decode_any W_22794 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22798 : bv 32 := 0x0040006f.
Lemma F_22798 : fetch_word Ubsan.M.loaded_segments (0x22798 : word) = Some W_22798.
Proof. vm_refl. Qed.
Lemma D_22798 : decode_any W_22798 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2279c : bv 32 := 0x00052583.
Lemma F_2279c : fetch_word Ubsan.M.loaded_segments (0x2279c : word) = Some W_2279c.
Proof. vm_refl. Qed.
Lemma D_2279c : decode_any W_2279c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227a0 : bv 32 := 0x00043617.
Lemma F_227a0 : fetch_word Ubsan.M.loaded_segments (0x227a0 : word) = Some W_227a0.
Proof. vm_refl. Qed.
Lemma D_227a0 : decode_any W_227a0 = Some (Auipc 12 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227a4 : bv 32 := 0x00043697.
Lemma F_227a4 : fetch_word Ubsan.M.loaded_segments (0x227a4 : word) = Some W_227a4.
Proof. vm_refl. Qed.
Lemma D_227a4 : decode_any W_227a4 = Some (Auipc 13 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227a8 : bv 32 := 0x00043717.
Lemma F_227a8 : fetch_word Ubsan.M.loaded_segments (0x227a8 : word) = Some W_227a8.
Proof. vm_refl. Qed.
Lemma D_227a8 : decode_any W_227a8 = Some (Auipc 14 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227ac : bv 32 := 0x28863783.
Lemma F_227ac : fetch_word Ubsan.M.loaded_segments (0x227ac : word) = Some W_227ac.
Proof. vm_refl. Qed.
Lemma D_227ac : decode_any W_227ac = Some (Load SZ8 true 15 12 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227b0 : bv 32 := 0x28c6b683.
Lemma F_227b0 : fetch_word Ubsan.M.loaded_segments (0x227b0 : word) = Some W_227b0.
Proof. vm_refl. Qed.
Lemma D_227b0 : decode_any W_227b0 = Some (Load SZ8 true 13 13 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227b4 : bv 32 := 0x29073703.
Lemma F_227b4 : fetch_word Ubsan.M.loaded_segments (0x227b4 : word) = Some W_227b4.
Proof. vm_refl. Qed.
Lemma D_227b4 : decode_any W_227b4 = Some (Load SZ8 true 14 14 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227b8 : bv 32 := 0x00850613.
Lemma F_227b8 : fetch_word Ubsan.M.loaded_segments (0x227b8 : word) = Some W_227b8.
Proof. vm_refl. Qed.
Lemma D_227b8 : decode_any W_227b8 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227bc : bv 32 := 0x00078513.
Lemma F_227bc : fetch_word Ubsan.M.loaded_segments (0x227bc : word) = Some W_227bc.
Proof. vm_refl. Qed.
Lemma D_227bc : decode_any W_227bc = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227c0 : bv 32 := 0x00000793.
Lemma F_227c0 : fetch_word Ubsan.M.loaded_segments (0x227c0 : word) = Some W_227c0.
Proof. vm_refl. Qed.
Lemma D_227c0 : decode_any W_227c0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227c4 : bv 32 := 0x5f52f06f.
Lemma F_227c4 : fetch_word Ubsan.M.loaded_segments (0x227c4 : word) = Some W_227c4.
Proof. vm_refl. Qed.
Lemma D_227c4 : decode_any W_227c4 = Some (Jal 0 196084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227c8 : bv 32 := 0xff010113.
Lemma F_227c8 : fetch_word Ubsan.M.loaded_segments (0x227c8 : word) = Some W_227c8.
Proof. vm_refl. Qed.
Lemma D_227c8 : decode_any W_227c8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227cc : bv 32 := 0x00113423.
Lemma F_227cc : fetch_word Ubsan.M.loaded_segments (0x227cc : word) = Some W_227cc.
Proof. vm_refl. Qed.
Lemma D_227cc : decode_any W_227cc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227d0 : bv 32 := 0x00813023.
Lemma F_227d0 : fetch_word Ubsan.M.loaded_segments (0x227d0 : word) = Some W_227d0.
Proof. vm_refl. Qed.
Lemma D_227d0 : decode_any W_227d0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227d4 : bv 32 := 0x01010413.
Lemma F_227d4 : fetch_word Ubsan.M.loaded_segments (0x227d4 : word) = Some W_227d4.
Proof. vm_refl. Qed.
Lemma D_227d4 : decode_any W_227d4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227d8 : bv 32 := 0x00044517.
Lemma F_227d8 : fetch_word Ubsan.M.loaded_segments (0x227d8 : word) = Some W_227d8.
Proof. vm_refl. Qed.
Lemma D_227d8 : decode_any W_227d8 = Some (Auipc 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227dc : bv 32 := 0x5f850513.
Lemma F_227dc : fetch_word Ubsan.M.loaded_segments (0x227dc : word) = Some W_227dc.
Proof. vm_refl. Qed.
Lemma D_227dc : decode_any W_227dc = Some (OpImm ALU_ADD 10 10 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227e0 : bv 32 := 0x00054503.
Lemma F_227e0 : fetch_word Ubsan.M.loaded_segments (0x227e0 : word) = Some W_227e0.
Proof. vm_refl. Qed.
Lemma D_227e0 : decode_any W_227e0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227e4 : bv 32 := 0x00157513.
Lemma F_227e4 : fetch_word Ubsan.M.loaded_segments (0x227e4 : word) = Some W_227e4.
Proof. vm_refl. Qed.
Lemma D_227e4 : decode_any W_227e4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227e8 : bv 32 := 0x00050663.
Lemma F_227e8 : fetch_word Ubsan.M.loaded_segments (0x227e8 : word) = Some W_227e8.
Proof. vm_refl. Qed.
Lemma D_227e8 : decode_any W_227e8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227ec : bv 32 := 0x0040006f.
Lemma F_227ec : fetch_word Ubsan.M.loaded_segments (0x227ec : word) = Some W_227ec.
Proof. vm_refl. Qed.
Lemma D_227ec : decode_any W_227ec = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227f0 : bv 32 := 0x03c0006f.
Lemma F_227f0 : fetch_word Ubsan.M.loaded_segments (0x227f0 : word) = Some W_227f0.
Proof. vm_refl. Qed.
Lemma D_227f0 : decode_any W_227f0 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227f4 : bv 32 := 0x00044517.
Lemma F_227f4 : fetch_word Ubsan.M.loaded_segments (0x227f4 : word) = Some W_227f4.
Proof. vm_refl. Qed.
Lemma D_227f4 : decode_any W_227f4 = Some (Auipc 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227f8 : bv 32 := 0x5dc50593.
Lemma F_227f8 : fetch_word Ubsan.M.loaded_segments (0x227f8 : word) = Some W_227f8.
Proof. vm_refl. Qed.
Lemma D_227f8 : decode_any W_227f8 = Some (OpImm ALU_ADD 11 10 1500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_227fc : bv 32 := 0x00100513.
Lemma F_227fc : fetch_word Ubsan.M.loaded_segments (0x227fc : word) = Some W_227fc.
Proof. vm_refl. Qed.
Lemma D_227fc : decode_any W_227fc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22800 : bv 32 := 0x00a58023.
Lemma F_22800 : fetch_word Ubsan.M.loaded_segments (0x22800 : word) = Some W_22800.
Proof. vm_refl. Qed.
Lemma D_22800 : decode_any W_22800 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22804 : bv 32 := 0x00043517.
Lemma F_22804 : fetch_word Ubsan.M.loaded_segments (0x22804 : word) = Some W_22804.
Proof. vm_refl. Qed.
Lemma D_22804 : decode_any W_22804 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22808 : bv 32 := 0x23c53503.
Lemma F_22808 : fetch_word Ubsan.M.loaded_segments (0x22808 : word) = Some W_22808.
Proof. vm_refl. Qed.
Lemma D_22808 : decode_any W_22808 = Some (Load SZ8 true 10 10 572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2280c : bv 32 := 0x02050063.
Lemma F_2280c : fetch_word Ubsan.M.loaded_segments (0x2280c : word) = Some W_2280c.
Proof. vm_refl. Qed.
Lemma D_2280c : decode_any W_2280c = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22810 : bv 32 := 0x0040006f.
Lemma F_22810 : fetch_word Ubsan.M.loaded_segments (0x22810 : word) = Some W_22810.
Proof. vm_refl. Qed.
Lemma D_22810 : decode_any W_22810 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22814 : bv 32 := 0xffff9517.
Lemma F_22814 : fetch_word Ubsan.M.loaded_segments (0x22814 : word) = Some W_22814.
Proof. vm_refl. Qed.
Lemma D_22814 : decode_any W_22814 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22818 : bv 32 := 0x0f450513.
Lemma F_22818 : fetch_word Ubsan.M.loaded_segments (0x22818 : word) = Some W_22818.
Proof. vm_refl. Qed.
Lemma D_22818 : decode_any W_22818 = Some (OpImm ALU_ADD 10 10 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2281c : bv 32 := 0x00044597.
Lemma F_2281c : fetch_word Ubsan.M.loaded_segments (0x2281c : word) = Some W_2281c.
Proof. vm_refl. Qed.
Lemma D_2281c : decode_any W_2281c = Some (Auipc 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22820 : bv 32 := 0x5bc58593.
Lemma F_22820 : fetch_word Ubsan.M.loaded_segments (0x22820 : word) = Some W_22820.
Proof. vm_refl. Qed.
Lemma D_22820 : decode_any W_22820 = Some (OpImm ALU_ADD 11 11 1468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22824 : bv 32 := 0x000000ef.
Lemma F_22824 : fetch_word Ubsan.M.loaded_segments (0x22824 : word) = Some W_22824.
Proof. vm_refl. Qed.
Lemma D_22824 : decode_any W_22824 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22828 : bv 32 := 0x0040006f.
Lemma F_22828 : fetch_word Ubsan.M.loaded_segments (0x22828 : word) = Some W_22828.
Proof. vm_refl. Qed.
Lemma D_22828 : decode_any W_22828 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2282c : bv 32 := 0x00813083.
Lemma F_2282c : fetch_word Ubsan.M.loaded_segments (0x2282c : word) = Some W_2282c.
Proof. vm_refl. Qed.
Lemma D_2282c : decode_any W_2282c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22830 : bv 32 := 0x00013403.
Lemma F_22830 : fetch_word Ubsan.M.loaded_segments (0x22830 : word) = Some W_22830.
Proof. vm_refl. Qed.
Lemma D_22830 : decode_any W_22830 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22834 : bv 32 := 0x01010113.
Lemma F_22834 : fetch_word Ubsan.M.loaded_segments (0x22834 : word) = Some W_22834.
Proof. vm_refl. Qed.
Lemma D_22834 : decode_any W_22834 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22838 : bv 32 := 0x00008067.
Lemma F_22838 : fetch_word Ubsan.M.loaded_segments (0x22838 : word) = Some W_22838.
Proof. vm_refl. Qed.
Lemma D_22838 : decode_any W_22838 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2283c : bv 32 := 0xff010113.
Lemma F_2283c : fetch_word Ubsan.M.loaded_segments (0x2283c : word) = Some W_2283c.
Proof. vm_refl. Qed.
Lemma D_2283c : decode_any W_2283c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22840 : bv 32 := 0x00113423.
Lemma F_22840 : fetch_word Ubsan.M.loaded_segments (0x22840 : word) = Some W_22840.
Proof. vm_refl. Qed.
Lemma D_22840 : decode_any W_22840 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22844 : bv 32 := 0x00813023.
Lemma F_22844 : fetch_word Ubsan.M.loaded_segments (0x22844 : word) = Some W_22844.
Proof. vm_refl. Qed.
Lemma D_22844 : decode_any W_22844 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22848 : bv 32 := 0x01010413.
Lemma F_22848 : fetch_word Ubsan.M.loaded_segments (0x22848 : word) = Some W_22848.
Proof. vm_refl. Qed.
Lemma D_22848 : decode_any W_22848 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2284c : bv 32 := 0x00044517.
Lemma F_2284c : fetch_word Ubsan.M.loaded_segments (0x2284c : word) = Some W_2284c.
Proof. vm_refl. Qed.
Lemma D_2284c : decode_any W_2284c = Some (Auipc 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22850 : bv 32 := 0x5cc50513.
Lemma F_22850 : fetch_word Ubsan.M.loaded_segments (0x22850 : word) = Some W_22850.
Proof. vm_refl. Qed.
Lemma D_22850 : decode_any W_22850 = Some (OpImm ALU_ADD 10 10 1484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22854 : bv 32 := 0x00054503.
Lemma F_22854 : fetch_word Ubsan.M.loaded_segments (0x22854 : word) = Some W_22854.
Proof. vm_refl. Qed.
Lemma D_22854 : decode_any W_22854 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22858 : bv 32 := 0x00157513.
Lemma F_22858 : fetch_word Ubsan.M.loaded_segments (0x22858 : word) = Some W_22858.
Proof. vm_refl. Qed.
Lemma D_22858 : decode_any W_22858 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2285c : bv 32 := 0x00050663.
Lemma F_2285c : fetch_word Ubsan.M.loaded_segments (0x2285c : word) = Some W_2285c.
Proof. vm_refl. Qed.
Lemma D_2285c : decode_any W_2285c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22860 : bv 32 := 0x0040006f.
Lemma F_22860 : fetch_word Ubsan.M.loaded_segments (0x22860 : word) = Some W_22860.
Proof. vm_refl. Qed.
Lemma D_22860 : decode_any W_22860 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22864 : bv 32 := 0x0580006f.
Lemma F_22864 : fetch_word Ubsan.M.loaded_segments (0x22864 : word) = Some W_22864.
Proof. vm_refl. Qed.
Lemma D_22864 : decode_any W_22864 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22868 : bv 32 := 0x00044517.
Lemma F_22868 : fetch_word Ubsan.M.loaded_segments (0x22868 : word) = Some W_22868.
Proof. vm_refl. Qed.
Lemma D_22868 : decode_any W_22868 = Some (Auipc 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2286c : bv 32 := 0x5b050593.
Lemma F_2286c : fetch_word Ubsan.M.loaded_segments (0x2286c : word) = Some W_2286c.
Proof. vm_refl. Qed.
Lemma D_2286c : decode_any W_2286c = Some (OpImm ALU_ADD 11 10 1456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22870 : bv 32 := 0x00100513.
Lemma F_22870 : fetch_word Ubsan.M.loaded_segments (0x22870 : word) = Some W_22870.
Proof. vm_refl. Qed.
Lemma D_22870 : decode_any W_22870 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22874 : bv 32 := 0x00a58023.
Lemma F_22874 : fetch_word Ubsan.M.loaded_segments (0x22874 : word) = Some W_22874.
Proof. vm_refl. Qed.
Lemma D_22874 : decode_any W_22874 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22878 : bv 32 := 0x00043517.
Lemma F_22878 : fetch_word Ubsan.M.loaded_segments (0x22878 : word) = Some W_22878.
Proof. vm_refl. Qed.
Lemma D_22878 : decode_any W_22878 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2287c : bv 32 := 0x1d053503.
Lemma F_2287c : fetch_word Ubsan.M.loaded_segments (0x2287c : word) = Some W_2287c.
Proof. vm_refl. Qed.
Lemma D_2287c : decode_any W_2287c = Some (Load SZ8 true 10 10 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22880 : bv 32 := 0x00050e63.
Lemma F_22880 : fetch_word Ubsan.M.loaded_segments (0x22880 : word) = Some W_22880.
Proof. vm_refl. Qed.
Lemma D_22880 : decode_any W_22880 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22884 : bv 32 := 0x0040006f.
Lemma F_22884 : fetch_word Ubsan.M.loaded_segments (0x22884 : word) = Some W_22884.
Proof. vm_refl. Qed.
Lemma D_22884 : decode_any W_22884 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22888 : bv 32 := 0x00044517.
Lemma F_22888 : fetch_word Ubsan.M.loaded_segments (0x22888 : word) = Some W_22888.
Proof. vm_refl. Qed.
Lemma D_22888 : decode_any W_22888 = Some (Auipc 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2288c : bv 32 := 0x2e850513.
Lemma F_2288c : fetch_word Ubsan.M.loaded_segments (0x2288c : word) = Some W_2288c.
Proof. vm_refl. Qed.
Lemma D_2288c : decode_any W_2288c = Some (OpImm ALU_ADD 10 10 744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22890 : bv 32 := 0x00053503.
Lemma F_22890 : fetch_word Ubsan.M.loaded_segments (0x22890 : word) = Some W_22890.
Proof. vm_refl. Qed.
Lemma D_22890 : decode_any W_22890 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22894 : bv 32 := 0x230300ef.
Lemma F_22894 : fetch_word Ubsan.M.loaded_segments (0x22894 : word) = Some W_22894.
Proof. vm_refl. Qed.
Lemma D_22894 : decode_any W_22894 = Some (Jal 1 197168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22898 : bv 32 := 0x0040006f.
Lemma F_22898 : fetch_word Ubsan.M.loaded_segments (0x22898 : word) = Some W_22898.
Proof. vm_refl. Qed.
Lemma D_22898 : decode_any W_22898 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2289c : bv 32 := 0x00043517.
Lemma F_2289c : fetch_word Ubsan.M.loaded_segments (0x2289c : word) = Some W_2289c.
Proof. vm_refl. Qed.
Lemma D_2289c : decode_any W_2289c = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228a0 : bv 32 := 0x1b453503.
Lemma F_228a0 : fetch_word Ubsan.M.loaded_segments (0x228a0 : word) = Some W_228a0.
Proof. vm_refl. Qed.
Lemma D_228a0 : decode_any W_228a0 = Some (Load SZ8 true 10 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228a4 : bv 32 := 0x00050c63.
Lemma F_228a4 : fetch_word Ubsan.M.loaded_segments (0x228a4 : word) = Some W_228a4.
Proof. vm_refl. Qed.
Lemma D_228a4 : decode_any W_228a4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228a8 : bv 32 := 0x0040006f.
Lemma F_228a8 : fetch_word Ubsan.M.loaded_segments (0x228a8 : word) = Some W_228a8.
Proof. vm_refl. Qed.
Lemma D_228a8 : decode_any W_228a8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228ac : bv 32 := 0xffff9517.
Lemma F_228ac : fetch_word Ubsan.M.loaded_segments (0x228ac : word) = Some W_228ac.
Proof. vm_refl. Qed.
Lemma D_228ac : decode_any W_228ac = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228b0 : bv 32 := 0x05c50513.
Lemma F_228b0 : fetch_word Ubsan.M.loaded_segments (0x228b0 : word) = Some W_228b0.
Proof. vm_refl. Qed.
Lemma D_228b0 : decode_any W_228b0 = Some (OpImm ALU_ADD 10 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228b4 : bv 32 := 0x000000ef.
Lemma F_228b4 : fetch_word Ubsan.M.loaded_segments (0x228b4 : word) = Some W_228b4.
Proof. vm_refl. Qed.
Lemma D_228b4 : decode_any W_228b4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228b8 : bv 32 := 0x0040006f.
Lemma F_228b8 : fetch_word Ubsan.M.loaded_segments (0x228b8 : word) = Some W_228b8.
Proof. vm_refl. Qed.
Lemma D_228b8 : decode_any W_228b8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228bc : bv 32 := 0x00813083.
Lemma F_228bc : fetch_word Ubsan.M.loaded_segments (0x228bc : word) = Some W_228bc.
Proof. vm_refl. Qed.
Lemma D_228bc : decode_any W_228bc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228c0 : bv 32 := 0x00013403.
Lemma F_228c0 : fetch_word Ubsan.M.loaded_segments (0x228c0 : word) = Some W_228c0.
Proof. vm_refl. Qed.
Lemma D_228c0 : decode_any W_228c0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228c4 : bv 32 := 0x01010113.
Lemma F_228c4 : fetch_word Ubsan.M.loaded_segments (0x228c4 : word) = Some W_228c4.
Proof. vm_refl. Qed.
Lemma D_228c4 : decode_any W_228c4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_228c8 : bv 32 := 0x00008067.
Lemma F_228c8 : fetch_word Ubsan.M.loaded_segments (0x228c8 : word) = Some W_228c8.
Proof. vm_refl. Qed.
Lemma D_228c8 : decode_any W_228c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
